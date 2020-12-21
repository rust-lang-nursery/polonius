// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A version of the Naive datalog analysis using Datafrog.

use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use crate::facts::FactTypes;
use crate::output::{Context, Output};

pub(super) fn compute<T: FactTypes>(
    ctx: &Context<'_, T>,
    result: &mut Output<T>,
) -> (
    Relation<(T::Loan, T::Point)>,
    Relation<(T::Origin, T::Origin, T::Point)>,
) {
    let timer = Instant::now();

    let (errors, subset_errors) = {
        // Static inputs
        let origin_live_on_entry_rel = &ctx.origin_live_on_entry;
        let cfg_edge = &ctx.cfg_edge;
        let loan_killed_at = &ctx.loan_killed_at;
        let known_subset = &ctx.known_subset;
        let placeholder_origin = &ctx.placeholder_origin;

        // Create a new iteration context, ...
        let mut iteration = Iteration::new();

        // .. some variables, ..
        let subset = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset");
        let origin_contains_loan_on_entry =
            iteration.variable::<(T::Origin, T::Loan, T::Point)>("origin_contains_loan_on_entry");
        let loan_live_at = iteration.variable::<((T::Loan, T::Point), ())>("loan_live_at");

        // `loan_invalidated_at` facts, stored ready for joins
        let loan_invalidated_at =
            iteration.variable::<((T::Loan, T::Point), ())>("loan_invalidated_at");

        // different indices for `subset`.
        let subset_o1p = iteration.variable_indistinct("subset_o1p");
        let subset_o2p = iteration.variable_indistinct("subset_o2p");

        // different index for `origin_contains_loan_on_entry`.
        let origin_contains_loan_on_entry_op =
            iteration.variable_indistinct("origin_contains_loan_on_entry_op");

        // we need `origin_live_on_entry` in both variable and relation forms.
        // (respectively, for the regular join and the leapjoin).
        let origin_live_on_entry_var =
            iteration.variable::<((T::Origin, T::Point), ())>("origin_live_on_entry");

        // variable and index to compute the subsets of placeholders
        let subset_placeholder =
            iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_placeholder");
        let subset_placeholder_o2p = iteration.variable_indistinct("subset_placeholder_o2p");

        // output relations: illegal accesses errors, and illegal subset relations errors
        let errors = iteration.variable("errors");
        let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");

        // load initial facts.
        subset.extend(ctx.subset_base.iter());
        origin_contains_loan_on_entry.extend(ctx.loan_issued_at.iter());
        loan_invalidated_at.extend(
            ctx.loan_invalidated_at
                .iter()
                .map(|&(loan, point)| ((loan, point), ())),
        );
        origin_live_on_entry_var.extend(
            origin_live_on_entry_rel
                .iter()
                .map(|&(origin, point)| ((origin, point), ())),
        );

        // .. and then start iterating rules!
        while iteration.changed() {
            // Cleanup step: remove symmetries
            // - remove regions which are `subset`s of themselves
            //
            // FIXME: investigate whether is there a better way to do that without complicating
            // the rules too much, because it would also require temporary variables and
            // impact performance. Until then, the big reduction in tuples improves performance
            // a lot, even if we're potentially adding a small number of tuples
            // per round just to remove them in the next round.
            subset
                .recent
                .borrow_mut()
                .elements
                .retain(|&(origin1, origin2, _)| origin1 != origin2);

            subset_placeholder
                .recent
                .borrow_mut()
                .elements
                .retain(|&(origin1, origin2, _)| origin1 != origin2);

            // remap fields to re-index by keys.
            subset_o1p.from_map(&subset, |&(origin1, origin2, point)| {
                ((origin1, point), origin2)
            });
            subset_o2p.from_map(&subset, |&(origin1, origin2, point)| {
                ((origin2, point), origin1)
            });

            subset_placeholder_o2p.from_map(&subset_placeholder, |&(origin1, origin2, point)| {
                ((origin2, point), origin1)
            });

            origin_contains_loan_on_entry_op
                .from_map(&origin_contains_loan_on_entry, |&(origin, loan, point)| {
                    ((origin, point), loan)
                });

            // subset(origin1, origin2, point) :-
            //   subset_base(origin1, origin2, point).
            // Already loaded; `subset_base` is static.

            // subset(origin1, origin3, point) :-
            //   subset(origin1, origin2, point),
            //   subset(origin2, origin3, point).
            subset.from_join(
                &subset_o2p,
                &subset_o1p,
                |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point),
            );

            // subset(origin1, origin2, point2) :-
            //   subset(origin1, origin2, point1),
            //   cfg_edge(point1, point2),
            //   origin_live_on_entry(origin1, point2),
            //   origin_live_on_entry(origin2, point2).
            subset.from_leapjoin(
                &subset,
                (
                    cfg_edge.extend_with(|&(_origin1, _origin2, point1)| point1),
                    origin_live_on_entry_rel.extend_with(|&(origin1, _origin2, _point1)| origin1),
                    origin_live_on_entry_rel.extend_with(|&(_origin1, origin2, _point1)| origin2),
                ),
                |&(origin1, origin2, _point1), &point2| (origin1, origin2, point2),
            );

            // origin_contains_loan_on_entry(origin, loan, point) :-
            //   loan_issued_at(origin, loan, point).
            // Already loaded; `loan_issued_at` is static.

            // origin_contains_loan_on_entry(origin2, loan, point) :-
            //   origin_contains_loan_on_entry(origin1, loan, point),
            //   subset(origin1, origin2, point).
            origin_contains_loan_on_entry.from_join(
                &origin_contains_loan_on_entry_op,
                &subset_o1p,
                |&(_origin1, point), &loan, &origin2| (origin2, loan, point),
            );

            // origin_contains_loan_on_entry(origin, loan, point2) :-
            //   origin_contains_loan_on_entry(origin, loan, point1),
            //   !loan_killed_at(loan, point1),
            //   cfg_edge(point1, point2),
            //   origin_live_on_entry(origin, point2).
            origin_contains_loan_on_entry.from_leapjoin(
                &origin_contains_loan_on_entry,
                (
                    loan_killed_at.filter_anti(|&(_origin, loan, point1)| (loan, point1)),
                    cfg_edge.extend_with(|&(_origin, _loan, point1)| point1),
                    origin_live_on_entry_rel.extend_with(|&(origin, _loan, _point1)| origin),
                ),
                |&(origin, loan, _point1), &point2| (origin, loan, point2),
            );

            // loan_live_at(loan, point) :-
            //   origin_contains_loan_on_entry(origin, loan, point),
            //   origin_live_on_entry(origin, point).
            loan_live_at.from_join(
                &origin_contains_loan_on_entry_op,
                &origin_live_on_entry_var,
                |&(_origin, point), &loan, _| ((loan, point), ()),
            );

            // errors(loan, point) :-
            //   loan_invalidated_at(loan, point),
            //   loan_live_at(loan, point).
            errors.from_join(
                &loan_invalidated_at,
                &loan_live_at,
                |&(loan, point), _, _| (loan, point),
            );

            // subset_placeholder(Origin1, Origin2, Point) :-
            //   subset(Origin1, Origin2, Point),
            //   placeholder_origin(Origin1).
            subset_placeholder.from_leapjoin(
                &subset_o1p,
                (
                    placeholder_origin.extend_with(|&((origin1, _point), _origin2)| origin1),
                    // remove symmetries:
                    datafrog::ValueFilter::from(|&((origin1, _point), origin2), _| {
                        origin1 != origin2
                    }),
                ),
                |&((origin1, point), origin2), _| (origin1, origin2, point),
            );

            // subset_placeholder(Origin1, Origin3, Point) :-
            //   subset_placeholder(Origin1, Origin2, Point),
            //   subset(Origin2, Origin3, Point).
            subset_placeholder.from_join(
                &subset_placeholder_o2p,
                &subset_o1p,
                |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point),
            );

            // subset_errors(Origin1, Origin2, Point) :-
            //   subset_placeholder(Origin1, Origin2, Point),
            //   placeholder_origin(Origin2),
            //   !known_subset(Origin1, Origin2).
            subset_errors.from_leapjoin(
                &subset_placeholder,
                (
                    placeholder_origin.extend_with(|&(_origin1, origin2, _point)| origin2),
                    known_subset.filter_anti(|&(origin1, origin2, _point)| (origin1, origin2)),
                    // remove symmetries:
                    datafrog::ValueFilter::from(|&(origin1, origin2, _point), _| {
                        origin1 != origin2
                    }),
                ),
                |&(origin1, origin2, point), _| (origin1, origin2, point),
            );
        }

        // Handle verbose output data
        if result.dump_enabled {
            let subset = subset.complete();
            assert!(
                subset
                    .iter()
                    .filter(|&(origin1, origin2, _)| origin1 == origin2)
                    .count()
                    == 0,
                "unwanted subset symmetries"
            );
            for &(origin1, origin2, location) in subset.iter() {
                result
                    .subset
                    .entry(location)
                    .or_default()
                    .entry(origin1)
                    .or_default()
                    .insert(origin2);
            }

            let origin_contains_loan_on_entry = origin_contains_loan_on_entry.complete();
            for &(origin, loan, location) in origin_contains_loan_on_entry.iter() {
                result
                    .origin_contains_loan_at
                    .entry(location)
                    .or_default()
                    .entry(origin)
                    .or_default()
                    .insert(loan);
            }

            let loan_live_at = loan_live_at.complete();
            for &((loan, location), _) in loan_live_at.iter() {
                result.loan_live_at.entry(location).or_default().push(loan);
            }
        }

        (errors.complete(), subset_errors.complete())
    };

    info!(
        "analysis done: {} `errors` tuples, {} `subset_errors` tuples, {:?}",
        errors.len(),
        subset_errors.len(),
        timer.elapsed()
    );

    (errors, subset_errors)
}
