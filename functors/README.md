# Functors, Transformations, Adjunctions

Status: **draft** (2026-11-12). Module `kategoria::functors`.

## 1. Concepts

A functor is its values on every object and arrow; a natural transformation its components. Whether such data are a functor, or natural, is a claim answered with the place where it fails. Functors are *found* by a search that branches only on arrows nothing forces, and that visits exactly the functors there are. A left adjoint is built from universal arrows, or the object with none is named; what is built is then verified by the triangle identities. Theory: [docs/theory.md](../docs/theory.md), §3.

## 2. Content

- `functor.hpp`: `Functor`, `Transformation`; `verify`, `identity`, `compose`, `constant`; `for_each_functor(C, D, visit, options)` (options: injective, a limit, a part already fixed), `count_functors`, `all_functors`, `isomorphism(C, D)`; `natural`, `for_each_transformation`, `all_transformations`, `natural_isomorphism`, `vertical`, `whisker_left`, `whisker_right`, `horizontal`; `functor_category(C, D)`; `faithful`, `full`, `essentially_surjective`, `equivalence` (with the functor back, the unit and the counit built), `equivalent(C, D)` by skeletons; `comma(A, B, C, F, G)` with its two projections.
- `adjunction.hpp`: `Adjunction{left, right, unit, counit}`, `verify_adjunction`, `left_adjoint`, `right_adjoint`; `Monad{T, unit, mult}`, `verify_monad`, `monad_of(adjunction)`, `identity_monad`, `eilenberg_moore` (with the forgetful functor), `kleisli` (with the free functor).

## 3. Checks

38: the search against the naive enumeration of every map of arrows, and against closed forms (monotone maps between ordinals, homomorphisms between groups); isomorphisms found and refused; the centre of a group as the natural transformations of its identity; [2, C] against the comma category (1 ↓ 1); the interchange law at 17,280 instances; an equivalence with its functor back; Galois connections; the diagonal's adjoints as meet and join, and none for a group; a closure operator as a monad, its algebras the closed sets.

## 4. Dependencies

`kategoria::finite`. The checks use morphe's `algebra`.

## 5. References

Mac Lane (1998), I.3–I.4, II.4–II.6, IV.1, IV.4, VI.1–VI.5.
