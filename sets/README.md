# Set-Valued Functors

Status: **draft** (2026-11-12). Module `kategoria::sets`.

## 1. Concepts

A functor from a finite category to finite sets is a set for each object and a function for each arrow: an action, a diagram of sets, or data on a schema. Natural transformations between two are found by fixing the image of one element at a time and carrying it along every arrow. On them stand the Yoneda lemma, the category of elements, limits and colimits, the three functors along a functor (pullback and the two Kan extensions, computed pointwise), and the classifier of subobjects, whose value at an object is the set of cosieves on it. Theory: [docs/theory.md](../docs/theory.md), §6.

## 2. Content

- `copresheaf.hpp`: `Copresheaf{name, elements, action}`, `verify`; `representable(C, a)`, `constant(C, n)`; `natural`, `for_each_transformation`, `count_transformations`, `all_transformations`, `isomorphism`; `yoneda(C, X, a)`; `elements(C, X)` with its projection; `sections` (the limit), `classes` (the colimit); `pullback(K, Y)`, `left_kan`, `right_kan` (each with its unit or counit), `left_kan_universal`, `right_kan_universal`; `classifier(C)`, `subfunctors`, `characteristic`, `classifies`, `subobjects(C, X)` (a Heyting algebra, as a category).

## 3. Checks

20: Yoneda at every object of four categories; actions of a cyclic group (fixed points as sections, orbits as classes, equivariant maps counted); the elements of a representable as a coslice; Kan extensions along the functor to a point, of a representable, along a subgroup (induction and coinduction) and along an inclusion of ordinals, each universal against every functor tried; the truth values over a point, a group, the ordinals and a monoid with an idempotent; the classifier classifying the subfunctors of every representable; the subfunctors as a cartesian closed order.

## 4. Dependencies

`kategoria::functors`. The checks use `kategoria::limits` and morphe's `algebra`.

## 5. References

Mac Lane (1998), III.2, X.3; Mac Lane and Moerdijk (1992), ch. I; Spivak (2012).
