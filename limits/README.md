# Limits and Colimits

Status: **draft** (2026-11-12). Module `kategoria::limits`.

## 1. Concepts

A cone on a diagram is a limit when every cone factors through it by exactly one arrow. In a finite category that is decided by listing the cones; a failure names the cone that does not factor, or factors twice. A limit is found by trying the cones. Colimits are limits in the opposite category. Theory: [docs/theory.md](../docs/theory.md), §4.

## 2. Content

- `limits.hpp`: `Cone{apex, legs}`, `verify_cone`, `for_each_cone`, `factorisations`, `is_limit`, `limit`, `is_colimit`, `colimit`; diagrams of the usual shapes (`empty_diagram`, `discrete_diagram`, `parallel_diagram`, `cospan_diagram`, `span_diagram`) and `terminal`, `initial`, `product`, `coproduct`, `equalizer`, `coequalizer`, `pullback`, `pushout`; `finitely_complete`, `finitely_cocomplete` (naming the first diagram without a limit); `preserves(J, D, cone, E, F)`; `exponential(C, a, b)`, `cartesian_closed(C)`.

## 3. Checks

23: meets and joins as products and coproducts in ordinals, divisors and subsets; what FinSet up to 2 has and lacks (2 × 2 does not exist); a cone that is not universal refused with the cone that does not factor; completeness of lattices and its failure in a group and in FinSet truncated, with the diagram named; a right adjoint keeping every product; exponentials in a Boolean algebra; cartesian closure of distributive lattices and its failure in the diamond and the pentagon.

## 4. Dependencies

`kategoria::functors`.

## 5. References

Mac Lane (1998), III.3–III.4, IV.6, V.2, V.5.
