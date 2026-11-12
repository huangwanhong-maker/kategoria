# Presented Categories

Status: **draft** (2026-11-12). Module `kategoria::presentations`.

## 1. Concepts

A presentation is a quiver with equations between parallel paths. Whether two paths are equal in the category it presents is undecidable in general; Knuth–Bendix completion on paths decides it whenever it ends, and when the normal forms are finitely many the category is built whole. Equality comes with a derivation by the presentation's own equations, which a checker of thirty lines verifies; inequality rests on confluence, which is verified on the rules as they stand. Where completion does not end, that is said. Theory: [docs/theory.md](../docs/theory.md), §5.

## 2. Content

- `presentation.hpp`: `Quiver`, `Path{source, edges}` (edges in the order travelled), `Equation`, `Presentation`; `target`, `composable`, `words`, `well_formed`; `Step{at, equation, forward}`, `Derivation`, `apply`, `check(P, from, to, derivation)`, `trace`, `shortened`, `reversed`; `Rule{left, right, why}`, `Completion{rules, complete, reason, pairs}`, `Bounds`, `complete(P, bounds)`, `normal_form`, `certify(P, K)`; `prove(P, K, u, v)` → `Proof{verdict, derivation}`; `category(P, K, most)` → `Presented{category, paths, generator, at}`.

## 3. Checks

23: nine presentations, each building a category isomorphic to what it presents (a path, the commutative square, ℤ/5, S₃, D₄ and Q₈ against morphe's tables, the walking isomorphism, and Δ up to [2] from its faces, degeneracies and the cosimplicial identities); (st)³ = 1 in S₃ with a derivation that checks, and derivations with a step removed or misplaced refused; s ≠ t by two normal forms, with the rules certified; a free monoid that is not finite; the braid monoid, whose completion does not end, with equal words still proved and unequal ones undecided.

## 4. Dependencies

`kategoria::finite`. The checks use `kategoria::functors` and morphe's `algebra`.

## 5. References

Knuth and Bendix (1970); Book and Otto (1993), ch. 2; Newman (1942); Mac Lane (1998), II.7–II.8.
