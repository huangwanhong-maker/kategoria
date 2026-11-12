# Symmetric Monoidal Theories

Status: **draft** (2026-11-12). Module `kategoria::monoidal`.

## 1. Concepts

A signature gives types and generators with wires in and out. A term is built from generators, identities and the symmetry by sequence and tensor; its string diagram is its wires and boxes. Two terms are equal by the axioms of symmetric monoidal categories alone exactly when their diagrams are isomorphic, which morphe's canonical forms decide. A model sends types to dimensions and generators to matrices over a semiring, with the Kronecker product or the direct sum as tensor; a law holds in a model when both sides are one matrix. Theory: [docs/theory.md](../docs/theory.md), §7.

## 2. Content

- `monoidal.hpp`: `Signature`, `Generator`, `Term` with `id`, `gen`, `swap`, `seq`, `par`; `words`; `type(S, term)` → `Typed{verdict, in, out}`; `Diagram{wires, boxes, inputs, outputs}`, `diagram(S, term)`, `depths`, `canonical`, `same(S, a, b)`; `Semiring` (integer, boolean, modular), `Matrix`, `Model`, `function(f, onto)`, `well_formed`, `evaluate`; `Law`, `Theory`, `well_formed(theory)`, `holds_in`, `laws_in`, `satisfies`.

## 3. Checks

30: typing and its refusals; the interchange law, the naturality and involution of the symmetry and the Yang–Baxter equation as equalities of diagrams; associativity and commutativity not axioms; (2, ∧, ⊤) with copying a bialgebra among finite sets and no Frobenius algebra, with the entry named; copying and its converse a special commutative Frobenius algebra among relations; addition and copying on a line a bialgebra over ℕ, a Hopf algebra over ℤ, and the Hopf law failing over the Booleans and holding modulo 2.

## 4. Dependencies

`kategoria::finite`; morphe's `combinatorics` (canonical forms of labelled graphs).

## 5. References

Joyal and Street (1991); Bonchi, Gadducci, Kissinger, Sobociński and Zanasi (2022); Carboni and Walters (1987); Lack (2004).
