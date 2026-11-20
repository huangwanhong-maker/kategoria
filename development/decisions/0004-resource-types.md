# 0004. Resource Types, Their Laws, and the Order of Grants

- **Status:** Accepted, provisionally
- **Date:** 2026-11-20
- **Decided by:** Claude, for Stage 3 of the infrastructure's design of an evolutionary framework for allocating heterogeneous resources (its idea of 2026-11-20). The user asked that resource categories be "definable, formal verificable (by category theory foundation)".

## 1. Context

The infrastructure's survey *Evolutionary heterogeneous resource allocation* (nine Parts) found the following:
- **What a resource type is.** It is a symmetric monoidal preorder: the shadow of a resource theory (Coecke, Fritz and Spekkens 2016; Fritz 2017). Divisibility, distinctness and copyability are extra structure: a quantity semiring, a validity predicate, an idempotent combination.
- **What can be verified.** Laws are verified with scoped verdicts:
  - by construction from verified primitives;
  - on generators for homomorphisms;
  - exhaustively on finite models;
  - by bounded search for convertibility, which is Ackermann-complete in general.
- **Order of allocation.** It is the non-commutativity of grants acting on states (Part II and Part IV, independently).
- **Operators.** No categorical treatment of evolutionary operators was found.

kategoria already held what this needs: preorders as categories, products, full subcategories, the verification of functors, and finite monoids validated as categories.

## 2. Decision

- **A module `resources`.** It holds resource types declared by their components, semirings, conversions, disposal, validity and laws. It answers each law by its method, with its scope stated:
  - a proof by construction, naming the closure theorem;
  - a proof for every bundle from the generators;
  - a proof for a finite model, where a counterexample refutes for the type;
  - a witness, a monotone or undecided.
- **Finite models' laws, decided by kategoria's own constructions:**
  - the totalisation, with an absorbing ⊤ for undefined combinations, validated as a monoid;
  - the order as a preorder category;
  - compatibility as the functoriality of combination, verified as a functor for small carriers.
- **Allocations** are checked as morphisms.
- **The order of grants on finite systems** is decided through the transition monoid, which kategoria validates, and the independence relation is derived.
- **The equivariance of kernels** is decided as naturality.
- **Exact arithmetic.** Amounts are morphe's exact rationals whose parts fit in 64 bits; beyond that they are refused, as invariant 7 requires. A search's witness is replayed by separate code, as invariant 5 requires.

## 3. Alternatives Considered

- **Floating-point amounts.** Rejected: no law is checked in floating point.
- **Sampled checks of laws over the reals.** Rejected here: kategoria does not draw at random, and a sample is evidence, not proof. A library that draws at random may sample and must say so.
- **Fractional application of conversions on divisible components** (continuous Petri nets). Deferred; such answers are undecided and say so.
- **The resource theory as a full symmetric monoidal category** with string diagrams, using `monoidal`. Deferred: the shadow decides feasibility, which allocation needs; the processes themselves can be added on `monoidal` later.

## 4. Consequences

- A person can declare a resource type, with its own space of amounts elsewhere, and learn which of its laws hold, how each is known, and how far the knowledge reaches.
- A search for allocations can ask whether its grants commute, and use the derived independence relation to evaluate each trace once.
- **Checks:** 39, held to answers by hand, closed forms and brute force.
- **Provisional:** the module's name; the default grid of a finite model; the search's budget.
