# Resource Types

Status: **draft** (2026-11-20). Module `kategoria::resources` ([decision 0004](../development/decisions/0004-resource-types.md)).

## 1. Concepts

A resource theory is a symmetric monoidal category: resources are objects, the conversions allowed for free are arrows, and nothing at all is the unit. Its shadow is an ordered commutative monoid, a symmetric monoidal preorder, in which a ≽ b when a converts into b (Coecke, Fritz and Spekkens 2016; Fritz 2017; Fong and Spivak 2019, ch. 2). A resource type declares that shadow by its parts:

- components, combined componentwise, each with its kinds and a quantity semiring that fixes divisibility: natural numbers (identical units), multiples of a grain, nonnegative rationals (divisible), integers and rationals (signed balances and debts), and two qualities, 0 or 1 under ∨ and nonnegative rationals under max;
- conversions, the generating free processes (a Petri net's transitions), and free disposal declared kind by kind, refused for chores and waste;
- validity: capacities and distinct items, which make combination partial;
- laws: conservation laws and monotones, weights on the kinds.

Every law is answered by a method whose verdict says what it establishes:

- **By construction:** for every type built from the primitive semirings by products, naming the closure theorem.
- **On the generating processes:** for homomorphisms such as conservation laws, monotones and prices. The verdict is a proof for every bundle, from finitely many checks.
- **Exhaustively on a finite model:** a truncation with partial addition, or an algebra declared whole on a finite carrier. The verdict is a proof for that model only, and a counterexample refutes for the type.
- **By bounded search:** convertibility, with a witness that separate code replays, or a monotone that refutes, or undecided.

The monoid laws of a finite model are decided by kategoria's validation of its totalisation, an absorbing ⊤ standing for every undefined combination, as a one-object category. Its order is a preorder category, and compatibility with combination is the functoriality of combination P × P → P. An allocation of a pool to recipients is a morphism pool → r₁ ⊗ … ⊗ rₙ, checked: every part and the whole valid, and the pool converting into the whole.

Order of allocation is decided on finite systems. Grants act partially on states. The order does not matter from a state exactly when every two grants commute on every reachable state, undefinedness included; then the action factors through the free commutative monoid. The pairs that commute are a trace monoid's independence relation. The maps words induce form the transition monoid, built by closure and validated by kategoria.

An operator of a search, as a kernel on finite genotypes, treats renamed items or recipients alike exactly when it is equivariant, which is naturality in the Kleisli category of distributions.

Theory: the infrastructure's survey [Evolutionary heterogeneous resource allocation](https://github.com/huangwanhong-maker/Noetarium-The-Science-and-Humanity-Infrastructure/blob/main/research/literature/reports/Evolutionary%20heterogeneous%20resource%20allocation.md), Part IV and §1.9.

## 2. Content

- `algebra.hpp`: `Quantity`, `Kind`, `Component`, `Bundle`, `Conversion`, `Law`, `Type`; `words`, `well_formed`, `member`, `combine`, `combine_all`, `invalid`, `valid`, `scale`; `value`, `verify_law`; `Step`, `check_witness`, `Conversion_search`, `convertible`.
- `finite.hpp`: `FiniteAlgebra`; `monoid_laws`, `commutative`, `order`, `monotone`, `quality_like`, `quantity_like`, `cancellative`, `catalysis_free`, `splittable`; `Grid`, `truncation`.
- `verify.hpp`: `Method`, `Entry`, `Report`, `Options`, `verify`; `Allocation_check`, `allocation`.
- `systems.hpp`: `System`, `TransitionMonoid`, `Independence`, `reachable`, `transition_monoid`, `independence`; `Kernel`, `Kernel2`, `is_kernel`, `equivariant`.

*Caveat.*
- **Exact amounts.** Amounts are exact rationals whose parts fit in 64 bits. A larger amount is refused, never carried.
- **Whole multiples.** Conversions are searched in whole multiples. An answer that would need a fractional application on divisible components is undecided, and says so.
- **No sampling.** Laws over the reals are proved by construction, or decided on a finite model.

## 3. Checks

39 (`tests/check_resources.cpp`):
- **A mixed type** (money, nurses, two distinct clinics, a permit): its carrier and combination by hand; a distinct item held twice invalid; a nurse refused halving. Its report is lawful on its model of 32 bundles, the monoid laws decided by the validation of the totalisation.
- **A capacity on a signed balance:** validity is not closed under parts, refuted with the pair.
- **Algebras declared whole:**
  - ℤ/3 with its natural order: a monoid whose order is incompatible with combination;
  - saturating addition: lawful, not cancellative;
  - |a − b|: not associative;
  - ℕ truncated with partial addition: lawful;
  - a partial addition broken by its undefinedness: refuted;
  - max on {0, 1}: quality-like.
- **Laws on the generators:** a law conserved, then no longer once disposal is free, though still a monotone; a doubling conversion refuted at its name.
- **2 H₂ + O₂ → 2 H₂O:** reached with a replayed witness; refuted by hydrogen; refuted exhaustively without laws; undecided when reachability never ends; a forged witness rejected.
- **Splittability:** a cow cannot be split between beef and leather; ℕ² with disposal is splittable, cancellative and catalysis-free.
- **Allocations:** a lawful one; one exceeding the pool; a distinct clinic given twice; a nurse left over where none may be disposed of.
- **Grant systems:**
  - a shared stock commutes, its transition monoid of the size brute force gives;
  - a rising price makes order matter, both outcomes named;
  - on two pools, only the competing pair fails to commute.
- **Operators:** swap mutation equivariant under renaming items and positions; moving one item to the front not; uniform crossover natural for a bit flip, a biased one not.

## 4. Dependencies

`kategoria::finite`, `kategoria::functors`; morphe's `arithmetic` (exact rationals).

## 5. References

- **Resource theories:** Coecke, Fritz and Spekkens (2016); Fritz (2017); Fong and Spivak (2019).
- **Petri nets as monoidal categories:** Meseguer and Montanari (1990).
- **Resource algebras:** Jung et al. (2018, Iris).
- **Varieties and orders:** Birkhoff (1935); Bloom (1976).
- **Complexity of reachability:** Mayr and Meyer (1982); Czerwiński and Orlikowski (2021); Leroux (2021).
- **Traces:** Mazurkiewicz (1977); Diekert and Rozenberg (1995).
- **Finite semigroups:** Rhodes and Steinberg (2009).
