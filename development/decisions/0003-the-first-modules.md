# 0003. The First Modules

- **Status:** Accepted, provisionally
- **Date:** 2026-11-12
- **Decided by:** Claude, for the infrastructure's ADR 0100

## 1. Context

The first use is the Category Studio: a script of declarations and claims, each answered with a verdict and a drawing. That fixes what the first slice must hold.

## 2. Decision

Eight modules, each a header-only target `kategoria::<module>`, in this order:

| Module | Depends on | Holds |
|---|---|---|
| `kernel` | — | `Verdict`: status, claim, reason, evidence, the number of instances examined |
| `finite` | kernel | `Category` as a table; `validate`; families; opposites, products, sums, slices; properties; generators |
| `functors` | finite | `Functor`, `Transformation`; verification and search; categories of functors; equivalences; comma categories; adjunctions; monads |
| `limits` | functors | cones; `is_limit` and `limit`; the usual shapes; completeness; preservation; exponentials |
| `sets` | functors | `Copresheaf`; Yoneda; elements; sections and classes; Kan extensions; the classifier of subobjects |
| `presentations` | finite | quivers with equations; completion; derivations and `check`; `certify`; the finite category |
| `monoidal` | finite, morphe's `combinatorics` | signatures, terms, diagrams; `same`; models; laws in a model |
| `script` | all of the above, morphe's `formal` and `algebra` | the grammar; `Session`; the document of answers |

Conventions fixed with them:

- composition is `compose(g, f)` = g ∘ f; a path lists its edges in the order travelled;
- a colimit is a limit in the opposite category, its cocone held as a cone;
- set-valued functors are covariant;
- a category built by a construction carries a `basis` of arrows that generate it where the construction knows a natural one;
- the language's grammar is BNF read by morphe; its statements are separated by lines, and items in a block by lines or `;`.

## 3. Alternatives Considered

- **Categories as abstract interfaces** (objects and arrows of any type, composition a callable). It serves infinite categories, and cannot decide a universal claim. The table can. An interface can be added beside it when a use asks.
- **A parser written by hand.** morphe's BNF reader exists, diagnoses exactly, and makes the grammar a text one can read; genomics' notations set the precedent.
- **Canonical forms for the isomorphism of categories.** Encoding the table as a labelled graph has a vertex for every composable pair, too many for morphe's dense search. The search for a functor injective on arrows is direct and fast on what a studio holds.
- **Rewriting of diagrams in the first slice.** It needs matching up to convexity and a search with its own bounds. Equality in the free symmetric monoidal category and laws in models are exact and are enough to begin; rewriting is planned.

## 4. Consequences

- 190 checks at founding (finite 36, functors 38, limits 23, sets 20, presentations 23, monoidal 30, script 20).
- Sizes are those a table allows: some thousands of arrows. A statement of the language refuses to build more than a bound.
- Found while checking, and now part of the design: arrows with retractions make every arrow a composite, so generators are given by constructions and not derived (theory §1). Confirmed while checking: the faces and degeneracies of Δ up to [2] with the cosimplicial identities among them do present it (theory §5).
