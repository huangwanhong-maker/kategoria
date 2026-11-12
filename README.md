# kategoria

*κατηγορία, what is said of a thing; the word Eilenberg and Mac Lane took from Aristotle for "category".* kategoria computes with categories: finite ones given whole, and those presented by generators and equations; functors, natural transformations and adjunctions between them; limits and colimits; set-valued functors; and symmetric monoidal theories with their string diagrams. Every claim made of them is answered with its evidence, and a small language states such claims in a script. It is one of the foundation libraries of [Noetarium, the Science and Humanity Infrastructure](https://github.com/huangwanhong-maker/Noetarium-The-Science-and-Humanity-Infrastructure), but it stands on its own (with calx and morphe beside it).

The name is provisional.

## 1. Concepts

The theory, with what each algorithm rests on, is in [docs/theory.md](docs/theory.md).

- **Claims answered with evidence.** A claim about categories is answered in one of three ways and never with a bare yes or no: it *holds*, with what makes it so; it *fails*, with the place where it fails; or it is *undecided*, with the reason. A claim about every instance of a finite structure is decided by examining every instance. A claim that something exists is decided by a search, and what the search finds is then checked by a function that does not share its code (theory §2).
- **Two ways to give a category.** A finite category is its table of composition, as a finite group is its table. A presented category is a quiver with equations between parallel paths; its word problem is attacked by Knuth–Bendix completion on paths, and when completion ends and the normal forms are finitely many, the category is built whole from them (theory §5).
- **Equality with its derivation.** Two paths found equal come with a derivation: a chain of steps, each replacing one side of one of the presentation's own equations by the other. The checker of derivations knows only the equations. Inequality rests on confluence, which is verified on the rules as they stand.
- **Universal properties decided.** A cone is a limit when every cone factors through it exactly once: that is decided by listing the cones, and a failure names the cone that does not factor. Adjoints are built from universal arrows, or the object that has none is named. Kan extensions of set-valued functors are computed pointwise and their universal property is decided against any functor given.
- **Diagrams as the free symmetric monoidal category.** Two terms of a monoidal signature are equal by the axioms of symmetric monoidal categories alone exactly when their string diagrams are isomorphic, which morphe's canonical forms of labelled graphs decide. A law of a theory holding in a model is another matter, decided entry by entry on matrices.

A method belongs here when it computes with categories as objects of study, or decides a claim about them. Structures that happen to form a category (groups, graphs, complexes, grammars) stay where they are; kategoria reads them as categories ([decision 0002](development/decisions/0002-scope-boundaries-and-dependencies.md)).

## 2. Modules

| Module | Holds | Status |
|---|---|---|
| [kernel](kernel/README.md) | Verdicts: holds, fails or undecided, with the claim, the reason and the evidence piece by piece | draft |
| [finite](finite/README.md) | Finite categories as tables, validated; families (ordinals, lattices of subsets and divisors, monoids and groups, FinSet and Δ truncated); opposites, products, sums, slices; monos, epis, isomorphisms, skeletons, generators | draft |
| [functors](functors/README.md) | Functors and natural transformations, verified and found by search; categories of functors; faithful, full, equivalences with the functor back built; comma categories; adjunctions from universal arrows; monads, their algebras and Kleisli categories | draft |
| [limits](limits/README.md) | Cones; limits and colimits decided and found; products, equalizers, pullbacks and their duals; finite completeness; preservation; exponentials and cartesian closure | draft |
| [sets](sets/README.md) | Set-valued functors: representables and the Yoneda lemma, the category of elements, sections and classes, the pullback and both Kan extensions along a functor with their universal properties, the classifier of subobjects, subfunctors as a Heyting algebra | draft |
| [presentations](presentations/README.md) | Quivers with equations; Knuth–Bendix completion on paths; derivations and their checker; the rules certified; the finite category built from normal forms | draft |
| [monoidal](monoidal/README.md) | Symmetric monoidal signatures, terms and their typing; string diagrams; equality in the free symmetric monoidal category; models in matrices over a semiring with the Kronecker product or the direct sum; laws decided in a model | draft |
| [script](script/README.md) | A language of declarations and claims, its grammar read by morphe's BNF reader; a session that carries a script out and answers each statement with a verdict and a view of what there is to draw | draft |
| rewriting | Equality of string diagrams modulo a theory's laws, by double-pushout rewriting with convex matches | planned |
| enriched | Categories enriched in a semiring or a quantale: weighted limits, the magnitude of a category | planned |
| higher | 2-categories and bicategories of spans and of profunctors; pasting diagrams | planned |
| logic | The internal language: regular and coherent theories, their models as functors, sketches | planned |

## 3. Checks

`node development/tools/run-cpp.mjs foundations/kategoria foundations/kategoria` from the infrastructure's root builds and runs the 190 checks. Each holds against an answer known beforehand: counts in closed form (monotone maps between ordinals, homomorphisms between groups, the arrows of FinSet and Δ truncated); the naive enumeration, where the search must find exactly what it finds; morphe's tables of S₃, D₄ and Q₈ against their presentations; the simplex category up to [2] rebuilt from its faces, degeneracies and the cosimplicial identities; Galois connections, meets and joins as adjoints; induction and coinduction along a subgroup as Kan extensions; the truth values over an ordinal, a group and a monoid with an idempotent; and the laws of bialgebras, Hopf algebras and Frobenius algebras in finite sets, relations and matrices.

## 4. Dependencies

morphe (canonical forms of labelled graphs, the BNF reader and Earley's parser, permutation groups) and calx (its `verification`, for the checks). Header-only C++20.

## 5. Licence

MIT; see [LICENSE](LICENSE) and [CONTRIBUTORS.txt](CONTRIBUTORS.txt).
