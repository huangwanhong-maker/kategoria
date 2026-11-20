# CLAUDE.md

This file guides Claude Code in the kategoria repository.

kategoria is one of the foundation libraries of [Noetarium, the Science and Humanity Infrastructure](https://github.com/huangwanhong-maker/Noetarium-The-Science-and-Humanity-Infrastructure), which includes it as the git submodule `foundations/kategoria`. It is a project in its own right and must make sense without the infrastructure.

## 1. Purpose and Scope

kategoria computes with categories as objects of study, and decides claims about them:

- finite categories given whole, and categories presented by generators and equations;
- functors, natural transformations, equivalences, adjunctions and monads;
- limits and colimits, and what functors keep of them;
- set-valued functors: representables, elements, Kan extensions, the classifier of subobjects;
- symmetric monoidal theories: string diagrams, their equality, their models;
- resource types: symmetric monoidal preorders with their laws verified and each verdict scoped, allocations as morphisms, and the order of grants decided on finite systems (decision 0004);
- a language in which such things are declared and claims about them are stated, answered statement by statement;
- later, rewriting of diagrams modulo a theory, enriched and higher categories, and the internal language.

It builds on two sibling libraries:

- **morphe**, for canonical forms of labelled graphs, grammars written in BNF with Earley's parser, and finite groups;
- **calx**, for the report of its checks.

Out of scope:

| Topic | Where it belongs |
|---|---|
| Groups, rings, modules, lattices and their algorithms for their own sake; graphs; complexes; formal languages and their parsers; graph rewriting | morphe's `algebra`, `combinatorics`, `topology` and `formal` |
| The λ-calculi, proof terms and proof assistants; satisfiability | morphe's planned `logic` |
| Numerical linear algebra: matrices over floating-point numbers | calx |
| What a category is *of*: a schema of a database, a process of a market, a network of reactions | the domains of the infrastructure |
| Drawing diagrams of categories and string diagrams | the infrastructure's `visualization/` and its works |

The boundary is [decision 0002](development/decisions/0002-scope-boundaries-and-dependencies.md): a method that computes with categories as such, or decides a claim about them, is kategoria's; a structure that happens to form a category stays where it is, and kategoria reads it as one.

## 2. Invariants

1. **Dependencies.** kategoria depends only on morphe and calx among project libraries, and never on physis, tyche, peira, nomos, eikon, heuresis, syntaxis or the infrastructure's domains, edges or applications.
2. **No particular objects.** Nothing in kategoria names an object in nature; its examples are mathematical.
3. **Pure.** No I/O, no global state, no randomness.
4. **Evidence.** A claim is answered with a `Verdict`: holds, fails or undecided, with the reason and the evidence. No function answers a claim with a bare boolean where a place of failure can be named.
5. **Search and check apart.** What a search finds (a limit, an adjoint, a derivation, an isomorphism) is verified by a function that does not share the search's code, before it is reported as holding.
6. **Undecided is said.** Where a bound stops a search or a completion, the answer is undecided with the reason; nothing is reported as failing that was only not found, except where the search is exhaustive, and then that is said.
7. **Exact.** Arithmetic is on integers; an entry that outgrows 64 bits is refused, never wrapped.
8. **Truth known.** Checks are held to answers known in closed form, to brute force, or to structures built another way. Reference values from other software come from running it, never from memory.
9. **Reuse.** What a sibling holds is used through its public headers, never written again here.
10. **Cited sources.** Every implemented method cites its source; theorem or section numbers are given only where certain.

## 3. Design Philosophy

kategoria shares its governing principle with its sibling repositories: **modular, extensible, revisable**.

- **Status vocabulary:**
  - `planned`: named, no content yet;
  - `seed`: an idea, possibly wrong;
  - `draft`: being worked out;
  - `stable`: tested and relied upon;
  - `deprecated`: superseded, with a pointer to its replacement.
- **One answer.** Every module answers with the kernel's verdict, so that a reader, a page or another program treats all answers alike.
- **Data whole.** A finite category is its table; a functor its values on every arrow; a set-valued functor its sets and functions. Nothing is lazy, so that every claim can be decided by looking.

## 4. Repository Layout

```
kategoria/
├── CMakeLists.txt   the project: one header-only target kategoria::<module> per module (kategoria_module); the siblings added once
├── kernel/ · finite/ · functors/ · limits/ · sets/ · presentations/ · monoidal/ · resources/ · script/
├── docs/            the theory note
└── development/     decisions · ideas · release notes
```

Each module directory holds:
- `README.md`: concepts first, then the content, then the checks;
- `include/kategoria/<module>/`;
- `tests/check_<module>.cpp`, a check program on calx's `verification`, registered with CTest by `kategoria_module` in the top-level `CMakeLists.txt`.

The modules and their order are in [decision 0003](development/decisions/0003-the-first-modules.md).

## 5. Working Procedures

### 5.1 Decisions and Ideas

- Decisions are numbered records in `development/decisions/`. Records are never rewritten; a later record supersedes an earlier one.
- Ideas are files named `development/ideas/YYYY-MM-DD-slug.md`, with status `seed`, `promoted` or `abandoned`.
- **Release notes.** At each commit, add to `development/release-notes/YYYY-MM-DD.md` (one file per day, one short section per commit) a concise summary in plain prose of what is new, what one can now do and what works better. It is not a list of changes (the git log keeps those), and it is not written between commits.

### 5.2 Change Discipline

- Before restructuring or changing an invariant (§2), propose the change and wait for the user's agreement.
- Keep each change to one concept.
- A change to the language (`script/`) changes its grammar, its session, its checks and the header comment of `language.hpp` together.

### 5.3 Shared Conventions

calx, morphe, physis, tyche, peira, nomos, eikon, heuresis, syntaxis, kategoria and the infrastructure keep these conventions identical:

- writing style;
- status vocabulary;
- decision, idea and release-note conventions.

Change them in every repository together.

### 5.4 Working Inside the Infrastructure

When you edit kategoria inside the infrastructure's `foundations/kategoria`:

1. commit in kategoria first;
2. then commit the updated pointer in the infrastructure.

When a change needs a sibling to change as well, commit them in dependency order: calx and morphe first, then kategoria.

## 6. Conventions

- **Composition.** `compose(g, f)` is g ∘ f, "g after f". A path lists its edges in the order travelled: {f, g} is g ∘ f. In words an arrow is written as a composite, the arrow travelled first at the right.
- **Indices.** Objects and arrows are indices into their lists; `none` stands for "no such". In the categories built here the identities come first, unless said otherwise.
- **Names.** An object or an arrow has a name for those who read it; nothing computes with names, except the script language, which resolves them once.
- **Colimits.** A cocone is held as a cone whose legs run into the apex; a colimit is computed as a limit in the opposite category.
- **Set-valued functors** are covariant (C → FinSet); a presheaf is one on the opposite category.
- **Diagrams** are read in the order the wires pass: a sequence lists its parts from first to last. A matrix has a row for each output and a column for each input.
- **Writing style.**
  - Headings are declarative, numbered and academic, never questions.
  - Concepts come before structure.
  - Label asides with *Rationale.*, *Remark.* or *Caveat.*
  - British spelling; English throughout.

## 7. Technology

- **Language: C++.** This follows ADR 0003 of the infrastructure.
- **Provisional:** C++20 without extensions, header-only targets `kategoria::<module>`; CMake 3.20 or later. Checks are programs on calx's `verification`, registered with CTest. On the development machine the compiler is GCC in WSL.
- **Dependency resolution.** Inside the infrastructure, kategoria uses the targets of `foundations/calx` and `foundations/morphe`, adding each that no larger project has added. Never nest submodules.
