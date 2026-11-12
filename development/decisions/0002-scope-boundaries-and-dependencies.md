# 0002. Scope, Boundaries and Dependencies

- **Status:** Accepted
- **Date:** 2026-11-12
- **Decided by:** the user ("implement the category theory experiment studio, with formal verifier and visualizer … as an independent foundation") and Claude; the infrastructure's ADR 0100

## 1. Context

The infrastructure's algebraic foundation, morphe, planned a module `categories` from its first day, and named category theory its spine. The user asked for a studio of experiments in category theory with a formal verifier and a visualizer, and for its mathematics to stand as a foundation of its own.

Three things had to be settled: whether such a library is a foundation; where it stands against morphe; and what "formal verifier" means for a library that computes.

## 2. Decision

1. **A foundation.** Categories, functors and their universal constructions name no object in nature, and every domain whose structures compose may use them (schemas of data, processes, rewriting, networks). The library is a foundation, kategoria. The studio is a work of the infrastructure; the drawings are the visualization layer's.
2. **Above morphe.** kategoria depends on morphe and on calx's `verification`, and on nothing else. morphe keeps the structures (groups, graphs, complexes, words, grammars) and their algorithms; kategoria computes with categories as such and reads morphe's structures as categories where it needs them. morphe's planned `categories` row now points here (morphe's decision 0013).
3. **Scope.** A method is kategoria's when it computes with categories as objects of study or decides a claim about them: finite and presented categories; functors, transformations, adjunctions, monads; limits; set-valued functors and Kan extensions; monoidal theories and string diagrams; and a language in which these are stated.
4. **What "verifier" means here.** Every claim is answered with a verdict, holds, fails or undecided, with its evidence. Universal claims over finite structures are decided by examining every instance. What a search finds is checked by a function that does not share the search's code. Where a bound stops a search, the answer is undecided and says so. The checker of equational derivations knows only the presentation's equations. This is a verifier of claims about given, finite or finitely presented structures. It is not a proof assistant: it does not check proofs of theorems about all categories.
5. **Out of scope:** proof terms and type theory (morphe's planned `logic`); numerical linear algebra (calx); what a category is of (the domains); drawing (the infrastructure's `visualization/`).

## 3. Alternatives Considered

- **morphe's `categories` module, as planned.** It would keep one algebraic foundation. Rejected at the user's word, and for three reasons that hold on their own: the body is large (seven modules and a language at its founding); it needs morphe's graphs, canonical forms, grammars and groups beneath it, as syntaxis needed morphe's and physis's; and a language of claims with its session is a different kind of thing from a module of algebra.
- **Below morphe, so that morphe could build on it.** morphe's structures do not need categories to be computed with, and kategoria needs morphe's algorithms. The order chosen has no cycle and loses nothing: where morphe's own structures are wanted as categories, kategoria builds them.
- **A proof assistant's kernel** (dependent types, tactics). It answers another question, and good ones exist. What a working mathematician lacks is a place to try a finite case and be told exactly where a claim fails.
- **Booleans with messages.** Rejected: an answer that cannot say where it fails teaches nothing, and an answer that cannot say "not decided" will sometimes lie.

## 4. Consequences

- morphe's "categorical spine" is read as kategoria reading morphe's structures, not as morphe depending on categories. If a generic construction is one day wanted beneath morphe's structures, it is proposed there.
- The library decides only what is finite or finitely presented. Statements about all categories are outside it, and are said to be.
- The name is provisional until the user confirms it.
