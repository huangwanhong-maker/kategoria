# Verdicts

Status: **draft** (2026-11-12). Module `kategoria::kernel`.

## 1. Concepts

A claim is answered in one of three ways, never with a bare yes or no: it *holds*, with what makes it so; it *fails*, with the place where it fails; it is *undecided*, with the reason no answer was reached. The evidence is a list of named pieces in words, so that a reader, a page or another program can show it. The rule every module follows is in [docs/theory.md](../docs/theory.md), §2: universal claims over finite structures are decided by examining every instance; what a search finds is checked by a function that does not share its code.

## 2. Content

- `verdict.hpp`: `Status` (`holds`, `fails`, `undecided`) and `word(status)`; `Evidence{role, value}`; `Verdict{status, claim, reason, evidence, examined}` with `holds()`, `fails()`, `with(role, value)`, `piece(role)`, and the makers `Verdict::yes`, `no`, `unknown`; `both(a, b)`, the first of two that does not hold; `count(n, one, many)`, a number with its noun.

## 3. Checks

The kernel has no check program of its own: every other module's checks read its verdicts.

## 4. Dependencies

None.

## 5. References

de Bruijn's criterion for proof checkers (a small part that checks) is the model; see the theory note, §2.
