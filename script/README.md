# The Language of Scripts

Status: **draft** (2026-11-12). Module `kategoria::script`.

## 1. Concepts

A script declares categories, functors, natural transformations, set-valued functors, theories, models and diagrams, and states claims (`check`) and questions (`find`). Its grammar is written in BNF and read by morphe's reader, so that a statement that is not understood is answered with how far it is right and what could come next. A statement that defines something is answered with the verdict that it is what it is declared to be, and the thing is kept under its name only when it is; a statement that cannot be carried out is answered with the reason, and the script goes on. Each answer carries a view of what there is to draw. In a set-valued functor, an arrow out of an object with no element need not be written, since there is one function from the empty set.

## 2. Content

- `language.hpp`: `grammar_text()` (the grammar of one statement, in BNF; its header comment is the language's summary), `grammar()`, `statements(script)` (a script cut into statements with their lines), `name_of`.
- `session.hpp`: `Session` with `most_arrows` and `run(script)` → a list of outcomes, each `{line, text, kind, name, status, claim, reason, evidence, examined, view}`; `Refusal`. The views, by their `type`: `category` (objects, arrows with their kinds, generators, the table when small, equations, facts), `functor`, `transformation`, `adjunction`, `sets`, `cone`, `derivation`, `string`, `theory`, `laws`, `table`, `composition`.
- `document.hpp`: `Value`, a small tree of maps, lists, texts and numbers that writes itself as JSON.

What one may write:

```
category Sq { objects A B C D;  f : A -> B;  g : B -> D;  h : A -> C;  k : C -> D;  g . f = k . h }
category P = product C D          chain 4 · discrete 3 · subsets 3 · divisors 12 · finset 2 · simplex 2 · mult 6 · cyclic 4 ·
                                  symmetric 3 · dihedral 4 · quaternion · arrow · iso · pair · point · op C · skeleton C ·
                                  arrows C · elements X · subobjects X · algebras L · kleisli L · sum C D · slice C A ·
                                  coslice C A · functors C D · comma F G
functor F : C -> D { A -> X;  f -> v . u }
functor G = left adjoint F        identity C · compose G F · constant C D X · right adjoint F · diagonal C · first P ·
                                  second P · projection E
transformation t : F => G { A -> u }
sets X : C { A = {a, b};  B = {c};  f : a -> c, b -> c }
sets Y = lan X K                  hom C A · constant C 2 · pullback Y K · ran X K · omega C
theory M { type x;  m : x x -> x;  e : I -> x;  law unit : (e * x) >> m = x }
model B : M in sets { x = 2;  m = 0 0 0 1;  e = 1 }        in sets · relations · matrices · sums, then: mod 2 · boolean
diagram d = (m * x) >> m in M
check g . f = k . h in Sq         check F · check F is faithful · check f is mono in C · check C is complete · check L -| R ·
                                  check C equivalent D · check C isomorphic D · check yoneda X A · check classifier X
find product A B in C             find limit F · find terminal in C · find equalizer f g in C · find exponential A B in C ·
                                  find functors C -> D · find transformations F => G · find generators C · find rules C ·
                                  find table C · find subfunctors X · find sections X · find classes X
```

## 3. Checks

21: scripts with the status each statement must be answered with and a word that must stand in the answer: a commutative square and its derivation; S₃ presented, proved and refuted; functors that are, that break an equation, that are left open; adjoints between ordinals; limits in a lattice and what FinSet truncated lacks; an instance, its Kan extensions, Yoneda and the classifier; theories and their models; equivalence and isomorphism; categories that are not finite; and what cannot be read or carried out, with its line and column.

## 4. Dependencies

`kategoria::limits`, `sets`, `presentations`, `monoidal`; morphe's `formal` (grammars in BNF, Earley's parser) and `algebra` (permutation groups).

## 5. References

Backus (1959) and ISO/IEC 14977 for the notation of the grammar; Earley (1970).
