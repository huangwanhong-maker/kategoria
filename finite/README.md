# Finite Categories

Status: **draft** (2026-11-12). Module `kategoria::finite`.

## 1. Concepts

A finite category is held as its table of composition, as a finite group is held as its table. Whether a table is a category is a claim, answered by `validate` with the arrows at which an axiom fails. The families are those a first course meets: ordinals and other orders (thin categories), monoids and groups (one object), and the first objects of FinSet and of the simplex category. Theory: [docs/theory.md](../docs/theory.md), §1.

## 2. Content

- `category.hpp`: `Category{name, objects, arrows, identity, table, basis}` with `compose(g, f)` = g ∘ f, `hom(a, b)`, `object(name)`, `arrow(name)`, `typed(f)`; `assemble(…, compose)`; `validate(C)`.
- Families: `discrete`, `preorder(objects, leq)`, `chain(n)`, `divisors(n)`, `subsets(n)`, `monoid(elements, table)`, `multiplicative(n)`, `group(n, table, name, elements)`, `concrete(…, maps)` (functions composed as functions), `finset(n)`, `simplex(n)`.
- Constructions: `opposite`, `product`, `coproduct`, `full_subcategory`, `slice`, `coslice` (each with the places of its objects and arrows in the category it was made from).
- Properties: `inverse`, `is_iso`, `monic`, `epic` (verdicts naming the two arrows identified), `initial_objects`, `terminal_objects`, `isomorphism_classes`, `skeleton`, `is_thin`, `is_groupoid`, `is_discrete`, `components`, `generated(C, by)`, `generators(C)`.

## 3. Checks

36: the families against their counts in closed form; a table that is not associative refused at three named arrows; the opposite of the opposite; slices and coslices by their counts; the 8 monic, 5 epic and 4 invertible arrows of FinSet up to 2; skeletons and components; generators (the covers of an order, the faces and degeneracies of Δ, a few elements of a group), and that a category with retractions still gets arrows that generate it.

## 4. Dependencies

`kategoria::kernel`. The checks use morphe's `algebra` for the tables of groups.

## 5. References

Mac Lane (1998), I.1–I.5, II.2–II.4.
