# Categories Computed With: What kategoria Decides, and on What It Rests

Status: **draft** (2026-11-12).

This note states what each module of kategoria computes, the definitions it uses, and why its answers are right. Definitions follow Mac Lane, *Categories for the Working Mathematician* (2nd ed., 1998; cited as CWM with chapter and section). Statements proved here are short; the others are cited.

## 1. Categories Given Whole

**Definition 1.1.** A *finite category* $\mathcal C$ is finite sets of objects and arrows, maps $\operatorname{dom}, \operatorname{cod}$, an identity $1_a$ for each object, and a composite $g \circ f$ for each pair with $\operatorname{cod} f = \operatorname{dom} g$, such that $\operatorname{dom}(g \circ f) = \operatorname{dom} f$, $\operatorname{cod}(g\circ f) = \operatorname{cod} g$, $f \circ 1 = f = 1 \circ f$, and $h \circ (g \circ f) = (h \circ g)\circ f$ (CWM I.1).

It is held as its table of composition (`finite::Category`), of $n^2$ entries for $n$ arrows. `validate` examines every instance of every axiom, $O(n^3)$, and answers a failure with the arrows at which it fails. Every other claim about a finite category is a statement about finitely many arrows, and is decided by examining them.

*Remark.* Thin categories are preorders; categories with one object are monoids; groupoids with one object are groups. The families of `finite` are these, with the full subcategories of $\mathbf{FinSet}$ and of the simplex category $\Delta$ on their first objects.

**Proposition 1.2 (generators).** In a category where an arrow $d$ has a retraction $s$ ($s \circ d = 1$), $d = (d \circ s)\circ d$ is a composite of two arrows that are not identities. So "the arrows that are no composite of two non-identities" generate a partial order (they are its covers) and need not generate a category with retractions.

*Consequence.* `finite::generators` uses the basis a construction gives (the covers of a partial order; the faces and degeneracies of $\Delta$; a presentation's own generators; a product's pairs of a generator and an identity). Without one it adds arrows in order until they generate, and says that the choice is one that generates and not a canonical one. The faces and degeneracies of $\Delta_{\le 2}$ are themselves not the fewest that generate: $\delta_0 = \sigma_1 \delta_0 \delta_1$ (a check of `presentations`).

## 2. Evidence

**Definition 2.1.** A *verdict* on a claim is one of *holds*, *fails*, *undecided*, with a reason and named pieces of evidence (`kernel::Verdict`).

The rule of the library has three parts.

1. *Universal claims* ("$F$ keeps every composite", "every cone factors once") over a finite structure are decided by examining every instance. A failure is answered with a counterexample, by name.
2. *Existential claims* ("there is a limit", "there is a left adjoint", "the two paths are equal", "the categories are isomorphic") are decided by a search. What the search finds is a *witness*, and it is verified by a function that states the definition and does not share the search's code: `is_limit` for `limit`, `verify_adjunction` for `left_adjoint`, `check` for `prove`, `verify` for every functor found. A witness that does not verify is reported as undecided, never as holding.
3. *Negative existential claims* have no small witness in general. They are answered *fails* only where the search is exhaustive over a finite space (every cone was a candidate; every bijection was tried), and that is said; or where a certificate of another kind exists (two different normal forms under a rewriting system verified to be confluent, §5). Otherwise the answer is *undecided*.

*Remark.* This is the criterion of de Bruijn for proof checkers, in the small: the part that must be trusted is the part that checks, and it is kept short (`presentations::check` is thirty lines and knows only the equations).

## 3. Functors, Transformations, Adjoints

**Search for functors.** A functor $F : \mathcal C \to \mathcal D$ is determined by its values on arrows that generate $\mathcal C$. `for_each_functor` assigns arrows one at a time and carries each assignment to its consequences: the ends of an arrow fix the images of its objects; an identity goes to an identity; two assigned arrows that compose fix the image of their composite. It branches only where nothing forces a value.

**Proposition 3.1.** The assignments `for_each_functor` completes are exactly the functors $\mathcal C \to \mathcal D$, each once.

*Proof.* Every propagation step is forced by the definition of a functor, so no functor is lost, and the search tries every value of every arrow it branches on. A completed assignment has every arrow assigned and every composable pair propagated without conflict, so it keeps ends, identities and composites. Two completed assignments differ at some branch, so none is visited twice. $\square$

The checks compare the count with the naive enumeration of all maps of arrows, and with closed forms ($\binom{m+k-1}{m}$ monotone maps from the ordinal $m$ to the ordinal $k$; homomorphisms between small groups).

**Equivalence.** A functor is an equivalence exactly when it is full, faithful and essentially surjective (CWM IV.4, Theorem 1). `equivalence` builds the functor back by choosing, for each object $d$, an object $c_d$ with an isomorphism $F c_d \cong d$, and verifies what it built. Two finite categories are equivalent exactly when their skeletons are isomorphic (CWM IV.4), which `equivalent` decides by searching for a functor injective on arrows.

**Adjoints.** $R : \mathcal D \to \mathcal C$ has a left adjoint exactly when every object $c$ has a universal arrow $c \to R d$ (CWM IV.1, Theorem 2). `left_adjoint` searches for one at each object; where an object has none it is named, and the answer is *fails* (the search over $d$ and over arrows $c \to Rd$ is exhaustive). Where every object has one, the adjoint, its unit and its counit are built and `verify_adjunction` checks naturality and both triangle identities. A right adjoint is a left adjoint between the opposite categories.

**Monads.** `verify_monad` checks the unit and associativity laws (CWM VI.1); `monad_of` gives $T = RL$, $\eta$, $\mu = R\varepsilon L$; `eilenberg_moore` and `kleisli` build the categories of algebras and of free algebras (CWM VI.2, VI.5).

## 4. Limits

**Definition 4.1.** A *cone* on $D : \mathcal J \to \mathcal C$ is an object $a$ with arrows $\lambda_j : a \to D j$ such that $D u \circ \lambda_j = \lambda_k$ for each $u : j \to k$. It is a *limit* when every cone $(b, \kappa)$ has exactly one $h : b \to a$ with $\lambda_j \circ h = \kappa_j$ for all $j$ (CWM III.3–III.4).

`is_limit` lists the cones on $D$ and counts the factorisations of each. `limit` returns the first cone that `is_limit` accepts. Colimits are limits in the opposite category.

**Finite completeness.** A category has every finite limit when it has a terminal object, binary products and equalizers (CWM V.2); `finitely_complete` checks those three and names the first diagram without a limit.

**Exponentials.** $b^a$ with $\mathrm{ev} : b^a \times a \to b$ is universal among arrows $c \times a \to b$ (CWM IV.6). A lattice is cartesian closed exactly when it is a Heyting algebra; a finite lattice is one exactly when it is distributive. The checks hold the subsets of a set, an ordinal and the divisors of 12 to be cartesian closed, and the diamond $M_3$ and the pentagon $N_5$ not to be.

## 5. Presentations

**Definition 5.1.** A *presentation* is a quiver $Q$ and equations $l_i = r_i$ between parallel paths of $Q$. It presents the quotient of the free category on $Q$ by the least congruence containing the equations (CWM II.8).

Whether two paths are equal in that quotient is the word problem of a monoid with several objects, which is undecidable in general (Markov 1947; Post 1947). kategoria attacks it by completion.

**Rules.** Paths with one source and target are ordered by *shortlex*: shorter first, then by their edges in order. This is a well-order compatible with composition. A *rule* $l \to r$ has $l > r$. The rules *reduce* a path by replacing an occurrence of some $l$ by its $r$; reduction ends, since each step decreases the path.

**Completion** (Knuth and Bendix 1970; for words and paths, Book and Otto 1993, ch. 2). Each equation is oriented into a rule. A *critical pair* arises where two left sides overlap or one contains another: the path on which both rules apply has two reducts. Each pair is reduced on both sides; where the normal forms differ, the greater is made a rule that rewrites to the lesser. The procedure ends when every critical pair joins.

**Proposition 5.2.** If completion ends, the rules are terminating and confluent, so every path has exactly one normal form, and two paths are equal in the presented category exactly when their normal forms coincide.

*Proof.* Termination is by the shortlex order. Every critical pair joins, so the system is locally confluent (the critical pair lemma), and a terminating, locally confluent system is confluent (Newman 1942). Every rule is a consequence of the equations, and every equation's sides have one normal form, so the congruence generated by the rules is that of the equations. $\square$

**Derivations.** Each rule carries a derivation of its right side from its left by the *original* equations: for a rule made from a critical pair, the derivation runs back along one reduction to the peak and forward along the other. A reduction of a path is then a derivation in the equations' own terms, and two paths with one normal form are joined by a derivation `check` verifies. `check` replays the steps knowing only the equations; nothing of the completion is trusted.

**Inequality.** `certify` verifies on the rules as they stand that each decreases, each is derived from the equations by its own derivation, and every critical pair joins. By Proposition 5.2 two different normal forms then show two paths unequal.

**The finite category.** When completion ends, the normal forms are the paths no left side occurs in. They are listed breadth first; when they are at most a bound, the category whose arrows are the normal forms and whose composite is the normal form of the concatenation is built. It is a category by Proposition 5.2, and `validate` confirms it.

*Caveat.* Completion need not end even when the word problem is decidable: for the braid monoid $\langle a, b \mid aba = bab \rangle$ in the shortlex order it produces rules without end. The answer is then *undecided* for paths whose normal forms so far differ, and equalities found are still proved.

*Found while checking.* The full subcategory of $\Delta$ on $[0], [1], [2]$ is presented by its eight faces and degeneracies with the twelve cosimplicial identities among them: completion ends with twelve rules and 31 normal forms, and the category built is isomorphic to the one given by monotone maps.

## 6. Set-Valued Functors

A functor $X : \mathcal C \to \mathbf{FinSet}$ is a finite set for each object and a function for each arrow. Read as data, $\mathcal C$ is a schema and $X$ an instance (Spivak 2012).

**Natural transformations** $X \Rightarrow Y$ are found by fixing the image of one element at a time and carrying it along every arrow out of its object: naturality forces the images of the whole orbit.

**Yoneda** (CWM III.2). $\operatorname{Nat}(\mathcal C(a, -), X) \cong X(a)$, by $\alpha \mapsto \alpha_a(1_a)$. `yoneda` lists the transformations and checks that the map is a bijection.

**Limits and colimits.** The limit of $X$ is the set of its sections, the natural transformations $1 \Rightarrow X$; the colimit is the set of classes of elements under $x \sim X(f)\,x$ (CWM III.3, V.1).

**Kan extensions** (CWM X.3, Theorem 1). For $K : \mathcal C \to \mathcal D$:

$$(\operatorname{Lan}_K X)(d) = \operatorname*{colim}_{(c,\; h : Kc \to d)} X(c), \qquad (\operatorname{Ran}_K X)(d) = \lim_{(c,\; h : d \to Kc)} X(c).$$

The left extension at $d$ is the set of triples $(c, h, x)$ modulo $(c, h' \circ Kf, x) \sim (c', h', X(f)x)$; the right is the set of families $s(c, h) \in X(c)$ with $X(f)\,s(c, h) = s(c', Kf \circ h)$. With the pullback $Y \mapsto Y \circ K$ they are the three functors $\Sigma_K \dashv \Delta_K \dashv \Pi_K$. `left_kan_universal` and `right_kan_universal` decide the universal property against a given $Y$: composing with the unit (or the counit) is a bijection between two sets of transformations, both listed.

*Checked.* Along a functor to a point the extensions are the colimit and the limit. $\operatorname{Lan}_K \mathcal C(c, -) \cong \mathcal D(Kc, -)$. Along the inclusion of a subgroup $H \le G$ they are induction and coinduction: a one-point $H$-set induces to the $[G:H]$ cosets and coinduces to one point, and the regular $H$-set coinduces to $|H|^{[G:H]}$ points.

**The classifier of subobjects** (Mac Lane and Moerdijk 1992, ch. I). In $[\mathcal C, \mathbf{Set}]$, $\Omega(c)$ is the set of cosieves on $c$ (sets of arrows out of $c$ closed under composition on the left), and $u : c \to c'$ sends $S$ to $\{g \mid g \circ u \in S\}$. Subfunctors of $X$ correspond to transformations $X \Rightarrow \Omega$ by $x \mapsto \{f \mid X(f)x \in S\}$. `classifies` lists both and checks the correspondence. The subfunctors under inclusion form a Heyting algebra, which `limits::cartesian_closed` confirms as a category.

## 7. Monoidal Theories

**Definition 7.1.** A *signature* is a set of types and a set of generators, each with a list of types in and a list out. *Terms* are built from generators, identities and symmetries by sequence and tensor. A *string diagram* is a set of wires, each with a type, each leaving at most one box and entering at most one, and boxes labelled by generators, with the diagram's own wires in and out in order.

**Theorem 7.2** (Joyal and Street 1991; in the form used here, Bonchi, Gadducci, Kissinger, Sobociński and Zanasi 2022). Two terms are equal in the free symmetric monoidal category on a signature exactly when their string diagrams are isomorphic by a bijection of wires and boxes that keeps types, generators, the order of each box's wires, and the diagram's wires in and out.

`monoidal::same` encodes a diagram as a labelled graph (a vertex for each wire, labelled by its type and its place among the diagram's wires in and out; a vertex for each box, labelled by its generator; an edge for each port, labelled by its side and place) and compares morphe's canonical forms. Where morphe's search gives up, the answer is undecided.

**Models.** A model sends each type to a dimension and each generator to a matrix over a semiring (the integers, the Booleans, or the integers modulo $n$), with the tensor the Kronecker product or the direct sum. Functions between finite sets with the cartesian product, relations, and linear maps are of the first kind; matrices as a PROP of the second. A law holds in a model when both sides evaluate to one matrix.

*Caveat.* A law that holds in one model says nothing of the theory. A law that fails in a model of the other laws shows it does not follow from them. Equality modulo a theory's laws, by rewriting diagrams with convex matches (Bonchi et al. 2022, part II), is planned.

*Checked.* $(2, \wedge, \top)$ with copying is a bialgebra among finite sets and not a Frobenius algebra; copying with its converse is a special commutative Frobenius algebra among relations (Carboni and Walters 1987); addition with copying on a line is a bialgebra over $\mathbb N$ (Lack 2004), a Hopf algebra over $\mathbb Z$ with antipode $-1$, and with antipode $1$ fails the Hopf law over the Booleans and satisfies it modulo 2.

## 8. The Language

A script declares categories, functors, transformations, set-valued functors, theories, models and diagrams, and states claims and questions. Its grammar is written in BNF and read by morphe's reader, so that a statement that is not understood is answered with how far it is right and what could come next. A statement that defines something is answered with the verdict that it is what it is declared to be, and the thing is kept under its name only when it is. Each answer carries a view of what there is to draw, which a work's page may show (`script/README.md`).

## 9. References

- Aristotle. *Categories*.
- Book, R. V., Otto, F. (1993). *String-Rewriting Systems*. Springer.
- Bonchi, F., Gadducci, F., Kissinger, A., Sobociński, P., Zanasi, F. (2022). String diagram rewrite theory I: rewriting with Frobenius structure. *Journal of the ACM* 69(2); II: rewriting with symmetric monoidal structure. *Mathematical Structures in Computer Science* 32(4).
- Carboni, A., Walters, R. F. C. (1987). Cartesian bicategories I. *Journal of Pure and Applied Algebra* 49.
- Eilenberg, S., Mac Lane, S. (1945). General theory of natural equivalences. *Transactions of the American Mathematical Society* 58.
- Joyal, A., Street, R. (1991). The geometry of tensor calculus I. *Advances in Mathematics* 88.
- Knuth, D. E., Bendix, P. B. (1970). Simple word problems in universal algebras. In *Computational Problems in Abstract Algebra*. Pergamon.
- Lack, S. (2004). Composing PROPs. *Theory and Applications of Categories* 13.
- Mac Lane, S. (1998). *Categories for the Working Mathematician*, 2nd ed. Springer.
- Mac Lane, S., Moerdijk, I. (1992). *Sheaves in Geometry and Logic*. Springer.
- Newman, M. H. A. (1942). On theories with a combinatorial definition of "equivalence". *Annals of Mathematics* 43.
- Spivak, D. I. (2012). Functorial data migration. *Information and Computation* 217.
