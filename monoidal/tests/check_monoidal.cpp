// Checks of kategoria/monoidal: terms, diagrams, their equality, and models.
//
// - Typing: a sequence whose parts do not meet is refused at the part that does not fit.
// - Equality in the free symmetric monoidal category: the interchange law, the naturality of the symmetry, its
//   involution and the Yang–Baxter equation hold as equalities of diagrams; f ⊗ g ≠ g ⊗ f, and associativity of a
//   multiplication, which is a law of a theory and not of the structure, does not hold.
// - Models with the Kronecker product: (2, ∧, true) is a commutative monoid among finite sets; copying and deleting are
//   a commutative comonoid; the two form a bialgebra; they are not a Frobenius algebra, and the entry where the
//   Frobenius law fails is named. Among relations, copying and its converse are one (Carboni and Walters 1987).
// - Models with the direct sum: addition, zero, copy and discard on a line are a bialgebra over the natural numbers
//   (matrices as a PROP; Lack 2004); with the antipode −1 a Hopf algebra over ℤ; with the antipode 1 the Hopf
//   law fails over the Booleans, where 1 + 1 = 1, and holds modulo 2.

#include <kategoria/monoidal/monoidal.hpp>

#include <calx/verification/check.hpp>

#include <string>
#include <vector>

using namespace kategoria::monoidal;

int main() {
  calx::verification::Suite s;
  // One type x; boxes f, g, h, k : x → x; m : x ⊗ x → x, e : I → x; d : x → x ⊗ x, c : x → I; a : x → x.
  Signature S{"a signature", {"x"}, {{"f", {0}, {0}}, {"g", {0}, {0}}, {"h", {0}, {0}}, {"k", {0}, {0}}, {"m", {0, 0}, {0}}, {"e", {}, {0}}, {"d", {0}, {0, 0}}, {"c", {0}, {}}, {"a", {0}, {0}}}};
  const Term f = gen(0), g = gen(1), h = gen(2), k = gen(3), m = gen(4), e = gen(5), d = gen(6), c = gen(7), a = gen(8), x = id({0}), sw = swap(0, 0);

  // Typing.
  const Typed t1 = type(S, seq({par({f, g}), m}));
  s.require("type: (f ⊗ g) ; m is x ⊗ x → x", t1.verdict.holds() && t1.in == std::vector<Index>{0, 0} && t1.out == std::vector<Index>{0});
  const Typed t2 = type(S, seq({m, m}));
  s.require("type: m ; m is refused, the second m not fitting the one wire the first leaves", t2.verdict.fails() && !t2.verdict.piece("at").empty(), t2.verdict.reason);
  s.require("type: the unit is I → I, and e ⊗ e is I → x ⊗ x", type(S, id()).in.empty() && type(S, par({e, e})).in.empty() && type(S, par({e, e})).out.size() == 2);

  // Diagrams.
  const Diagram D = diagram(S, seq({par({f, g}), m, d, par({h, c})}));
  s.require("diagram: (f ⊗ g) ; m ; d ; (h ⊗ c) has 6 boxes, 8 wires, 2 in and 1 out, at depths 0, 0, 1, 2, 3, 3",
            D.boxes.size() == 6 && D.wires.size() == 8 && D.inputs.size() == 2 && D.outputs.size() == 1 && depths(D) == std::vector<Index>{0, 0, 1, 2, 3, 3});

  // Equality by the axioms alone.
  auto holds = [&](const std::string& what, const Term& l, const Term& r) {
    const auto v = same(S, l, r);
    s.require(what, v.holds(), v.reason);
  };
  auto fails = [&](const std::string& what, const Term& l, const Term& r) {
    const auto v = same(S, l, r);
    s.require(what, v.fails(), v.reason);
  };
  holds("the interchange law: (f ⊗ g) ; (h ⊗ k) = (f ; h) ⊗ (g ; k)", seq({par({f, g}), par({h, k})}), par({seq({f, h}), seq({g, k})}));
  holds("sliding: (f ⊗ x) ; (x ⊗ g) = (x ⊗ g) ; (f ⊗ x) = f ⊗ g", seq({par({f, x}), par({x, g})}), seq({par({x, g}), par({f, x})}));
  holds("the symmetry is natural: (f ⊗ g) ; σ = σ ; (g ⊗ f)", seq({par({f, g}), sw}), seq({sw, par({g, f})}));
  holds("the symmetry is an involution: σ ; σ = x ⊗ x", seq({sw, sw}), id({0, 0}));
  holds("the Yang–Baxter equation: (σ ⊗ x) ; (x ⊗ σ) ; (σ ⊗ x) = (x ⊗ σ) ; (σ ⊗ x) ; (x ⊗ σ)", seq({par({sw, x}), par({x, sw}), par({sw, x})}), seq({par({x, sw}), par({sw, x}), par({x, sw})}));
  holds("the unit: f ⊗ I = f, and identities compose away", par({f, id()}), seq({x, f, x}));
  holds("scalars commute: (e ; c) ⊗ f = f ⊗ (e ; c)", par({seq({e, c}), f}), par({f, seq({e, c})}));
  fails("f ⊗ g ≠ g ⊗ f", par({f, g}), par({g, f}));
  fails("f ; g ≠ g ; f", seq({f, g}), seq({g, f}));
  fails("associativity is no axiom: (m ⊗ x) ; m ≠ (x ⊗ m) ; m", seq({par({m, x}), m}), seq({par({x, m}), m}));
  fails("commutativity is no axiom: σ ; m ≠ m", seq({sw, m}), m);
  const auto typed = same(S, m, d);
  s.require("same: terms of different types are refused, with both types", typed.fails() && typed.piece("left") == "x ⊗ x → x" && typed.piece("right") == "x → x ⊗ x", typed.reason);

  // Theories.
  const Signature B{"bialgebras", {"x"}, {{"m", {0, 0}, {0}}, {"e", {}, {0}}, {"d", {0}, {0, 0}}, {"c", {0}, {}}, {"a", {0}, {0}}}};
  const Term M = gen(0), E = gen(1), Dl = gen(2), C = gen(3), A = gen(4);
  const std::vector<Law> monoid{{"associativity", seq({par({M, x}), M}), seq({par({x, M}), M})}, {"the left unit", seq({par({E, x}), M}), x}, {"the right unit", seq({par({x, E}), M}), x}};
  const std::vector<Law> comonoid{{"coassociativity", seq({Dl, par({Dl, x})}), seq({Dl, par({x, Dl})})}, {"the left counit", seq({Dl, par({C, x})}), x}, {"the right counit", seq({Dl, par({x, C})}), x}};
  const Law commutative{"commutativity", seq({sw, M}), M}, cocommutative{"cocommutativity", seq({Dl, sw}), Dl};
  const std::vector<Law> bialgebra{{"the bialgebra law", seq({M, Dl}), seq({par({Dl, Dl}), par({x, sw, x}), par({M, M})})}, {"unit then copy", seq({E, Dl}), par({E, E})}, {"multiply then discard", seq({M, C}), par({C, C})}, {"unit then discard", seq({E, C}), id()}};
  const Law frobenius{"the Frobenius law", seq({par({Dl, x}), par({x, M})}), seq({M, Dl})}, special{"speciality", seq({Dl, M}), x};
  const Law hopf{"the antipode law", seq({Dl, par({x, A}), M}), seq({C, E})};
  auto theory = [&](std::string name, std::vector<std::vector<Law>> parts) {
    Theory T{B, {}};
    T.signature.name = std::move(name);
    for (auto& p : parts) T.laws.insert(T.laws.end(), p.begin(), p.end());
    return T;
  };
  const Theory bialgebras = theory("commutative and cocommutative bialgebras", {monoid, comonoid, {commutative, cocommutative}, bialgebra});
  s.require("the laws of bialgebras are well formed", well_formed(bialgebras).holds());
  Theory crooked = bialgebras;
  crooked.laws.push_back({"a law between different types", M, Dl});
  s.require("well_formed: a law whose sides have different types is refused and named", well_formed(crooked).fails() && well_formed(crooked).piece("at") == "a law between different types");

  // Finite sets with ×: x is the set 2; m is ∧, e is true, d copies, c deletes, a is the identity.
  Model sets{"(2, ∧, true) with copying, among finite sets", Semiring::integer, 0, true, {2}, {function({0, 0, 0, 1}, 2), function({1}, 2), function({0, 3}, 4), function({0, 0}, 1), function({0, 1}, 2)}};
  s.require("finite sets: (2, ∧, true) with copy and delete is a commutative, cocommutative bialgebra", satisfies(bialgebras, sets).holds(), satisfies(bialgebras, sets).reason);
  const auto fv = holds_in(B, sets, frobenius.left, frobenius.right, frobenius.name);
  s.require("finite sets: it is no Frobenius algebra; the two sides differ at a named entry", fv.fails() && !fv.piece("at").empty(), fv.reason);
  s.require("finite sets: ∧ after copying is the identity (speciality: x ∧ x = x)", holds_in(B, sets, special.left, special.right).holds());
  Model xor_{"(2, ⊕, false) with copying", Semiring::integer, 0, true, {2}, {function({0, 1, 1, 0}, 2), function({0}, 2), function({0, 3}, 4), function({0, 0}, 1), function({0, 1}, 2)}};
  s.require("finite sets: (2, xor, false) with copy and the identity as antipode is a Hopf algebra (a group: x xor x = false), where ∧ is none",
            satisfies(theory("Hopf algebras", {monoid, comonoid, bialgebra, {hopf}}), xor_).holds() && holds_in(B, sets, hopf.left, hopf.right).fails());

  // Relations: copy and its converse.
  Model rel{"copying and its converse, among relations", Semiring::boolean, 0, true, {2}, {Matrix{2, 4, {1, 0, 0, 0, 0, 0, 0, 1}}, Matrix{2, 1, {1, 1}}, function({0, 3}, 4), Matrix{1, 2, {1, 1}}, function({0, 1}, 2)}};
  const Theory frobenius_algebras = theory("special commutative Frobenius algebras", {monoid, comonoid, {commutative, cocommutative, frobenius, special}});
  s.require("relations: copying and its converse are a special commutative Frobenius algebra", satisfies(frobenius_algebras, rel).holds(), satisfies(frobenius_algebras, rel).reason);
  const auto bv = holds_in(B, rel, bialgebra[1].left, bialgebra[1].right, bialgebra[1].name);
  s.require("relations: they are no bialgebra: the unit copied is not two units", bv.fails() && holds_in(B, rel, bialgebra[0].left, bialgebra[0].right).holds(), bv.reason);

  // Matrices with ⊕: x is a line; m adds, e is zero, d copies, c discards, a is the antipode.
  auto line = [](Semiring ring, long long modulus, long long antipode, std::string name) {
    return Model{std::move(name), ring, modulus, false, {1}, {Matrix{1, 2, {1, 1}}, Matrix{1, 0, {}}, Matrix{2, 1, {1, 1}}, Matrix{0, 1, {}}, Matrix{1, 1, {antipode}}}};
  };
  const Theory hopf_algebras = theory("commutative Hopf algebras", {monoid, comonoid, {commutative, cocommutative}, bialgebra, {hopf}});
  s.require("matrices over ℕ with ⊕: addition and copying on a line are a bialgebra", satisfies(bialgebras, line(Semiring::integer, 0, 1, "a line over ℕ")).holds());
  s.require("matrices over ℤ: with the antipode −1, a Hopf algebra", satisfies(hopf_algebras, line(Semiring::integer, 0, -1, "a line over ℤ")).holds());
  const auto hb = satisfies(hopf_algebras, line(Semiring::boolean, 0, 1, "a line over the Booleans"));
  s.require("matrices over the Booleans: the antipode law fails, 1 + 1 being 1; modulo 2 it holds, 1 + 1 being 0", hb.fails() && hb.reason.find("antipode") != std::string::npos &&
                                                                                                               satisfies(hopf_algebras, line(Semiring::modular, 2, 1, "a line over ℤ/2")).holds(), hb.reason);
  s.require("matrices: the Frobenius law fails for addition and copying", holds_in(B, line(Semiring::integer, 0, 1, "a line"), frobenius.left, frobenius.right).fails());

  // Evaluation.
  const Matrix and_twice = evaluate(B, sets, seq({par({M, x}), M}));
  s.require("evaluate: (x ∧ y) ∧ z is 1 at (1, 1, 1) only", and_twice.rows == 2 && and_twice.cols == 8 && and_twice.at(1, 7) == 1 && and_twice.at(0, 6) == 1 && and_twice.at(1, 6) == 0);
  Model wrong = sets;
  wrong.generators[0] = Matrix{2, 2, {1, 0, 0, 1}};
  s.require("well_formed: a generator given a matrix of the wrong shape is refused and named", well_formed(B, wrong).fails() && well_formed(B, wrong).piece("at") == "m");
  (void)a, (void)A;
  return s.done();
}
