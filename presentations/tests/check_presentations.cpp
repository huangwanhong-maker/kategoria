// Checks of kategoria/presentations: categories presented by generators and equations, completion, derivations.
//
// - Categories built from presentations, each isomorphic to the category it presents: the free category on a path of
//   two edges (the ordinal 3); the commutative square (the ordinal 2 squared); ℤ/5, S₃ = ⟨s, t | s², t², sts = tst⟩,
//   D₄ = ⟨r, s | r⁴, s², srsr⟩ and Q₈ = ⟨i, j | i⁴, i² = j², iji = j⟩ against morphe's tables; the walking
//   isomorphism; a split idempotent; and Δ up to [2] from its faces and degeneracies with the cosimplicial identities,
//   of 31 arrows.
// - Derivations: (st)³ = 1 in S₃ comes with a derivation by the three equations that check() accepts; a derivation
//   with a step removed, or with a step that does not apply, is refused; s ≠ t is answered with two normal forms,
//   and certify() verifies the confluence that answer rests on.
// - A free monoid completes with no rule and is not finite. The braid monoid ⟨a, b | aba = bab⟩ does not complete
//   within small bounds: equal words are still proved equal, unequal ones are undecided, and said to be.

#include <kategoria/functors/functor.hpp>
#include <kategoria/presentations/presentation.hpp>

#include <calx/verification/check.hpp>
#include <morphe/algebra/finite_group.hpp>

#include <sstream>
#include <string>
#include <vector>

using namespace kategoria::presentations;
using kategoria::finite::Category;

// A path written as its edges' names in the order travelled, or "@A" for the identity of A.
static Path path(const Quiver& Q, const std::string& text) {
  std::istringstream in(text);
  Path p;
  bool first = true;
  for (std::string w; in >> w;) {
    if (w[0] == '@') {
      for (Index a = 0; a < Q.objects.size(); a++)
        if (Q.objects[a] == w.substr(1)) p.source = a;
      continue;
    }
    for (Index e = 0; e < Q.edges.size(); e++)
      if (Q.edges[e].name == w) {
        if (first) p.source = Q.edges[e].dom, first = false;
        p.edges.push_back(e);
      }
  }
  return p;
}
static Presentation make(std::string name, std::vector<std::string> objects, std::vector<Edge> edges, const std::vector<std::pair<std::string, std::string>>& equations) {
  Presentation P{std::move(name), {std::move(objects), std::move(edges)}, {}};
  for (auto& [l, r] : equations) P.equations.push_back({path(P.quiver, l), path(P.quiver, r)});
  return P;
}
static Category group_of(const morphe::algebra::FiniteGroup& G) { return kategoria::finite::group(G.order(), G.table, G.name); }

int main() {
  calx::verification::Suite s;
  auto presents = [&](const std::string& what, const Presentation& P, const Category& expected) {
    const Completion K = complete(P);
    const auto built = category(P, K);
    const bool ok = well_formed(P).holds() && K.complete && built && kategoria::finite::validate(built->category).holds() && built->category.size() == expected.size() &&
                    kategoria::functors::isomorphism(built->category, expected).has_value() && certify(P, K).holds();
    s.require(what + ": " + std::to_string(expected.size()) + " arrows, isomorphic to what it presents, its rules certified", ok,
              built ? std::to_string(built->category.size()) + " arrows, " + std::to_string(K.rules.size()) + " rules" : K.complete ? "not finite" : K.reason);
  };
  using kategoria::finite::chain;
  presents("the free category on • → • → •", make("a path", {"A", "B", "C"}, {{"f", 0, 1}, {"g", 1, 2}}, {}), chain(3));
  presents("the commutative square", make("a square", {"A", "B", "C", "D"}, {{"f", 0, 1}, {"g", 1, 3}, {"h", 0, 2}, {"k", 2, 3}}, {{"f g", "h k"}}), kategoria::finite::product(chain(2), chain(2)));
  presents("ℤ/5 = ⟨a | a⁵⟩", make("ℤ/5", {"∗"}, {{"a", 0, 0}}, {{"a a a a a", "@∗"}}), group_of(morphe::algebra::cyclic(5)));
  const Presentation S3 = make("S₃", {"∗"}, {{"s", 0, 0}, {"t", 0, 0}}, {{"s s", "@∗"}, {"t t", "@∗"}, {"s t s", "t s t"}});
  presents("S₃ = ⟨s, t | s², t², sts = tst⟩", S3, group_of(morphe::algebra::symmetric(3)));
  presents("D₄ = ⟨r, s | r⁴, s², srsr⟩", make("D₄", {"∗"}, {{"r", 0, 0}, {"s", 0, 0}}, {{"r r r r", "@∗"}, {"s s", "@∗"}, {"s r s r", "@∗"}}), group_of(morphe::algebra::dihedral(4)));
  presents("Q₈ = ⟨i, j | i⁴, i² = j², iji = j⟩", make("Q₈", {"∗"}, {{"i", 0, 0}, {"j", 0, 0}}, {{"i i i i", "@∗"}, {"i i", "j j"}, {"i j i", "j"}}), group_of(morphe::algebra::quaternion()));
  presents("the walking isomorphism", make("an isomorphism", {"A", "B"}, {{"f", 0, 1}, {"g", 1, 0}}, {{"f g", "@A"}, {"g f", "@B"}}), kategoria::finite::preorder({"a", "b"}, {{1, 1}, {1, 1}}));
  presents("Δ up to [2] from faces and degeneracies",
           make("Δ≤2", {"[0]", "[1]", "[2]"}, {{"d0", 0, 1}, {"d1", 0, 1}, {"s0", 1, 0}, {"e0", 1, 2}, {"e1", 1, 2}, {"e2", 1, 2}, {"t0", 2, 1}, {"t1", 2, 1}},
                {{"d0 e1", "d0 e0"}, {"d0 e2", "d1 e0"}, {"d1 e2", "d1 e1"}, {"d0 s0", "@[0]"}, {"d1 s0", "@[0]"}, {"e0 t0", "@[1]"}, {"e1 t0", "@[1]"}, {"e1 t1", "@[1]"}, {"e2 t1", "@[1]"},
                 {"e0 t1", "s0 d0"}, {"e2 t0", "s0 d1"}, {"t0 s0", "t1 s0"}}),
           kategoria::finite::simplex(2));

  // Small monoids and idempotents, by their counts.
  auto arrows = [](const Presentation& P) {
    const auto built = category(P, complete(P));
    return built ? built->category.size() : std::size_t{0};
  };
  const Presentation cube = make("⟨a | a³ = a⟩", {"∗"}, {{"a", 0, 0}}, {{"a a a", "a"}});
  s.require("the monoid ⟨a | a³ = a⟩ has 3 arrows and is no group", arrows(cube) == 3 && !kategoria::finite::is_groupoid(category(cube, complete(cube))->category));
  s.require("an idempotent has 2 arrows; split by r ∘ s = 1, 5 arrows, s ∘ r the idempotent",
            arrows(make("an idempotent", {"A"}, {{"e", 0, 0}}, {{"e e", "e"}})) == 2 && arrows(make("a retract", {"A", "B"}, {{"r", 0, 1}, {"s", 1, 0}}, {{"s r", "@B"}})) == 5);

  // Derivations.
  const Completion K = complete(S3);
  const Path ststst = path(S3.quiver, "s t s t s t"), one = path(S3.quiver, "@∗");
  const Proof cubed = prove(S3, K, ststst, one);
  s.require("(st)³ = 1 in S₃: proved, by a derivation that uses the three equations only and that check() accepts", cubed.verdict.holds() && !cubed.derivation.empty() && check(S3, ststst, one, cubed.derivation).holds(),
            cubed.verdict.reason);
  const auto passed = trace(S3, ststst, cubed.derivation);
  s.require("trace: the derivation passes through one path more than it has steps, from the first to the last, never twice through one",
            passed.size() == cubed.derivation.size() + 1 && passed.front() == ststst && passed.back() == one && shortened(S3, ststst, cubed.derivation).size() == cubed.derivation.size());
  Derivation cut = cubed.derivation;
  cut.pop_back();
  Derivation stray = cubed.derivation;
  stray[0].at = 5;
  s.require("check: the derivation with its last step removed, or with a step moved to where it does not apply, is refused",
            check(S3, ststst, one, cut).fails() && check(S3, ststst, one, stray).fails() && !check(S3, ststst, one, stray).piece("at").empty());
  Derivation detour = cubed.derivation;
  detour.insert(detour.begin(), {Step{0, 0, false}, Step{0, 0, true}});  // insert s s at the front, and remove it
  s.require("shortened: a detour that returns to the same path is dropped, and what is left still checks", check(S3, ststst, one, detour).holds() && shortened(S3, ststst, detour).size() == cubed.derivation.size());
  const Proof apart = prove(S3, K, path(S3.quiver, "s"), path(S3.quiver, "t"));
  s.require("s ≠ t in S₃: answered with two normal forms", apart.verdict.fails() && apart.verdict.piece("left") == "s" && apart.verdict.piece("right") == "t", apart.verdict.reason);
  const Proof conj = prove(S3, K, path(S3.quiver, "s t s"), path(S3.quiver, "t s t"));
  s.require("sts = tst: one step, the equation itself", conj.verdict.holds() && conj.derivation.size() == 1);
  s.require("prove: two paths that are not parallel are refused", prove(make("a path", {"A", "B", "C"}, {{"f", 0, 1}, {"g", 1, 2}}, {}), {}, {0, {0}}, {1, {1}}).verdict.fails());
  Completion spoiled = K;
  spoiled.rules.erase(spoiled.rules.begin());  // s s → 1, which nothing else replaces
  s.require("certify: the rules with the first removed no longer join the sides of an equation, and are refused", !certify(S3, spoiled).holds());
  bool every_rule = true;
  for (auto& r : K.rules) every_rule = every_rule && check(S3, r.left, r.right, r.why).holds();
  s.require("every rule of the completion carries a derivation from the equations that checks", every_rule && K.rules.size() >= 3, std::to_string(K.rules.size()) + " rules, " + std::to_string(K.pairs) + " critical pairs");

  // Not finite, and not complete.
  const Presentation free = make("a free monoid", {"∗"}, {{"a", 0, 0}, {"b", 0, 0}}, {});
  s.require("a free monoid completes with no rule, and its arrows are not finitely many", complete(free).complete && complete(free).rules.empty() && !category(free, complete(free)).has_value());
  const Presentation braid = make("the braid monoid", {"∗"}, {{"a", 0, 0}, {"b", 0, 0}}, {{"a b a", "b a b"}});
  Bounds few;
  few.rules = 12;
  const Completion B = complete(braid, few);
  const Proof equal = prove(braid, B, path(braid.quiver, "b a b a b"), path(braid.quiver, "b a a b a")), open = prove(braid, B, path(braid.quiver, "a"), path(braid.quiver, "b"));
  s.require("the braid monoid does not complete within 12 rules, and says so", !B.complete && !B.reason.empty() && certify(braid, B).status == kategoria::kernel::Status::undecided, B.reason);
  s.require("there, babab = baaba is still proved, with a derivation that checks; a ≠ b is undecided", equal.verdict.holds() && check(braid, path(braid.quiver, "b a b a b"), path(braid.quiver, "b a a b a"), equal.derivation).holds() &&
                                                                                                    open.verdict.status == kategoria::kernel::Status::undecided, equal.verdict.reason + "; " + open.verdict.reason);
  s.require("well_formed: an equation between paths that are not parallel is refused", well_formed(make("wrong", {"A", "B"}, {{"f", 0, 1}}, {{"f", "@A"}})).fails());
  return s.done();
}
