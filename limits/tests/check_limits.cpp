// Checks of kategoria/limits: cones, limits and colimits, completeness, preservation, exponentials.
//
// - In a lattice, products are meets and coproducts joins: minimum and maximum in an ordinal, the greatest common
//   divisor and least common multiple among the divisors of 12, intersection and union among subsets.
// - In FinSet up to 2: 1 × 2 = 2 and 1 + 1 = 2 exist, 2 × 2 does not (it has 4 elements); the equalizer of two
//   different points of 2 is empty; terminal 1, initial ∅.
// - A cone that is not universal is refused with the cone that does not factor through it.
// - Finite completeness: lattices have every finite limit and colimit; FinSet up to 2 and a group do not, and the
//   first diagram without a limit is named.
// - Right adjoints keep limits (Mac Lane 1971, V.5, Theorem 1): at every product, for a Galois connection.
// - Cartesian closed: Boolean algebras, ordinals and the divisors of 12 (finite distributive lattices are Heyting
//   algebras), with b^a = ¬a ∪ b among subsets; the diamond M₃ and the pentagon N₅ are not distributive, and are not.

#include <kategoria/functors/adjunction.hpp>
#include <kategoria/limits/limits.hpp>

#include <calx/verification/check.hpp>
#include <morphe/algebra/finite_group.hpp>

#include <string>
#include <vector>

using namespace kategoria::finite;
using namespace kategoria::limits;

static kategoria::functors::Functor monotone(const Category& C, const Category& D, const std::vector<Index>& map, std::string name = "F") {
  kategoria::functors::Functor F{std::move(name), map, {}};
  for (Index f = 0; f < C.size(); f++) F.arrows.push_back(D.hom(map[C.dom(f)], map[C.cod(f)]).at(0));
  return F;
}

int main() {
  calx::verification::Suite s;
  auto apex = [](const Category& C, const Limit& L) { return L.cone ? C.objects[L.cone->apex] : std::string("none"); };

  const Category c4 = chain(4), D12 = divisors(12), P3 = subsets(3), F2 = finset(2);
  s.require("the ordinal 4: 1 × 2 = 1, 1 + 2 = 2, terminal 3, initial 0", apex(c4, product(c4, 1, 2)) == "1" && apex(c4, coproduct(c4, 1, 2)) == "2" && apex(c4, terminal(c4)) == "3" && apex(c4, initial(c4)) == "0");
  s.require("the divisors of 12: 4 × 6 = 2 and 4 + 6 = 12", apex(D12, product(D12, D12.object("4"), D12.object("6"))) == "2" && apex(D12, coproduct(D12, D12.object("4"), D12.object("6"))) == "12");
  s.require("the subsets of 3: the pullback of ab ⊆ abc ⊇ ac is a; the pushout of ab ⊇ a ⊆ ac is abc",
            apex(P3, pullback(P3, P3.arrow("ab≤abc"), P3.arrow("ac≤abc"))) == "a" && apex(P3, pushout(P3, P3.arrow("a≤ab"), P3.arrow("a≤ac"))) == "abc");
  const Index zero = F2.object("0"), one = F2.object("1"), two = F2.object("2");
  s.require("FinSet up to 2: 1 × 2 = 2, 1 + 1 = 2, terminal 1, initial ∅", apex(F2, product(F2, one, two)) == "2" && apex(F2, coproduct(F2, one, one)) == "2" && apex(F2, terminal(F2)) == "1" && apex(F2, initial(F2)) == "0");
  const Limit four = product(F2, two, two);
  s.require("FinSet up to 2: 2 × 2 does not exist, and no cone is said to be universal", !four.cone && four.verdict.fails(), four.verdict.reason);
  s.require("FinSet up to 2: the equalizer of the two points of 2 is ∅; of a point with itself, 1",
            apex(F2, equalizer(F2, F2.arrow("[1→2|0]"), F2.arrow("[1→2|1]"))) == "0" && apex(F2, equalizer(F2, F2.arrow("[1→2|0]"), F2.arrow("[1→2|0]"))) == "1");
  s.require("FinSet up to 2: the coequalizer of the two points of 2 is 1", apex(F2, coequalizer(F2, F2.arrow("[1→2|0]"), F2.arrow("[1→2|1]"))) == "1");
  (void)zero;

  // A cone that is not universal.
  const Diagram pair = discrete_diagram(c4, {1, 2});
  const Cone low{0, {c4.arrow("0≤1"), c4.arrow("0≤2")}}, right{1, {c4.identity[1], c4.arrow("1≤2")}};
  const auto refused = is_limit(c4, pair.shape, pair.functor, low);
  s.require("is_limit: 0 over 1 and 2 is a cone and no limit; the cone from 1, which does not factor through it, is named",
            verify_cone(c4, pair.shape, pair.functor, low).holds() && refused.fails() && refused.piece("at").find("1") == 0, refused.reason);
  s.require("is_limit: 1 is the limit, each of the 2 cones factoring once", is_limit(c4, pair.shape, pair.functor, right).holds() && is_limit(c4, pair.shape, pair.functor, right).examined == 2);
  const Cone crooked{1, {c4.identity[1], c4.identity[1]}};
  s.require("verify_cone: a leg that does not reach its object is refused", verify_cone(c4, pair.shape, pair.functor, crooked).fails());
  s.require("is_colimit: 2 under 1 and 2 is the colimit, 3 is not", is_colimit(c4, pair.shape, pair.functor, {2, {c4.arrow("1≤2"), c4.identity[2]}}).holds() && is_colimit(c4, pair.shape, pair.functor, {3, {c4.arrow("1≤3"), c4.arrow("2≤3")}}).fails());

  // Completeness.
  s.require("finite limits and colimits: the ordinal 4, the subsets of 3 and the divisors of 12 have them all",
            finitely_complete(c4).holds() && finitely_cocomplete(c4).holds() && finitely_complete(P3).holds() && finitely_cocomplete(P3).holds() && finitely_complete(D12).holds());
  const auto no_products = finitely_complete(F2);
  s.require("finite limits: FinSet up to 2 lacks one, and 2 × 2 is named", no_products.fails() && no_products.piece("at") == "2, 2", no_products.reason);
  const Category Z3 = group(3, morphe::algebra::cyclic(3).table, "ℤ/3");
  s.require("finite limits: a group has no terminal object", finitely_complete(Z3).fails() && finitely_complete(Z3).reason.find("terminal") != std::string::npos);
  s.require("finite colimits: a group has no initial object, and that is the word used", finitely_cocomplete(Z3).reason.find("initial") != std::string::npos, finitely_cocomplete(Z3).reason);
  s.require("finite limits: a point has them all; the discrete 2 has none", finitely_complete(discrete(1)).holds() && finitely_complete(discrete(2)).fails());

  // What functors keep.
  const Category c2 = chain(2);
  const auto in = monotone(c2, c4, {0, 2}, "i");
  const auto adj = kategoria::functors::right_adjoint(c2, c4, in);
  bool kept = adj.adjunction.has_value();
  for (Index a = 0; a < 4 && kept; a++)
    for (Index b = 0; b < 4 && kept; b++) {
      const Diagram d = discrete_diagram(c4, {a, b});
      kept = preserves(d.shape, d.functor, *limit(c4, d.shape, d.functor).cone, c2, adj.adjunction->right).holds();
    }
  s.require("a right adjoint keeps limits: every product of the ordinal 4, for the Galois connection onto {0, 2}", kept);
  const Category P2 = subsets(2);
  const auto size = monotone(P2, chain(3), {0, 1, 1, 2}, "the cardinality");
  const Diagram ab = discrete_diagram(P2, {1, 2});
  const auto lost = preserves(ab.shape, ab.functor, *limit(P2, ab.shape, ab.functor).cone, chain(3), size);
  s.require("the cardinality of subsets does not keep a ∩ b = ∅: its image 0 is not the product of 1 and 1", lost.fails(), lost.reason);

  // Exponentials.
  const Exponential e = exponential(P3, P3.object("ab"), P3.object("c"));
  s.require("the subsets of 3: c^ab = ¬ab ∪ c = c", e.verdict.holds() && P3.objects[e.object] == "c", e.verdict.reason);
  const Exponential e2 = exponential(P3, P3.object("a"), P3.object("b"));
  s.require("the subsets of 3: b^a = ¬a ∪ b = bc", e2.verdict.holds() && P3.objects[e2.object] == "bc");
  s.require("cartesian closed: the subsets of 2, the ordinal 4 and the divisors of 12", cartesian_closed(P2).holds() && cartesian_closed(c4).holds() && cartesian_closed(D12).holds());
  const Category M3 = preorder({"0", "a", "b", "c", "1"}, {{1, 1, 1, 1, 1}, {0, 1, 0, 0, 1}, {0, 0, 1, 0, 1}, {0, 0, 0, 1, 1}, {0, 0, 0, 0, 1}}, "the diamond M₃");
  const Category N5 = preorder({"0", "a", "b", "c", "1"}, {{1, 1, 1, 1, 1}, {0, 1, 1, 0, 1}, {0, 0, 1, 0, 1}, {0, 0, 0, 1, 1}, {0, 0, 0, 0, 1}}, "the pentagon N₅");
  const auto m3 = cartesian_closed(M3), n5 = cartesian_closed(N5);
  s.require("cartesian closed: the diamond and the pentagon are lattices and are not, and the exponential that is missing is named",
            finitely_complete(M3).holds() && finitely_complete(N5).holds() && m3.fails() && n5.fails() && !m3.piece("at").empty(), m3.reason + "; " + n5.reason);
  s.require("cartesian closed: FinSet up to 1 is; FinSet up to 2 is not, lacking 2 × 2", cartesian_closed(finset(1)).holds() && cartesian_closed(F2).fails());
  return s.done();
}
