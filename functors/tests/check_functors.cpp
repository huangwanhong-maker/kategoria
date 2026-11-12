// Checks of kategoria/functors: functors, natural transformations, equivalences, comma categories, adjunctions, monads.
//
// - The search for functors against the naive enumeration of every map of arrows, and against closed forms: monotone
//   maps between ordinals, C(m + k − 1, m); homomorphisms between groups (ℤ/4 → ℤ/2: 2; ℤ/2 → S₃: 4; S₃ → S₃: 10).
// - Isomorphisms: the subsets of 2 are the square of the ordinal 2 and their own opposite; ℤ/4 is not ℤ/2 × ℤ/2.
// - Natural transformations: those from the identity of a group to itself are its centre (S₃: 1, ℤ/4: 4, D₄: 2); the
//   category of functors from the ordinal 2 is the comma category of the identity with itself, built another way; the
//   interchange law of the two compositions.
// - Equivalences: the walking isomorphism is equivalent to a point, with the functor back built and verified.
// - Adjunctions: Galois connections between ordinals; the diagonal of a lattice has both adjoints, meet and join, and
//   that of a group none; the adjoints of the functor to a point pick the initial and the terminal object.
// - Monads: a closure operator, its algebras the closed sets; the monad of an adjunction; the identity monad.

#include <kategoria/functors/adjunction.hpp>
#include <kategoria/functors/functor.hpp>

#include <calx/verification/check.hpp>
#include <morphe/algebra/finite_group.hpp>

#include <string>
#include <vector>

using namespace kategoria::finite;
using namespace kategoria::functors;

static Category group_of(const morphe::algebra::FiniteGroup& G) { return group(G.order(), G.table, G.name); }

// Every map of the arrows of C to those of D, each asked whether it is a functor.
static std::uint64_t naive(const Category& C, const Category& D) {
  std::vector<Index> image(C.size(), 0);
  std::uint64_t count = 0;
  while (true) {
    Functor F{"", {}, image};
    for (Index a = 0; a < C.objects.size(); a++) F.objects.push_back(D.dom(image[C.identity[a]]));
    count += verify(C, D, F).holds();
    std::size_t k = 0;
    while (k < image.size() && ++image[k] == D.size()) image[k++] = 0;
    if (k == image.size()) return count;
  }
}

// The functor between thin categories that a monotone map of objects is.
static Functor monotone(const Category& C, const Category& D, const std::vector<Index>& map, std::string name = "F") {
  Functor F{std::move(name), map, {}};
  for (Index f = 0; f < C.size(); f++) F.arrows.push_back(D.hom(map[C.dom(f)], map[C.cod(f)]).at(0));
  return F;
}

int main() {
  calx::verification::Suite s;
  const Category S3 = group_of(morphe::algebra::symmetric(3)), Z2 = group_of(morphe::algebra::cyclic(2)), Z4 = group_of(morphe::algebra::cyclic(4)), Z6 = group_of(morphe::algebra::cyclic(6));
  const Category V4 = group_of(morphe::algebra::direct_product(morphe::algebra::cyclic(2), morphe::algebra::cyclic(2)));
  const Category D4 = group_of(morphe::algebra::dihedral(4));

  // The search.
  const Category sq = product(chain(2), chain(2));
  s.require("search: the functors from the ordinal 3 to the square are those the naive enumeration finds", count_functors(chain(3), sq) == naive(chain(3), sq), std::to_string(count_functors(chain(3), sq)));
  s.require("search: the functors from (ℤ/4, ×) to FinSet up to 2 are those the naive enumeration finds", count_functors(multiplicative(4), finset(2)) == naive(multiplicative(4), finset(2)),
            std::to_string(count_functors(multiplicative(4), finset(2))));
  bool all_verify = true;
  for_each_functor(finset(2), finset(2), [&](const Functor& F) { return all_verify = all_verify && verify(finset(2), finset(2), F).holds(), true; });
  s.require("search: every functor found from FinSet up to 2 to itself verifies", all_verify);
  s.require("monotone maps between ordinals: C(m + k − 1, m): 6 from 2 to 3, 10 from 3 to 3, 35 from 4 to 4",
            count_functors(chain(2), chain(3)) == 6 && count_functors(chain(3), chain(3)) == 10 && count_functors(chain(4), chain(4)) == 35);
  s.require("homomorphisms of groups: ℤ/4 → ℤ/2: 2; S₃ → ℤ/2: 2; ℤ/2 → S₃: 4; ℤ/6 → ℤ/4: 2; S₃ → S₃: 10",
            count_functors(Z4, Z2) == 2 && count_functors(S3, Z2) == 2 && count_functors(Z2, S3) == 4 && count_functors(Z6, Z4) == 2 && count_functors(S3, S3) == 10);
  s.require("functors from a discrete category on 2 are the pairs of objects: 9 into FinSet up to 2", count_functors(discrete(2), finset(2)) == 9);
  Options fixed;
  fixed.objects = {none, 2};
  s.require("search: with the image of an object fixed, only the functors through it: 3 monotone maps from 2 to 3 ending at 2", count_functors(chain(2), chain(3), fixed) == 3);

  // verify() names the place.
  Functor wrong = identity(chain(3));
  wrong.arrows[chain(3).arrow("0≤2")] = chain(3).arrow("0≤1");
  const auto v = verify(chain(3), chain(3), wrong);
  s.require("verify: a map that sends 0≤2 elsewhere fails, at a named arrow", v.fails() && !v.piece("at").empty(), v.reason);

  // Isomorphisms.
  s.require("isomorphism: the subsets of 2 are the square of the ordinal 2, and their own opposite", isomorphism(subsets(2), sq).has_value() && isomorphism(subsets(2), opposite(subsets(2))).has_value());
  s.require("isomorphism: ℤ/4 is not ℤ/2 × ℤ/2, though both have 4 arrows", !isomorphism(Z4, V4).has_value());
  s.require("isomorphism: the slice of the ordinal 4 over 2 is the ordinal 3", isomorphism(slice(chain(4), 2).category, chain(3)).has_value());
  s.require("isomorphism: an ordinal is its opposite; FinSet up to 2 is not", isomorphism(chain(4), opposite(chain(4))).has_value() && !isomorphism(finset(2), opposite(finset(2))).has_value());

  // Natural transformations.
  auto centre = [](const Category& G) { return all_transformations(G, G, identity(G), identity(G)).size(); };
  s.require("the natural transformations 1 ⇒ 1 of a group are its centre: S₃ 1, ℤ/4 4, D₄ 2", centre(S3) == 1 && centre(Z4) == 4 && centre(D4) == 2);
  Transformation skew = identity_transformation(S3, S3, identity(S3));
  skew.components[0] = 1;
  const auto nv = natural(S3, S3, identity(S3), identity(S3), skew);
  s.require("natural: an element outside the centre is not natural, and the square that fails is named", nv.fails() && !nv.piece("at").empty(), nv.reason);
  const FunctorCategory arrows = functor_category(chain(2), chain(3));
  const Comma squares = comma(chain(3), chain(3), chain(3), identity(chain(3)), identity(chain(3)));
  s.require("[2, C] is the comma category (1 ↓ 1): for the ordinal 3, 6 objects, and the two are isomorphic",
            arrows.category.objects.size() == 6 && validate(arrows.category).holds() && validate(squares.category).holds() && isomorphism(arrows.category, squares.category).has_value(),
            std::to_string(arrows.category.size()) + " and " + std::to_string(squares.category.size()) + " arrows");
  const FunctorCategory pairs = functor_category(discrete(2), chain(3));
  s.require("[the discrete 2, C] is C × C", isomorphism(pairs.category, product(chain(3), chain(3))).has_value());
  const FunctorCategory ends = functor_category(Z2, S3);
  s.require("[ℤ/2, S₃]: 4 functors in 2 classes of isomorphic ones (the trivial one, and the three transpositions conjugate)",
            ends.functors.size() == 4 && validate(ends.category).holds() && isomorphism_classes(ends.category) == std::vector<Index>{0, 1, 1, 1},
            std::to_string(ends.category.size()) + " arrows");
  // The interchange law, (s′ · s) ∗ (t′ · t) = (s′ ∗ t′) · (s ∗ t), over the endofunctors of S₃.
  const auto endo = all_functors(S3, S3);
  std::size_t tried = 0, kept = 0;
  for (auto& F : endo)
    for (auto& G : endo)
      for (auto& H : endo)
        for (auto& t : all_transformations(S3, S3, F, G))
          for (auto& t2 : all_transformations(S3, S3, G, H))
            for (std::size_t p = 0; p < 4; p++)
              for (std::size_t q = 0; q < 4; q++)
                for (std::size_t r = 0; r < 4; r++)
                  for (auto& u : all_transformations(S3, S3, endo[p], endo[q]))
                    for (auto& u2 : all_transformations(S3, S3, endo[q], endo[r])) {
                      tried++;
                      kept += horizontal(S3, H, endo[p], vertical(S3, u2, u), vertical(S3, t2, t)).components ==
                              vertical(S3, horizontal(S3, H, endo[q], u2, t2), horizontal(S3, G, endo[p], u, t)).components;
                    }
  s.require("the interchange law holds at every instance over the endofunctors of S₃", tried > 100 && kept == tried, std::to_string(kept) + " of " + std::to_string(tried));

  // What a functor keeps.
  const Functor inclusion = monotone(chain(2), chain(3), {0, 2});
  s.require("the inclusion of the ordinal 2 in 3 at 0 and 2: faithful and full, not essentially surjective",
            faithful(chain(2), chain(3), inclusion).holds() && full(chain(2), chain(3), inclusion).holds() && essentially_surjective(chain(2), chain(3), inclusion).fails());
  Functor sign;
  for_each_functor(S3, Z2, [&](const Functor& F) { return sign = F, F.arrows[1] == 0 && F.arrows[2] == 0 && F.arrows[3] == 0 && F.arrows[4] == 0 && F.arrows[5] == 0; });
  const auto unfaithful = faithful(S3, Z2, sign);
  s.require("the sign of S₃: full, not faithful, and two arrows it identifies are named", full(S3, Z2, sign).holds() && unfaithful.fails() && !unfaithful.piece("at").empty());

  // Equivalences.
  const Category iso = preorder({"a", "b"}, {{1, 1}, {1, 1}}, "the walking isomorphism"), point = discrete(1);
  const Equivalence E = equivalence(iso, point, constant(iso, point, 0));
  s.require("the walking isomorphism is equivalent to a point: the functor back and its natural isomorphisms are built and verify",
            E.verdict.holds() && verify(point, iso, E.inverse).holds() && natural(iso, iso, identity(iso), compose(E.inverse, constant(iso, point, 0)), E.unit).holds(), E.verdict.reason);
  const Category thick = product(iso, Z2);
  Functor second{"the projection", std::vector<Index>(thick.objects.size(), 0), {}};
  for (Index f = 0; f < thick.size(); f++) second.arrows.push_back(f % static_cast<Index>(Z2.size()));
  s.require("the walking isomorphism times ℤ/2 is equivalent to ℤ/2 by the projection", equivalence(thick, Z2, second).verdict.holds());
  s.require("equivalent: by skeletons; the ordinal 2 is not equivalent to the discrete 2, nor ℤ/4 to ℤ/2 × ℤ/2", equivalent(thick, Z2).holds() && equivalent(chain(2), discrete(2)).fails() && equivalent(Z4, V4).fails());
  const Equivalence not_one = equivalence(chain(2), chain(3), inclusion);
  s.require("equivalence: the inclusion of the ordinal 2 in 3 is none, and why is said", not_one.verdict.fails() && not_one.verdict.reason.find("essentially surjective") != std::string::npos, not_one.verdict.reason);

  // Comma categories.
  const Category F2 = finset(2);
  const Comma under = comma(point, F2, F2, constant(point, F2, F2.object("2")), identity(F2));
  s.require("the comma category (c ↓ 1) is the coslice under c: for 2 in FinSet up to 2", isomorphism(under.category, coslice(F2, F2.object("2")).category).has_value() && verify(under.category, F2, under.second).holds());

  // Adjunctions.
  const Category c2 = chain(2), c4 = chain(4);
  const Functor in = monotone(c2, c4, {0, 2}, "i");
  const FoundAdjunction right = right_adjoint(c2, c4, in), left = left_adjoint(c4, c2, in);
  s.require("Galois: the inclusion of {0, 2} in the ordinal 4 has a right adjoint, the greatest below: 0, 0, 1, 1", right.adjunction && right.adjunction->right.objects == std::vector<Index>{0, 0, 1, 1} && right.verdict.holds(), right.verdict.reason);
  s.require("Galois: it has no left adjoint, and 3, which nothing lies above, is named", !left.adjunction && left.verdict.fails() && left.verdict.piece("at") == "3", left.verdict.reason);
  const Category L = divisors(12), LL = product(L, L);
  Functor diagonal{"Δ", {}, {}};
  for (Index a = 0; a < L.objects.size(); a++) diagonal.objects.push_back(a * static_cast<Index>(L.objects.size()) + a);
  for (Index f = 0; f < L.size(); f++) diagonal.arrows.push_back(f * static_cast<Index>(L.size()) + f);
  const FoundAdjunction meet = right_adjoint(L, LL, diagonal), join = left_adjoint(LL, L, diagonal);
  const Index four = L.object("4"), six = L.object("6");
  s.require("the diagonal of the divisors of 12 has a right adjoint, the greatest common divisor: (4, 6) ↦ 2",
            meet.adjunction && L.objects[meet.adjunction->right.objects[four * L.objects.size() + six]] == "2" && verify_adjunction(L, LL, *meet.adjunction).holds());
  s.require("and a left adjoint, the least common multiple: (4, 6) ↦ 12", join.adjunction && L.objects[join.adjunction->left.objects[four * L.objects.size() + six]] == "12" && verify_adjunction(LL, L, *join.adjunction).holds());
  const Category ZZ = product(Z2, Z2);
  Functor group_diagonal{"Δ", {0}, {}};
  for (Index f = 0; f < Z2.size(); f++) group_diagonal.arrows.push_back(f * static_cast<Index>(Z2.size()) + f);
  s.require("the diagonal of ℤ/2 has neither adjoint", !right_adjoint(Z2, ZZ, group_diagonal).adjunction && !left_adjoint(ZZ, Z2, group_diagonal).adjunction);
  const Functor bang = constant(F2, point, 0);
  const FoundAdjunction initial = left_adjoint(point, F2, bang), terminal = right_adjoint(F2, point, bang);
  s.require("the functor to a point: its left adjoint picks the initial object, its right the terminal",
            initial.adjunction && F2.objects[initial.adjunction->left.objects[0]] == "0" && terminal.adjunction && F2.objects[terminal.adjunction->right.objects[0]] == "1");
  Adjunction spoiled = *right.adjunction;
  spoiled.right = monotone(c4, c2, {0, 1, 1, 1});
  const auto sv = verify_adjunction(c2, c4, spoiled);
  s.require("verify_adjunction: another monotone map in the adjoint's place does not verify", !sv.holds(), sv.reason);

  // Monads.
  const Category P = subsets(3);
  std::vector<Index> with_a;
  for (Index k = 0; k < P.objects.size(); k++) with_a.push_back(k | 1);
  Monad closure{monotone(P, P, with_a, "T"), {"η", {}}, {"μ", {}}};
  for (Index k = 0; k < P.objects.size(); k++) closure.unit.components.push_back(P.hom(k, k | 1).at(0)), closure.mult.components.push_back(P.identity[k | 1]);
  const Algebras closed = eilenberg_moore(P, closure);
  s.require("a closure operator on the subsets of 3 (adding a) is a monad", verify_monad(P, closure).holds());
  s.require("its algebras are the 4 closed sets, a copy of the subsets of 2", closed.algebras.size() == 4 && isomorphism(closed.category, subsets(2)).has_value() && verify(closed.category, P, closed.forgetful).holds());
  const Kleisli free = kleisli(P, closure);
  s.require("its Kleisli category is a preorder on the 8 subsets, equivalent to its algebras", validate(free.category).holds() && is_thin(free.category) && equivalent(free.category, closed.category).holds() && verify(P, free.category, free.free).holds());
  const Monad galois = monad_of(*right.adjunction);
  s.require("the monad of an adjunction is a monad: for the Galois connection, and for the meet of the divisors of 12", verify_monad(c2, galois).holds() && verify_monad(L, monad_of(*meet.adjunction)).holds());
  s.require("the identity monad: its algebras and its Kleisli category are the category", isomorphism(eilenberg_moore(F2, identity_monad(F2)).category, F2).has_value() && isomorphism(kleisli(F2, identity_monad(F2)).category, F2).has_value());
  Monad no_unit = closure;
  no_unit.unit.components[0] = P.identity[0];
  s.require("verify_monad: a unit that is not natural into T is refused", !verify_monad(P, no_unit).holds());
  return s.done();
}
