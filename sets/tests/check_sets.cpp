// Checks of kategoria/sets: set-valued functors, the Yoneda lemma, elements, Kan extensions, the classifier of subobjects.
//
// - Representables are functors, and the Yoneda lemma holds at every object of several categories and functors.
// - A group as a category: its set-valued functors are its actions. Sections are fixed points and classes orbits
//   (Burnside's count); equivariant maps out of the regular action are the elements of the target.
// - The category of elements of Hom(a, −) is the coslice under a.
// - Kan extensions: along the functor to a point, the left is the colimit and the right the limit; the left extension
//   of Hom(c, −) along K is Hom(K c, −); along the inclusion of a subgroup they are induction and coinduction, of
//   |G|/|H| and |X|^(|G|/|H|) elements; and each is universal against every functor tried (Σ ⊣ Δ ⊣ Π).
// - The classifier: 2 truth values over a point and over a group, 3 and 2 over the ordinal 2, n + 1 at the bottom of
//   the ordinal n, 3 over the monoid with one idempotent; it classifies the subfunctors of every functor tried; and
//   the subfunctors form a Heyting algebra, cartesian closed as a category.

#include <kategoria/limits/limits.hpp>
#include <kategoria/sets/copresheaf.hpp>

#include <calx/verification/check.hpp>
#include <morphe/algebra/finite_group.hpp>

#include <string>
#include <vector>

using namespace kategoria::finite;
using namespace kategoria::sets;
using kategoria::functors::Functor;

static Category group_of(const morphe::algebra::FiniteGroup& G) { return group(G.order(), G.table, G.name); }

// The action of ℤ/n on n·k points in k cycles of length n: element g adds g to the first coordinate.
static Copresheaf cycles(std::size_t n, std::size_t k, std::string name) {
  Copresheaf X{std::move(name), {{}}, {}};
  for (std::size_t x = 0; x < n * k; x++) X.elements[0].push_back(std::to_string(x));
  for (std::size_t g = 0; g < n; g++) {
    Function f;
    for (std::size_t x = 0; x < n * k; x++) f.push_back(static_cast<Index>((x / n) * n + (x % n + g) % n));
    X.action.push_back(f);
  }
  return X;
}

int main() {
  calx::verification::Suite s;
  const Category F2 = finset(2), D1 = simplex(1), c3 = chain(3), point = discrete(1);
  const Category Z4 = group_of(morphe::algebra::cyclic(4)), Z2 = group_of(morphe::algebra::cyclic(2)), S3 = group_of(morphe::algebra::symmetric(3));

  // Representables and Yoneda.
  bool functors = true, yon = true;
  std::size_t tried = 0;
  for (const Category* C : {&F2, &D1, &c3, &S3})
    for (Index a = 0; a < C->objects.size(); a++) {
      const Copresheaf H = representable(*C, a);
      functors = functors && verify(*C, H).holds();
      for (Index b = 0; b < C->objects.size(); b++) yon = yon && yoneda(*C, representable(*C, b), a).holds(), tried++;
      yon = yon && yoneda(*C, constant(*C, 3), a).holds();
    }
  s.require("representables are functors, on FinSet up to 2, Δ up to [1], the ordinal 3 and S₃", functors);
  s.require("the Yoneda lemma holds at every object, for every representable and for a constant functor", yon, std::to_string(tried) + " pairs");
  Copresheaf torn = constant(c3, 2);
  torn.action[c3.arrow("0≤2")] = {1, 0};  // 0≤1 and 1≤2 act as the identity, their composite does not
  const auto tv = verify(c3, torn);
  s.require("verify: a functor that does not keep a composite is refused at named arrows", tv.fails() && !tv.piece("at").empty(), tv.reason);

  // Actions of a group.
  const Copresheaf regular = representable(Z4, 0), two_cycles = cycles(4, 2, "two cycles"), three_points = constant(Z4, 3);
  s.require("ℤ/4: two cycles of 4 points are a functor with no fixed point and 2 orbits; 3 fixed points have 3 sections and 3 classes",
            verify(Z4, two_cycles).holds() && sections(Z4, two_cycles).empty() && classes(Z4, two_cycles).count == 2 && sections(Z4, three_points).size() == 3 && classes(Z4, three_points).count == 3);
  s.require("equivariant maps: from the regular action to X there are |X|; from two cycles to the regular action 4² = 16; from fixed points to it none",
            count_transformations(Z4, regular, two_cycles) == 8 && count_transformations(Z4, two_cycles, regular) == 16 && count_transformations(Z4, three_points, regular) == 0);
  s.require("isomorphism: two cycles are two copies of the regular action, not eight fixed points", !isomorphism(Z4, two_cycles, constant(Z4, 8)).has_value() && isomorphism(Z4, cycles(4, 1, "one cycle"), regular).has_value());

  // Elements.
  const Index two = F2.object("2");
  const Elements E = elements(F2, representable(F2, two));
  s.require("the category of elements of Hom(2, −) is the coslice under 2", validate(E.category).holds() && kategoria::functors::isomorphism(E.category, coslice(F2, two).category).has_value() &&
                                                                               kategoria::functors::verify(E.category, F2, E.projection).holds());
  s.require("a representable has one class: its category of elements has an initial object (here two isomorphic ones, the identity and the swap of 2)",
            classes(F2, representable(F2, two)).count == 1 && initial_objects(E.category).size() == 2);

  // Kan extensions along the functor to a point.
  const Functor bang = kategoria::functors::constant(Z4, point, 0);
  const Kan lan = left_kan(Z4, point, bang, two_cycles), ran = right_kan(Z4, point, bang, three_points);
  s.require("along the functor to a point: the left extension is the colimit (2 orbits), the right the limit (3 fixed points)", lan.extension.size(0) == 2 && ran.extension.size(0) == 3 && verify(point, lan.extension).holds());
  // Of a representable.
  const Functor in = [&] {
    Functor F{"i", {0, 2}, {}};
    for (Index f = 0; f < chain(2).size(); f++) F.arrows.push_back(chain(4).hom(F.objects[chain(2).dom(f)], F.objects[chain(2).cod(f)]).at(0));
    return F;
  }();
  const Category c2 = chain(2), c4 = chain(4);
  bool rep = true;
  for (Index a = 0; a < 2; a++) rep = rep && isomorphism(c4, left_kan(c2, c4, in, representable(c2, a)).extension, representable(c4, in.objects[a])).has_value();
  s.require("the left extension of Hom(c, −) along K is Hom(K c, −): for the inclusion of {0, 2} in the ordinal 4", rep);
  // Induction and coinduction along a subgroup.
  Functor sub;
  kategoria::functors::Options injective;
  injective.injective = true;
  kategoria::functors::for_each_functor(Z2, Z4, [&](const Functor& F) { return sub = F, false; }, injective);
  sub.name = "the inclusion";
  const Copresheaf fixed = constant(Z2, 1), flip = representable(Z2, 0);
  const Kan induced = left_kan(Z2, Z4, sub, fixed), coinduced = right_kan(Z2, Z4, sub, flip), coinduced_point = right_kan(Z2, Z4, sub, fixed);
  s.require("ℤ/2 in ℤ/4: inducing a fixed point gives the 2 cosets; coinducing it gives 1 point; coinducing the regular action gives 2² = 4 points",
            induced.extension.size(0) == 2 && coinduced_point.extension.size(0) == 1 && coinduced.extension.size(0) == 4 && verify(Z4, induced.extension).holds() && verify(Z4, coinduced.extension).holds(),
            std::to_string(induced.extension.size(0)) + ", " + std::to_string(coinduced_point.extension.size(0)) + ", " + std::to_string(coinduced.extension.size(0)));
  s.require("inducing the regular action of ℤ/2 gives that of ℤ/4", isomorphism(Z4, left_kan(Z2, Z4, sub, flip).extension, regular).has_value());
  bool universal = true;
  std::size_t against = 0;
  for (const Copresheaf& Y : {regular, two_cycles, three_points, cycles(4, 1, "one cycle")}) {
    universal = universal && left_kan_universal(Z2, Z4, sub, fixed, induced, Y).holds() && left_kan_universal(Z2, Z4, sub, flip, left_kan(Z2, Z4, sub, flip), Y).holds() &&
                right_kan_universal(Z2, Z4, sub, flip, coinduced, Y).holds() && right_kan_universal(Z2, Z4, sub, fixed, coinduced_point, Y).holds();
    against++;
  }
  s.require("both extensions along ℤ/2 in ℤ/4 are universal against each of 4 actions of ℤ/4 (Σ ⊣ Δ ⊣ Π)", universal, std::to_string(against));
  // Along a functor between categories with several objects.
  const Copresheaf X = [&] {  // on the ordinal 2: two elements at 0 sent to one of two at 1
    Copresheaf X{"X", {{"p", "q"}, {"r", "s"}}, {{0, 1}, {0, 1}, {0, 0}}};
    return X;
  }();
  const Kan L = left_kan(c2, c4, in, X), R = right_kan(c2, c4, in, X);
  bool both = verify(c2, X).holds() && verify(c4, L.extension).holds() && verify(c4, R.extension).holds();
  for (Index a = 0; a < 4; a++) both = both && left_kan_universal(c2, c4, in, X, L, representable(c4, a)).holds() && right_kan_universal(c2, c4, in, X, R, representable(c4, a)).holds();
  const Classifier omega4 = classifier(c4);
  both = both && left_kan_universal(c2, c4, in, X, L, omega4.omega).holds() && right_kan_universal(c2, c4, in, X, R, omega4.omega).holds();
  s.require("along the inclusion of {0, 2} in the ordinal 4: the left extension has 2, 2, 2, 2 elements, the right 2, 2, 2, 1, and both are universal",
            both && L.extension.size(0) == 2 && L.extension.size(1) == 2 && L.extension.size(2) == 2 && L.extension.size(3) == 2 && R.extension.size(0) == 2 && R.extension.size(1) == 2 && R.extension.size(2) == 2 && R.extension.size(3) == 1,
            std::to_string(L.extension.size(0)) + std::to_string(L.extension.size(1)) + std::to_string(L.extension.size(2)) + std::to_string(L.extension.size(3)) + " and " + std::to_string(R.extension.size(0)) +
                std::to_string(R.extension.size(1)) + std::to_string(R.extension.size(2)) + std::to_string(R.extension.size(3)));
  s.require("pullback: restricting the left extension along K gives X back here, through an invertible unit", isomorphism(c2, X, pullback(in, L.extension)).has_value() && bijective(L.comparison[0], 2) && bijective(L.comparison[1], 2));

  // The classifier.
  const Category M2 = multiplicative(2);
  s.require("truth values: 2 over a point and over S₃; 3 and 2 over the ordinal 2; 5, 4, 3, 2 over the ordinal 4; 3 over the monoid with an idempotent",
            classifier(point).omega.size(0) == 2 && classifier(S3).omega.size(0) == 2 && classifier(c2).omega.size(0) == 3 && classifier(c2).omega.size(1) == 2 && omega4.omega.size(0) == 5 && omega4.omega.size(1) == 4 &&
                omega4.omega.size(2) == 3 && omega4.omega.size(3) == 2 && classifier(M2).omega.size(0) == 3);
  bool omega_functor = true, classified = true;
  std::size_t count = 0;
  for (const Category* C : {&c2, &c3, &D1, &M2, &Z2, &F2}) {
    const Classifier K = classifier(*C);
    omega_functor = omega_functor && verify(*C, K.omega).holds();
    for (Index a = 0; a < C->objects.size(); a++) classified = classified && classifies(*C, representable(*C, a), K).holds(), count++;
    classified = classified && classifies(*C, constant(*C, 2), K).holds();
  }
  s.require("Ω is a functor on each of six categories", omega_functor);
  s.require("Ω classifies: the subfunctors of every representable and of the constant 2 are the transformations to Ω, one to one", classified, std::to_string(count) + " representables");
  s.require("subfunctors: the constant 2 on the ordinal 2 has 9 (a subset at 0 inside a subset at 1); two cycles of ℤ/4 have 4 (the unions of orbits)",
            subfunctors(c2, constant(c2, 2)).size() == 9 && subfunctors(Z4, two_cycles).size() == 4);
  const Category sub9 = subobjects(c2, constant(c2, 2));
  s.require("the subfunctors under inclusion are a Heyting algebra: cartesian closed as a category, though not Boolean", kategoria::limits::cartesian_closed(sub9).holds() && validate(sub9).holds());
  return s.done();
}
