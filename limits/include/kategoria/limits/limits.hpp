// Limits and colimits in a finite category: cones, their universal property decided, and the limit found.
//
// A diagram is a functor D : J → C. A cone on it is an apex with a leg to each D(j), commuting with the diagram's
// arrows; it is a limit when every cone factors through it by exactly one arrow (Mac Lane 1971, III.3–III.4).
// is_limit() decides that by examining every cone, and answers a failure with the cone that does not factor, or
// factors twice. limit() searches the cones for one that is_limit() accepts.
//
// Colimits are limits in the opposite category: a cocone is held as a Cone whose legs run D(j) → apex.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/functors/functor.hpp>
#include <kategoria/kernel/verdict.hpp>

#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::limits {

using finite::Category;
using finite::Index;
using finite::none;
using functors::Functor;
using kernel::Verdict;

namespace detail {
inline void replace_all(std::string& s, const std::string& from, const std::string& to) {
  for (std::size_t at = 0; (at = s.find(from, at)) != std::string::npos; at += to.size()) s.replace(at, from.size(), to);
}
}  // namespace detail

struct Cone {
  Index apex = none;
  std::vector<Index> legs;  // legs[j] : apex → D(j)
};

inline std::string words(const Category& C, const Cone& K) {
  std::string w = C.objects[K.apex];
  for (std::size_t j = 0; j < K.legs.size(); j++) w += (j ? ", " : " with ") + C.arrows[K.legs[j]].name;
  return w;
}

inline Verdict verify_cone(const Category& C, const Category& J, const Functor& D, const Cone& K) {
  const std::string claim = "it is a cone on " + (D.name.empty() ? "the diagram" : D.name);
  if (K.apex >= C.objects.size() || K.legs.size() != J.objects.size()) return Verdict::no(claim, "it has not an apex and one leg for each object of the shape");
  for (Index j = 0; j < J.objects.size(); j++)
    if (K.legs[j] >= C.size() || C.dom(K.legs[j]) != K.apex || C.cod(K.legs[j]) != D.objects[j])
      return Verdict::no(claim, "its leg at " + J.objects[j] + " does not run from the apex to " + C.objects[D.objects[j]]).with("at", J.objects[j]);
  for (Index u = 0; u < J.size(); u++)
    if (C.compose(D.arrows[u], K.legs[J.dom(u)]) != K.legs[J.cod(u)])
      return Verdict::no(claim, "its legs do not commute with " + C.arrows[D.arrows[u]].name).with("at", J.arrows[u].name);
  return Verdict::yes(claim, "its legs commute with every arrow of the diagram", J.size());
}

// Visits every cone on D (visit returns false to stop); the number visited.
template <class Visit>
std::uint64_t for_each_cone(const Category& C, const Category& J, const Functor& D, Visit visit) {
  const std::size_t m = J.objects.size();
  std::vector<std::vector<Index>> within(m);  // the arrows of J between objects ≤ j that touch j
  for (Index u = 0; u < J.size(); u++) within[std::max(J.dom(u), J.cod(u))].push_back(u);
  std::uint64_t count = 0;
  bool on = true;
  Cone K;
  K.legs.assign(m, none);
  auto go = [&](auto& self, Index j) -> void {
    if (j == m) {
      count++;
      on = visit(K);
      return;
    }
    for (Index leg : C.hom(K.apex, D.objects[j])) {
      K.legs[j] = leg;
      bool ok = true;
      for (Index u : within[j])
        if (C.compose(D.arrows[u], K.legs[J.dom(u)]) != K.legs[J.cod(u)]) {
          ok = false;
          break;
        }
      if (ok) self(self, j + 1);
      if (!on) return;
    }
    K.legs[j] = none;
  };
  for (Index a = 0; a < C.objects.size() && on; a++) {
    K.apex = a;
    go(go, 0);
  }
  return count;
}

// The arrows h : from.apex → to.apex with to.legs[j] ∘ h = from.legs[j] for every j.
inline std::vector<Index> factorisations(const Category& C, const Cone& from, const Cone& to) {
  std::vector<Index> out;
  for (Index h : C.hom(from.apex, to.apex)) {
    bool ok = true;
    for (std::size_t j = 0; j < to.legs.size() && ok; j++) ok = C.compose(to.legs[j], h) == from.legs[j];
    if (ok) out.push_back(h);
  }
  return out;
}

// Whether a cone is a limit: every cone factors through it by exactly one arrow.
inline Verdict is_limit(const Category& C, const Category& J, const Functor& D, const Cone& L) {
  const std::string claim = words(C, L) + " is a limit of " + (D.name.empty() ? "the diagram" : D.name);
  if (Verdict v = verify_cone(C, J, D, L); !v.holds()) return Verdict::no(claim, "it is not a cone: " + v.reason);
  Verdict out = Verdict::yes(claim);
  out.examined = for_each_cone(C, J, D, [&](const Cone& K) {
    const auto through = factorisations(C, K, L);
    if (through.size() == 1) return true;
    out = Verdict::no(claim, through.empty() ? "the cone from " + words(C, K) + " does not factor through it" : "the cone from " + words(C, K) + " factors through it in " + std::to_string(through.size()) + " ways");
    out.with("at", words(C, K));
    for (Index h : through) out.with("through", C.arrows[h].name);
    return false;
  });
  if (out.holds()) out.reason = (out.examined == 1 ? std::string("the one cone factors") : "each of the " + std::to_string(out.examined) + " cones factors") + " through it by exactly one arrow";
  return out;
}

struct Limit {
  Verdict verdict;
  std::optional<Cone> cone;
};

// A limit of D, when there is one.
inline Limit limit(const Category& C, const Category& J, const Functor& D) {
  const std::string claim = "there is a limit of " + (D.name.empty() ? "the diagram" : D.name) + " in " + C.name;
  Limit R;
  std::uint64_t cones = for_each_cone(C, J, D, [&](const Cone& K) {
    if (!is_limit(C, J, D, K).holds()) return true;
    R.cone = K;
    return false;
  });
  if (R.cone) {
    R.verdict = is_limit(C, J, D, *R.cone);
    R.verdict.with("witness", words(C, *R.cone));
  } else {
    R.verdict = Verdict::no(claim, cones == 0 ? "the diagram has no cone at all" : cones == 1 ? "its one cone is not universal" : "none of its " + std::to_string(cones) + " cones is universal", cones);
  }
  return R;
}

// A colimit of D: a limit of the same data between the opposite categories. Its legs run D(j) → apex.
inline Limit colimit(const Category& C, const Category& J, const Functor& D) {
  Limit R = limit(finite::opposite(C), finite::opposite(J), D);
  auto turn = [](std::string& s) { detail::replace_all(s, "a limit", "a colimit"), detail::replace_all(s, "cone", "cocone"); };
  turn(R.verdict.claim), turn(R.verdict.reason);
  return R;
}
inline Verdict is_colimit(const Category& C, const Category& J, const Functor& D, const Cone& L) { return is_limit(finite::opposite(C), finite::opposite(J), D, L); }

// ---- diagrams of the usual shapes ---------------------------------------------------------------------------------------------

struct Diagram {
  Category shape;
  Functor functor;
};

inline Diagram empty_diagram() { return {finite::discrete(std::vector<std::string>{}, "∅"), {"the empty diagram", {}, {}}}; }

// Objects with no arrows between them.
inline Diagram discrete_diagram(const Category& C, const std::vector<Index>& objects) {
  Diagram G{finite::discrete(objects.size()), {"the objects", objects, {}}};
  std::string w;
  for (Index a : objects) G.functor.arrows.push_back(C.identity[a]), w += (w.empty() ? "" : ", ") + C.objects[a];
  G.functor.name = "the objects " + w;
  return G;
}

// Two parallel arrows f, g : a → b, on the shape • ⇉ •.
inline Diagram parallel_diagram(const Category& C, Index f, Index g) {
  if (C.dom(f) != C.dom(g) || C.cod(f) != C.cod(g)) throw std::invalid_argument("kategoria::limits::parallel_diagram: " + C.arrows[f].name + " and " + C.arrows[g].name + " are not parallel");
  Category J = finite::assemble("⇉", {"0", "1"}, {{"id_0", 0, 0}, {"id_1", 1, 1}, {"u", 0, 1}, {"v", 0, 1}}, {0, 1}, [](Index y, Index x) { return x < 2 ? y : x; });
  return {std::move(J), {"the pair " + C.arrows[f].name + ", " + C.arrows[g].name, {C.dom(f), C.cod(f)}, {C.identity[C.dom(f)], C.identity[C.cod(f)], f, g}}};
}

// A cospan f : a → c ← b : g, on the shape • → • ← • (objects 0, 1, 2 with 2 the corner).
inline Diagram cospan_diagram(const Category& C, Index f, Index g) {
  if (C.cod(f) != C.cod(g)) throw std::invalid_argument("kategoria::limits::cospan_diagram: " + C.arrows[f].name + " and " + C.arrows[g].name + " do not end at one object");
  Category J = finite::assemble("→•←", {"0", "1", "2"}, {{"id_0", 0, 0}, {"id_1", 1, 1}, {"id_2", 2, 2}, {"u", 0, 2}, {"v", 1, 2}}, {0, 1, 2}, [](Index y, Index x) { return x < 3 ? y : x; });
  return {std::move(J), {"the cospan " + C.arrows[f].name + ", " + C.arrows[g].name, {C.dom(f), C.dom(g), C.cod(f)}, {C.identity[C.dom(f)], C.identity[C.dom(g)], C.identity[C.cod(f)], f, g}}};
}

// A span f : a ← c → b : g, on the shape • ← • → • (objects 0, 1, 2 with 2 the corner).
inline Diagram span_diagram(const Category& C, Index f, Index g) {
  if (C.dom(f) != C.dom(g)) throw std::invalid_argument("kategoria::limits::span_diagram: " + C.arrows[f].name + " and " + C.arrows[g].name + " do not begin at one object");
  Category J = finite::assemble("←•→", {"0", "1", "2"}, {{"id_0", 0, 0}, {"id_1", 1, 1}, {"id_2", 2, 2}, {"u", 2, 0}, {"v", 2, 1}}, {0, 1, 2}, [](Index y, Index x) { return y < 3 ? x : y; });
  return {std::move(J), {"the span " + C.arrows[f].name + ", " + C.arrows[g].name, {C.cod(f), C.cod(g), C.dom(f)}, {C.identity[C.cod(f)], C.identity[C.cod(g)], C.identity[C.dom(f)], f, g}}};
}

inline Limit terminal(const Category& C) {
  const Diagram G = empty_diagram();
  return limit(C, G.shape, G.functor);
}
inline Limit initial(const Category& C) {
  const Diagram G = empty_diagram();
  return colimit(C, G.shape, G.functor);
}
inline Limit product(const Category& C, Index a, Index b) {
  const Diagram G = discrete_diagram(C, {a, b});
  return limit(C, G.shape, G.functor);
}
inline Limit coproduct(const Category& C, Index a, Index b) {
  const Diagram G = discrete_diagram(C, {a, b});
  return colimit(C, G.shape, G.functor);
}
inline Limit equalizer(const Category& C, Index f, Index g) {
  const Diagram G = parallel_diagram(C, f, g);
  return limit(C, G.shape, G.functor);
}
inline Limit coequalizer(const Category& C, Index f, Index g) {
  const Diagram G = parallel_diagram(C, f, g);
  return colimit(C, G.shape, G.functor);
}
inline Limit pullback(const Category& C, Index f, Index g) {
  const Diagram G = cospan_diagram(C, f, g);
  return limit(C, G.shape, G.functor);
}
inline Limit pushout(const Category& C, Index f, Index g) {
  const Diagram G = span_diagram(C, f, g);
  return colimit(C, G.shape, G.functor);
}

// ---- having limits ------------------------------------------------------------------------------------------------------------

// Whether C has a terminal object, a product of every two objects and an equalizer of every parallel pair, and so
// every finite limit (Mac Lane 1971, V.2). A failure names the first diagram with no limit.
inline Verdict finitely_complete(const Category& C) {
  const std::string claim = C.name + " has every finite limit";
  std::size_t examined = 1;
  if (!terminal(C).cone) return Verdict::no(claim, "it has no terminal object", examined).with("at", "the empty diagram");
  for (Index a = 0; a < C.objects.size(); a++)
    for (Index b = a; b < C.objects.size(); b++) {
      examined++;
      if (!product(C, a, b).cone) return Verdict::no(claim, C.objects[a] + " and " + C.objects[b] + " have no product", examined).with("at", C.objects[a] + ", " + C.objects[b]);
    }
  for (Index f = 0; f < C.size(); f++)
    for (Index g = f + 1; g < C.size(); g++) {
      if (C.dom(f) != C.dom(g) || C.cod(f) != C.cod(g)) continue;
      examined++;
      if (!equalizer(C, f, g).cone) return Verdict::no(claim, C.arrows[f].name + " and " + C.arrows[g].name + " have no equalizer", examined).with("at", C.arrows[f].name + ", " + C.arrows[g].name);
    }
  return Verdict::yes(claim, "it has a terminal object, a product of every two objects and an equalizer of every parallel pair", examined);
}
inline Verdict finitely_cocomplete(const Category& C) {
  Verdict v = finitely_complete(finite::opposite(C));
  v.claim = C.name + " has every finite colimit";
  for (const auto& [from, to] : std::vector<std::pair<std::string, std::string>>{{"terminal", "initial"}, {"a product", "a coproduct"}, {"no product", "no coproduct"},
                                                                                {"an equalizer", "a coequalizer"}, {"no equalizer", "no coequalizer"}})
    detail::replace_all(v.reason, from, to);
  return v;
}

// Whether F : C → E keeps this limit: the image of the cone is a limit of F ∘ D.
inline Verdict preserves(const Category& J, const Functor& D, const Cone& L, const Category& E, const Functor& F) {
  Cone image{F.objects[L.apex], {}};
  for (Index leg : L.legs) image.legs.push_back(F.arrows[leg]);
  Functor FD = functors::compose(F, D);
  FD.name = "the image of " + (D.name.empty() ? "the diagram" : D.name);
  Verdict v = is_limit(E, J, FD, image);
  v.claim = (F.name.empty() ? "the functor" : F.name) + " keeps the limit of " + (D.name.empty() ? "the diagram" : D.name);
  return v;
}

// ---- exponentials -------------------------------------------------------------------------------------------------------------

// An exponential b^a: an object e with ev : e × a → b such that every g : c × a → b is ev ∘ (h × 1) for exactly one
// h : c → e (Mac Lane 1971, IV.6). Needs the products with a.
struct Exponential {
  Verdict verdict;
  Index object = none, evaluation = none;  // e, and ev : e × a → b with e × a the product found
};

inline Exponential exponential(const Category& C, Index a, Index b) {
  const std::string claim = C.objects[b] + "^" + C.objects[a] + " exists in " + C.name;
  const std::size_t m = C.objects.size();
  std::vector<Cone> times(m);  // times[c]: the product c × a
  for (Index c = 0; c < m; c++) {
    const Limit P = product(C, c, a);
    if (!P.cone) return {Verdict::no(claim, C.objects[c] + " and " + C.objects[a] + " have no product").with("at", C.objects[c] + ", " + C.objects[a]), none, none};
    times[c] = *P.cone;
  }
  // h × 1 : c × a → e × a, the arrow whose projections are h ∘ π₁ and π₂.
  auto times_one = [&](Index h, Index c, Index e) {
    const Cone from{times[c].apex, {C.compose(h, times[c].legs[0]), times[c].legs[1]}};
    return factorisations(C, from, times[e]).front();
  };
  std::size_t examined = 0;
  for (Index e = 0; e < m; e++)
    for (Index ev : C.hom(times[e].apex, b)) {
      bool universal = true;
      for (Index c = 0; c < m && universal; c++)
        for (Index g : C.hom(times[c].apex, b)) {
          examined++;
          std::size_t count = 0;
          for (Index h : C.hom(c, e)) count += C.compose(ev, times_one(h, c, e)) == g;
          if (count != 1) {
            universal = false;
            break;
          }
        }
      if (universal)
        return {Verdict::yes(claim, "every arrow c × " + C.objects[a] + " → " + C.objects[b] + " is the transpose of exactly one arrow c → " + C.objects[e], examined).with("witness", C.objects[e] + " with " + C.arrows[ev].name), e, ev};
    }
  return {Verdict::no(claim, "no object with an evaluation is universal", examined).with("at", C.objects[a] + ", " + C.objects[b]), none, none};
}

// Whether C is cartesian closed: a terminal object, binary products and exponentials.
inline Verdict cartesian_closed(const Category& C) {
  const std::string claim = C.name + " is cartesian closed";
  if (!terminal(C).cone) return Verdict::no(claim, "it has no terminal object").with("at", "the empty diagram");
  std::size_t examined = 0;
  for (Index a = 0; a < C.objects.size(); a++)
    for (Index b = 0; b < C.objects.size(); b++) {
      const Exponential E = exponential(C, a, b);
      examined += E.verdict.examined;
      if (!E.verdict.holds()) return Verdict::no(claim, E.verdict.reason.rfind("no object", 0) == 0 ? C.objects[b] + "^" + C.objects[a] + " does not exist" : E.verdict.reason, examined).with("at", std::string(E.verdict.piece("at")));
    }
  return Verdict::yes(claim, "it has a terminal object, a product of every two objects and an exponential of every two", examined);
}

}  // namespace kategoria::limits
