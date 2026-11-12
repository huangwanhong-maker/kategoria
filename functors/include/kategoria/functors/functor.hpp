// Functors between finite categories and natural transformations between them: given, verified, and found by search.
//
// A functor is its values on objects and on every arrow; a natural transformation is its components. Whether such data
// are a functor, or natural, is a claim answered with the place where it fails (Mac Lane 1971, I.3–I.4).
//
// Search. for_each_functor() visits every functor C → D. It assigns arrows one at a time and carries each assignment to
// its consequences (the ends of an arrow fix the images of its objects; two assigned arrows that compose fix the image
// of their composite), so that only a generating set is branched on. The functors found are then exactly those that
// verify() accepts, which the checks confirm against the naive enumeration.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/kernel/verdict.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::functors {

using finite::Category;
using finite::Index;
using finite::none;
using kernel::Verdict;

struct Functor {
  std::string name;
  std::vector<Index> objects, arrows;  // the image of each object and of each arrow
};

// components[c] : F c → G c, an arrow of the target.
struct Transformation {
  std::string name;
  std::vector<Index> components;
};

inline Verdict verify(const Category& C, const Category& D, const Functor& F) {
  const std::string claim = (F.name.empty() ? "it" : F.name) + " is a functor " + C.name + " → " + D.name;
  if (F.objects.size() != C.objects.size() || F.arrows.size() != C.size()) return Verdict::no(claim, "it is not given on every object and arrow");
  for (Index a = 0; a < C.objects.size(); a++)
    if (F.objects[a] >= D.objects.size()) return Verdict::no(claim, "it sends " + C.objects[a] + " to no object").with("at", C.objects[a]);
  std::size_t examined = 0;
  for (Index f = 0; f < C.size(); f++) {
    examined++;
    if (F.arrows[f] >= D.size()) return Verdict::no(claim, "it sends " + C.arrows[f].name + " to no arrow").with("at", C.arrows[f].name);
    if (D.dom(F.arrows[f]) != F.objects[C.dom(f)] || D.cod(F.arrows[f]) != F.objects[C.cod(f)])
      return Verdict::no(claim, "the image of " + C.typed(f) + " is " + D.typed(F.arrows[f]) + ", which does not run between the images of its ends", examined).with("at", C.arrows[f].name);
  }
  for (Index a = 0; a < C.objects.size(); a++) {
    examined++;
    if (F.arrows[C.identity[a]] != D.identity[F.objects[a]])
      return Verdict::no(claim, "it does not keep the identity of " + C.objects[a], examined).with("at", C.objects[a]).with("left", D.arrows[F.arrows[C.identity[a]]].name).with("right", D.arrows[D.identity[F.objects[a]]].name);
  }
  for (Index g = 0; g < C.size(); g++)
    for (Index f = 0; f < C.size(); f++) {
      if (C.cod(f) != C.dom(g)) continue;
      examined++;
      const Index left = F.arrows[C.compose(g, f)], right = D.compose(F.arrows[g], F.arrows[f]);
      if (left != right)
        return Verdict::no(claim, "it does not keep the composite " + C.arrows[g].name + " ∘ " + C.arrows[f].name, examined)
            .with("at", C.arrows[g].name + ", " + C.arrows[f].name).with("left", "F(" + C.arrows[g].name + " ∘ " + C.arrows[f].name + ") = " + D.arrows[left].name)
            .with("right", "F(" + C.arrows[g].name + ") ∘ F(" + C.arrows[f].name + ") = " + D.arrows[right].name);
    }
  return Verdict::yes(claim, "it keeps the ends of every arrow, every identity and every composite", examined);
}

inline Functor identity(const Category& C) { return {"1", finite::detail::iota(C.objects.size()), finite::detail::iota(C.size())}; }

// G after F.
inline Functor compose(const Functor& G, const Functor& F) {
  Functor H{G.name + " ∘ " + F.name, {}, {}};
  for (Index a : F.objects) H.objects.push_back(G.objects[a]);
  for (Index f : F.arrows) H.arrows.push_back(G.arrows[f]);
  return H;
}

// The functor C → D that is constant at an object.
inline Functor constant(const Category& C, const Category& D, Index d) {
  return {"Δ" + D.objects[d], std::vector<Index>(C.objects.size(), d), std::vector<Index>(C.size(), D.identity[d])};
}

// ---- the search for functors --------------------------------------------------------------------------------------------------

struct Options {
  bool injective = false;                // only functors injective on arrows (and so on objects)
  std::uint64_t limit = 1'000'000;       // stop after this many
  std::vector<Index> objects, arrows;    // a part already fixed: none where free (empty: nothing fixed)
};

namespace detail {

class Search {
 public:
  Search(const Category& C, const Category& D, bool injective)
      : obj(C.objects.size(), none), arr(C.size(), none), C_(C), D_(D), injective_(injective), used_(D.size(), 0) {}

  std::size_t mark() const { return trail_.size(); }
  void undo(std::size_t mark) {
    while (trail_.size() > mark) {
      const Index e = trail_.back();
      trail_.pop_back();
      if (e >= C_.size()) {
        obj[e - C_.size()] = none;
      } else {
        used_[arr[e]] = 0;
        arr[e] = none;
      }
    }
  }
  // Sends the arrow a to b, with every consequence; false when that contradicts what is assigned.
  bool assign(Index a, Index b) {
    if (b == none) return false;
    if (arr[a] != none) return arr[a] == b;
    if (C_.is_identity(a) && !D_.is_identity(b)) return false;
    if (injective_ && used_[b]) return false;
    const Index da = C_.dom(a), ca = C_.cod(a);
    if ((obj[da] != none && obj[da] != D_.dom(b)) || (obj[ca] != none && obj[ca] != D_.cod(b))) return false;
    if (da == ca && D_.dom(b) != D_.cod(b)) return false;
    arr[a] = b, used_[b] = 1, trail_.push_back(a);
    if (!object(da, D_.dom(b)) || !object(ca, D_.cod(b))) return false;
    for (Index x = 0; x < C_.size(); x++) {
      if (arr[x] == none) continue;
      if (C_.cod(a) == C_.dom(x) && !assign(C_.compose(x, a), D_.compose(arr[x], b))) return false;
      if (arr[x] == none) continue;
      if (C_.cod(x) == C_.dom(a) && !assign(C_.compose(a, x), D_.compose(b, arr[x]))) return false;
    }
    return true;
  }
  bool object(Index o, Index p) {
    if (obj[o] != none) return obj[o] == p;
    obj[o] = p, trail_.push_back(static_cast<Index>(C_.size()) + o);
    return assign(C_.identity[o], D_.identity[p]);
  }

  std::vector<Index> obj, arr;

 private:
  const Category &C_, &D_;
  bool injective_;
  std::vector<char> used_;
  std::vector<Index> trail_;
};

template <class Visit>
bool run(Search& s, const Category& C, const Category& D, const std::vector<Index>& order, std::size_t k, Visit& visit, std::uint64_t& count, std::uint64_t limit) {
  while (k < order.size() && s.arr[order[k]] != none) k++;
  if (k == order.size()) {
    count++;
    return visit(Functor{"", s.obj, s.arr}) && count < limit;
  }
  const Index a = order[k];
  for (Index b = 0; b < D.size(); b++) {
    const std::size_t m = s.mark();
    const bool went = s.assign(a, b);
    const bool on = !went || run(s, C, D, order, k + 1, visit, count, limit);
    s.undo(m);
    if (!on) return false;
  }
  return true;
}

}  // namespace detail

// Visits every functor C → D (visit returns false to stop); the number visited.
template <class Visit>
std::uint64_t for_each_functor(const Category& C, const Category& D, Visit visit, const Options& options = {}) {
  detail::Search s(C, D, options.injective);
  for (Index a = 0; a < options.objects.size(); a++)
    if (options.objects[a] != none && !s.object(a, options.objects[a])) return 0;
  for (Index f = 0; f < options.arrows.size(); f++)
    if (options.arrows[f] != none && !s.assign(f, options.arrows[f])) return 0;
  std::vector<Index> order = finite::generators(C);
  for (Index i : C.identity) order.push_back(i);
  for (Index f = 0; f < C.size(); f++) order.push_back(f);
  std::uint64_t count = 0;
  detail::run(s, C, D, order, 0, visit, count, options.limit);
  return count;
}

inline std::uint64_t count_functors(const Category& C, const Category& D, const Options& options = {}) {
  return for_each_functor(C, D, [](const Functor&) { return true; }, options);
}
inline std::vector<Functor> all_functors(const Category& C, const Category& D, const Options& options = {}) {
  std::vector<Functor> out;
  for_each_functor(C, D, [&](const Functor& F) { return out.push_back(F), true; }, options);
  for (std::size_t k = 0; k < out.size(); k++) out[k].name = "F" + std::to_string(k);
  return out;
}

// An isomorphism of categories C → D, when there is one.
inline std::optional<Functor> isomorphism(const Category& C, const Category& D) {
  if (C.objects.size() != D.objects.size() || C.size() != D.size()) return std::nullopt;
  std::optional<Functor> found;
  Options o;
  o.injective = true;
  for_each_functor(C, D, [&](const Functor& F) { return found = F, false; }, o);
  return found;
}

// ---- natural transformations --------------------------------------------------------------------------------------------------

inline Verdict natural(const Category& C, const Category& D, const Functor& F, const Functor& G, const Transformation& t) {
  const std::string claim = (t.name.empty() ? "it" : t.name) + " is natural from " + (F.name.empty() ? "F" : F.name) + " to " + (G.name.empty() ? "G" : G.name);
  if (t.components.size() != C.objects.size()) return Verdict::no(claim, "it has not one component for each object");
  for (Index c = 0; c < C.objects.size(); c++) {
    const Index k = t.components[c];
    if (k >= D.size() || D.dom(k) != F.objects[c] || D.cod(k) != G.objects[c])
      return Verdict::no(claim, "its component at " + C.objects[c] + " does not run from " + D.objects[F.objects[c]] + " to " + D.objects[G.objects[c]]).with("at", C.objects[c]);
  }
  std::size_t examined = 0;
  for (Index f = 0; f < C.size(); f++) {
    examined++;
    const Index left = D.compose(G.arrows[f], t.components[C.dom(f)]), right = D.compose(t.components[C.cod(f)], F.arrows[f]);
    if (left != right)
      return Verdict::no(claim, "the square at " + C.typed(f) + " does not commute", examined).with("at", C.arrows[f].name)
          .with("left", D.arrows[G.arrows[f]].name + " ∘ " + D.arrows[t.components[C.dom(f)]].name + " = " + D.arrows[left].name)
          .with("right", D.arrows[t.components[C.cod(f)]].name + " ∘ " + D.arrows[F.arrows[f]].name + " = " + D.arrows[right].name);
  }
  return Verdict::yes(claim, "the square at every arrow commutes", examined);
}

// Visits every natural transformation F ⇒ G (visit returns false to stop); the number visited.
template <class Visit>
std::uint64_t for_each_transformation(const Category& C, const Category& D, const Functor& F, const Functor& G, Visit visit, bool isomorphisms = false) {
  const std::size_t m = C.objects.size();
  std::vector<std::vector<Index>> candidates(m), within(m);  // within[c]: the arrows of C between objects ≤ c that touch c
  for (Index c = 0; c < m; c++)
    for (Index k : D.hom(F.objects[c], G.objects[c]))
      if (!isomorphisms || finite::is_iso(D, k)) candidates[c].push_back(k);
  for (Index f = 0; f < C.size(); f++) within[std::max(C.dom(f), C.cod(f))].push_back(f);
  Transformation t{"", std::vector<Index>(m, none)};
  std::uint64_t count = 0;
  bool on = true;
  auto go = [&](auto& self, Index c) -> void {
    if (c == m) {
      count++;
      on = visit(t);
      return;
    }
    for (Index k : candidates[c]) {
      t.components[c] = k;
      bool ok = true;
      for (Index f : within[c])
        if (D.compose(G.arrows[f], t.components[C.dom(f)]) != D.compose(t.components[C.cod(f)], F.arrows[f])) {
          ok = false;
          break;
        }
      if (ok) self(self, c + 1);
      if (!on) return;
    }
    t.components[c] = none;
  };
  go(go, 0);
  return count;
}
inline std::vector<Transformation> all_transformations(const Category& C, const Category& D, const Functor& F, const Functor& G) {
  std::vector<Transformation> out;
  for_each_transformation(C, D, F, G, [&](const Transformation& t) { return out.push_back(t), true; });
  return out;
}
// A natural isomorphism F ≅ G, when there is one.
inline std::optional<Transformation> natural_isomorphism(const Category& C, const Category& D, const Functor& F, const Functor& G) {
  std::optional<Transformation> found;
  for_each_transformation(C, D, F, G, [&](const Transformation& t) { return found = t, false; }, true);
  return found;
}

inline Transformation identity_transformation(const Category& C, const Category& D, const Functor& F) {
  Transformation t{"1", {}};
  for (Index c = 0; c < C.objects.size(); c++) t.components.push_back(D.identity[F.objects[c]]);
  return t;
}
// s after t, for t : F ⇒ G and s : G ⇒ H.
inline Transformation vertical(const Category& D, const Transformation& s, const Transformation& t) {
  Transformation r{s.name + " · " + t.name, {}};
  for (std::size_t c = 0; c < t.components.size(); c++) r.components.push_back(D.compose(s.components[c], t.components[c]));
  return r;
}
// H t, for t : F ⇒ G : C → D and H : D → E: the components H(t_c).
inline Transformation whisker_left(const Functor& H, const Transformation& t) {
  Transformation r{H.name + t.name, {}};
  for (Index k : t.components) r.components.push_back(H.arrows[k]);
  return r;
}
// t K, for K : B → C and t : F ⇒ G : C → D: the components t_{K b}.
inline Transformation whisker_right(const Transformation& t, const Functor& K) {
  Transformation r{t.name + K.name, {}};
  for (Index b : K.objects) r.components.push_back(t.components[b]);
  return r;
}
// The horizontal composite s ∗ t of t : F ⇒ G : C → D and s : H ⇒ K : D → E, with components s_{G c} ∘ H(t_c).
inline Transformation horizontal(const Category& E, const Functor& G, const Functor& H, const Transformation& s, const Transformation& t) {
  Transformation r{s.name + " ∗ " + t.name, {}};
  for (std::size_t c = 0; c < t.components.size(); c++) r.components.push_back(E.compose(s.components[G.objects[c]], H.arrows[t.components[c]]));
  return r;
}

// ---- the category of functors -------------------------------------------------------------------------------------------------

struct FunctorCategory {
  Category category;                            // its object k is functors[k], its arrow k is transformations[k]
  std::vector<Functor> functors;
  std::vector<Transformation> transformations;
  std::vector<std::pair<Index, Index>> between;  // the functors each transformation runs between
};

// [C, D]: the functors C → D and the natural transformations between them. Throws std::length_error past `most` arrows.
inline FunctorCategory functor_category(const Category& C, const Category& D, std::size_t most = 5000) {
  FunctorCategory R;
  Options o;
  o.limit = most + 1;
  R.functors = all_functors(C, D, o);
  if (R.functors.size() > most) throw std::length_error("kategoria::functors::functor_category: more than " + std::to_string(most) + " functors");
  const Index m = static_cast<Index>(R.functors.size());
  std::vector<std::string> names;
  std::vector<finite::Arrow> arrows;
  std::map<std::tuple<Index, Index, std::vector<Index>>, Index> at;
  for (Index i = 0; i < m; i++) {
    names.push_back(R.functors[i].name);
    Transformation t = identity_transformation(C, D, R.functors[i]);
    at[{i, i, t.components}] = i;
    arrows.push_back({"id_" + names[i], i, i});
    R.transformations.push_back(std::move(t)), R.between.push_back({i, i});
  }
  for (Index i = 0; i < m; i++)
    for (Index j = 0; j < m; j++)
      for (auto& t : all_transformations(C, D, R.functors[i], R.functors[j])) {
        if (at.count({i, j, t.components})) continue;
        if (arrows.size() >= most) throw std::length_error("kategoria::functors::functor_category: more than " + std::to_string(most) + " natural transformations");
        at[{i, j, t.components}] = static_cast<Index>(arrows.size());
        arrows.push_back({"t" + std::to_string(arrows.size() - m) + ":" + names[i] + "⇒" + names[j], i, j});
        R.transformations.push_back(t), R.between.push_back({i, j});
      }
  R.category = finite::assemble("[" + C.name + ", " + D.name + "]", std::move(names), std::move(arrows), finite::detail::iota(m), [&](Index g, Index f) {
    return at.at({R.between[f].first, R.between[g].second, vertical(D, R.transformations[g], R.transformations[f]).components});
  });
  return R;
}

// ---- what a functor keeps -----------------------------------------------------------------------------------------------------

inline Verdict faithful(const Category& C, const Category& D, const Functor& F) {
  const std::string claim = (F.name.empty() ? "it" : F.name) + " is faithful";
  std::size_t examined = 0;
  for (Index f = 0; f < C.size(); f++)
    for (Index g = f + 1; g < C.size(); g++) {
      if (C.dom(f) != C.dom(g) || C.cod(f) != C.cod(g)) continue;
      examined++;
      if (F.arrows[f] == F.arrows[g])
        return Verdict::no(claim, "it sends " + C.arrows[f].name + " and " + C.arrows[g].name + " to " + D.arrows[F.arrows[f]].name, examined).with("at", C.arrows[f].name + ", " + C.arrows[g].name);
    }
  return Verdict::yes(claim, "it tells apart every pair of parallel arrows", examined);
}
inline Verdict full(const Category& C, const Category& D, const Functor& F) {
  const std::string claim = (F.name.empty() ? "it" : F.name) + " is full";
  std::size_t examined = 0;
  for (Index a = 0; a < C.objects.size(); a++)
    for (Index b = 0; b < C.objects.size(); b++)
      for (Index h : D.hom(F.objects[a], F.objects[b])) {
        examined++;
        bool hit = false;
        for (Index f : C.hom(a, b)) hit = hit || F.arrows[f] == h;
        if (!hit) return Verdict::no(claim, D.typed(h) + " is the image of no arrow " + C.objects[a] + " → " + C.objects[b], examined).with("at", D.arrows[h].name);
      }
  return Verdict::yes(claim, "every arrow between images is an image", examined);
}
inline Verdict essentially_surjective(const Category& C, const Category& D, const Functor& F) {
  const std::string claim = (F.name.empty() ? "it" : F.name) + " is essentially surjective";
  const auto cls = finite::isomorphism_classes(D);
  std::vector<char> hit(D.objects.size(), 0);
  for (Index a : F.objects) hit[cls[a]] = 1;
  for (Index d = 0; d < D.objects.size(); d++)
    if (!hit[cls[d]]) return Verdict::no(claim, D.objects[d] + " is isomorphic to no image", D.objects.size()).with("at", D.objects[d]);
  (void)C;
  return Verdict::yes(claim, "every object is isomorphic to an image", D.objects.size());
}

// An equivalence, with what makes it one: a functor back, and natural isomorphisms 1 ≅ G F and F G ≅ 1.
struct Equivalence {
  Verdict verdict;
  Functor inverse;               // G : D → C
  Transformation unit, counit;   // unit : 1 ⇒ G F, counit : F G ⇒ 1
};

// Whether F is an equivalence. Where it is full, faithful and essentially surjective, the functor back is built
// (Mac Lane 1971, IV.4, Theorem 1) and what was built is verified.
inline Equivalence equivalence(const Category& C, const Category& D, const Functor& F) {
  Equivalence E;
  const std::string claim = (F.name.empty() ? "it" : F.name) + " is an equivalence " + C.name + " ≃ " + D.name;
  E.verdict = kernel::both(kernel::both(kernel::both(verify(C, D, F), faithful(C, D, F)), full(C, D, F)), essentially_surjective(C, D, F));
  if (!E.verdict.holds()) {
    E.verdict.reason = E.verdict.claim + " fails: " + E.verdict.reason;
    E.verdict.claim = claim;
    return E;
  }
  // For each d, an object c with an isomorphism e_d : F c → d.
  const std::size_t m = D.objects.size();
  std::vector<Index> back(m, none), e(m, none), e_inverse(m, none);
  for (Index d = 0; d < m; d++)
    for (Index c = 0; c < C.objects.size() && back[d] == none; c++)
      for (Index k : D.hom(F.objects[c], d))
        if (const Index inv = finite::inverse(D, k); inv != none) {
          back[d] = c, e[d] = k, e_inverse[d] = inv;
          break;
        }
  auto lift = [&](Index a, Index b, Index h) {  // the arrow a → b of C over h : F a → F b
    for (Index f : C.hom(a, b))
      if (F.arrows[f] == h) return f;
    return none;
  };
  E.inverse = {"G", back, std::vector<Index>(D.size(), none)};
  for (Index h = 0; h < D.size(); h++)
    E.inverse.arrows[h] = lift(back[D.dom(h)], back[D.cod(h)], D.compose(e_inverse[D.cod(h)], D.compose(h, e[D.dom(h)])));
  E.counit = {"ε", e};
  E.unit = {"η", {}};
  for (Index c = 0; c < C.objects.size(); c++) E.unit.components.push_back(lift(c, back[F.objects[c]], e_inverse[F.objects[c]]));
  const Functor GF = compose(E.inverse, F), FG = compose(F, E.inverse);
  Verdict built = kernel::both(kernel::both(verify(D, C, E.inverse), natural(C, C, identity(C), GF, E.unit)), natural(D, D, FG, identity(D), E.counit));
  for (Index k : E.unit.components)
    if (built.holds() && !finite::is_iso(C, k)) built = Verdict::no(claim, "a component of the unit built is not invertible");
  if (!built.holds()) {
    E.verdict = Verdict::unknown(claim, "the functor back that was built did not verify: " + built.reason);
    return E;
  }
  E.verdict = Verdict::yes(claim, "it is full, faithful and essentially surjective; a functor back and natural isomorphisms 1 ≅ G F and F G ≅ 1 were built and verified", E.verdict.examined + built.examined);
  return E;
}

// Whether two categories are equivalent: exactly when their skeletons are isomorphic.
inline Verdict equivalent(const Category& C, const Category& D) {
  const std::string claim = C.name + " ≃ " + D.name;
  const auto S = finite::skeleton(C), T = finite::skeleton(D);
  const auto iso = isomorphism(S.category, T.category);
  if (!iso) return Verdict::no(claim, "their skeletons, of " + std::to_string(S.category.objects.size()) + " and " + std::to_string(T.category.objects.size()) + " objects and " +
                                          std::to_string(S.category.size()) + " and " + std::to_string(T.category.size()) + " arrows, are not isomorphic (every bijection of their arrows was tried)");
  Verdict v = Verdict::yes(claim, "their skeletons are isomorphic", S.category.size());
  std::string pairs;
  for (Index a = 0; a < S.category.objects.size(); a++) pairs += (a ? ", " : "") + S.category.objects[a] + " ↦ " + T.category.objects[iso->objects[a]];
  return v.with("witness", pairs);
}

// ---- comma categories ---------------------------------------------------------------------------------------------------------

// F ↓ G for F : A → C and G : B → C: its objects are the (a, b, h : F a → G b), its arrows from (a, b, h) to (a′, b′, h′)
// the pairs (u : a → a′, v : b → b′) with G v ∘ h = h′ ∘ F u (Mac Lane 1971, II.6).
struct Comma {
  Category category;
  Functor first, second;                       // to A and to B
  std::vector<std::array<Index, 3>> objects;   // (a, b, h)
  std::vector<std::pair<Index, Index>> arrows; // (u, v)
};

inline Comma comma(const Category& A, const Category& B, const Category& C, const Functor& F, const Functor& G) {
  Comma K;
  std::vector<std::string> names;
  for (Index a = 0; a < A.objects.size(); a++)
    for (Index b = 0; b < B.objects.size(); b++)
      for (Index h : C.hom(F.objects[a], G.objects[b])) {
        K.objects.push_back({a, b, h});
        names.push_back("(" + A.objects[a] + "," + B.objects[b] + "," + C.arrows[h].name + ")");
      }
  const Index m = static_cast<Index>(K.objects.size());
  std::vector<finite::Arrow> arrows;
  std::map<std::array<Index, 4>, Index> at;  // (source, target, u, v)
  for (int pass = 0; pass < 2; pass++)       // identities first
    for (Index x = 0; x < m; x++)
      for (Index y = 0; y < m; y++)
        for (Index u : A.hom(K.objects[x][0], K.objects[y][0]))
          for (Index v : B.hom(K.objects[x][1], K.objects[y][1])) {
            if (C.compose(G.arrows[v], K.objects[x][2]) != C.compose(K.objects[y][2], F.arrows[u])) continue;
            const bool id = x == y && A.is_identity(u) && B.is_identity(v);
            if (id != (pass == 0)) continue;
            at[{x, y, u, v}] = static_cast<Index>(arrows.size());
            K.arrows.push_back({u, v});
            arrows.push_back({id ? "id_" + names[x] : "(" + A.arrows[u].name + "," + B.arrows[v].name + "):" + names[x] + "→" + names[y], x, y});
          }
  const auto ends = arrows;
  K.first = {"P", {}, {}}, K.second = {"Q", {}, {}};
  for (auto& o : K.objects) K.first.objects.push_back(o[0]), K.second.objects.push_back(o[1]);
  for (auto& [u, v] : K.arrows) K.first.arrows.push_back(u), K.second.arrows.push_back(v);
  K.category = finite::assemble("(" + F.name + " ↓ " + G.name + ")", std::move(names), std::move(arrows), finite::detail::iota(m), [&](Index g, Index f) {
    return at.at({ends[f].dom, ends[g].cod, A.compose(K.arrows[g].first, K.arrows[f].first), B.compose(K.arrows[g].second, K.arrows[f].second)});
  });
  return K;
}

}  // namespace kategoria::functors
