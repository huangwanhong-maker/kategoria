// Set-valued functors on a finite category: C → FinSet, given whole, with what is computed from them.
//
// A functor X : C → FinSet (a copresheaf; a presheaf is one on the opposite category) is a finite set for each object
// and a function for each arrow. Read as data, C is a schema and X an instance of it (Spivak 2012). Held here:
//
//   - representables Hom(a, −) and the Yoneda lemma, decided by enumeration (Mac Lane 1971, III.2);
//   - the category of elements;
//   - limits (sections) and colimits (classes) of X;
//   - the three functors along K : C → D: the pullback Y ∘ K, and the left and right Kan extensions of X, computed
//     pointwise from comma categories (X.3, Theorem 1), each with the unit or counit that makes it universal, and that
//     universal property decided for a given Y;
//   - the classifier of subobjects of [C, FinSet], whose value at c is the set of cosieves on c, with the subfunctors
//     of X and their characteristic maps (Mac Lane and Moerdijk 1992, ch. I).
//
// Natural transformations between such functors are found by assigning the image of one element at a time and
// carrying it along every arrow, so that one choice is made for each orbit.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/functors/functor.hpp>
#include <kategoria/kernel/verdict.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::sets {

using finite::Category;
using finite::Index;
using finite::none;
using functors::Functor;
using kernel::Verdict;

using Function = std::vector<Index>;  // the image of each element of a finite set {0, …, n − 1}
using Family = std::vector<Function>; // a function for each object

struct Copresheaf {
  std::string name;
  std::vector<std::vector<std::string>> elements;  // elements[c]: the elements of X(c), by name
  std::vector<Function> action;                    // action[f] : X(dom f) → X(cod f)

  std::size_t size(Index c) const { return elements[c].size(); }
  std::size_t total() const {
    std::size_t n = 0;
    for (auto& e : elements) n += e.size();
    return n;
  }
};

inline Verdict verify(const Category& C, const Copresheaf& X) {
  const std::string claim = (X.name.empty() ? "it" : X.name) + " is a functor " + C.name + " → FinSet";
  if (X.elements.size() != C.objects.size() || X.action.size() != C.size()) return Verdict::no(claim, "it is not given on every object and arrow");
  std::size_t examined = 0;
  for (Index f = 0; f < C.size(); f++) {
    if (X.action[f].size() != X.size(C.dom(f))) return Verdict::no(claim, "its function at " + C.arrows[f].name + " is not defined on the whole of " + C.objects[C.dom(f)]).with("at", C.arrows[f].name);
    for (Index y : X.action[f])
      if (y >= X.size(C.cod(f))) return Verdict::no(claim, "its function at " + C.arrows[f].name + " leaves " + C.objects[C.cod(f)]).with("at", C.arrows[f].name);
  }
  for (Index a = 0; a < C.objects.size(); a++)
    for (Index x = 0; x < X.size(a); x++) {
      examined++;
      if (X.action[C.identity[a]][x] != x) return Verdict::no(claim, "the identity of " + C.objects[a] + " moves " + X.elements[a][x], examined).with("at", C.objects[a]);
    }
  for (Index g = 0; g < C.size(); g++)
    for (Index f = 0; f < C.size(); f++) {
      if (C.cod(f) != C.dom(g)) continue;
      const Index gf = C.compose(g, f);
      for (Index x = 0; x < X.size(C.dom(f)); x++) {
        examined++;
        if (X.action[gf][x] != X.action[g][X.action[f][x]])
          return Verdict::no(claim, "it does not keep the composite " + C.arrows[g].name + " ∘ " + C.arrows[f].name + " at " + X.elements[C.dom(f)][x], examined).with("at", C.arrows[g].name + ", " + C.arrows[f].name);
      }
    }
  return Verdict::yes(claim, "it keeps every identity and every composite, element by element", examined);
}

// Hom(a, −): its elements at b are the arrows a → b, moved by composition.
inline Copresheaf representable(const Category& C, Index a) {
  Copresheaf X{"Hom(" + C.objects[a] + ", −)", std::vector<std::vector<std::string>>(C.objects.size()), std::vector<Function>(C.size())};
  std::vector<Index> place(C.size(), none);
  for (Index f = 0; f < C.size(); f++)
    if (C.dom(f) == a) place[f] = static_cast<Index>(X.elements[C.cod(f)].size()), X.elements[C.cod(f)].push_back(C.arrows[f].name);
  for (Index g = 0; g < C.size(); g++)
    for (Index f = 0; f < C.size(); f++)
      if (C.dom(f) == a && C.cod(f) == C.dom(g)) {
        if (X.action[g].empty()) X.action[g].assign(X.size(C.dom(g)), none);
        X.action[g][place[f]] = place[C.compose(g, f)];
      }
  return X;
}

// The functor constant at a set of n elements; with n = 1, the terminal one.
inline Copresheaf constant(const Category& C, std::size_t n) {
  Copresheaf X{n == 1 ? "1" : "the constant " + std::to_string(n), {}, {}};
  std::vector<std::string> names;
  for (std::size_t i = 0; i < n; i++) names.push_back(n == 1 ? "∗" : std::to_string(i));
  X.elements.assign(C.objects.size(), names);
  X.action.assign(C.size(), finite::detail::iota(n));
  return X;
}

// ---- natural transformations --------------------------------------------------------------------------------------------------

inline Verdict natural(const Category& C, const Copresheaf& X, const Copresheaf& Y, const Family& t) {
  const std::string claim = "it is natural from " + (X.name.empty() ? "X" : X.name) + " to " + (Y.name.empty() ? "Y" : Y.name);
  if (t.size() != C.objects.size()) return Verdict::no(claim, "it has not one function for each object");
  for (Index c = 0; c < C.objects.size(); c++) {
    if (t[c].size() != X.size(c)) return Verdict::no(claim, "its function at " + C.objects[c] + " is not defined on the whole set").with("at", C.objects[c]);
    for (Index y : t[c])
      if (y >= Y.size(c)) return Verdict::no(claim, "its function at " + C.objects[c] + " leaves the set").with("at", C.objects[c]);
  }
  std::size_t examined = 0;
  for (Index f = 0; f < C.size(); f++)
    for (Index x = 0; x < X.size(C.dom(f)); x++) {
      examined++;
      if (Y.action[f][t[C.dom(f)][x]] != t[C.cod(f)][X.action[f][x]])
        return Verdict::no(claim, "the square at " + C.arrows[f].name + " does not commute at " + X.elements[C.dom(f)][x], examined).with("at", C.arrows[f].name);
    }
  return Verdict::yes(claim, "the square at every arrow commutes, element by element", examined);
}

// Visits every natural transformation X ⇒ Y (visit returns false to stop); the number visited.
template <class Visit>
std::uint64_t for_each_transformation(const Category& C, const Copresheaf& X, const Copresheaf& Y, Visit visit) {
  const std::size_t m = C.objects.size();
  std::vector<std::vector<Index>> out(m);  // the arrows out of each object
  for (Index f = 0; f < C.size(); f++) out[C.dom(f)].push_back(f);
  Family t(m);
  for (Index c = 0; c < m; c++) t[c].assign(X.size(c), none);
  std::vector<std::pair<Index, Index>> trail;
  auto assign = [&](auto& self, Index c, Index x, Index y) -> bool {
    if (t[c][x] != none) return t[c][x] == y;
    t[c][x] = y, trail.push_back({c, x});
    for (Index f : out[c])
      if (!self(self, C.cod(f), X.action[f][x], Y.action[f][y])) return false;
    return true;
  };
  auto undo = [&](std::size_t mark) {
    for (; trail.size() > mark; trail.pop_back()) t[trail.back().first][trail.back().second] = none;
  };
  std::uint64_t count = 0;
  bool on = true;
  auto go = [&](auto& self, Index c, Index x) -> void {
    while (c < m && (x >= X.size(c) || t[c][x] != none)) {
      if (x >= X.size(c)) c++, x = 0;
      else x++;
    }
    if (c == m) {
      count++;
      on = visit(t);
      return;
    }
    for (Index y = 0; y < Y.size(c) && on; y++) {
      const std::size_t mark = trail.size();
      if (assign(assign, c, x, y)) self(self, c, x);
      undo(mark);
    }
  };
  go(go, 0, 0);
  return count;
}
inline std::uint64_t count_transformations(const Category& C, const Copresheaf& X, const Copresheaf& Y) {
  return for_each_transformation(C, X, Y, [](const Family&) { return true; });
}
inline std::vector<Family> all_transformations(const Category& C, const Copresheaf& X, const Copresheaf& Y) {
  std::vector<Family> out;
  for_each_transformation(C, X, Y, [&](const Family& t) { return out.push_back(t), true; });
  return out;
}

inline bool bijective(const Function& f, std::size_t onto) {
  if (f.size() != onto) return false;
  std::vector<char> hit(onto, 0);
  for (Index y : f)
    if (y >= onto || hit[y]++) return false;
  return true;
}

// A natural isomorphism X ≅ Y, when there is one.
inline std::optional<Family> isomorphism(const Category& C, const Copresheaf& X, const Copresheaf& Y) {
  for (Index c = 0; c < C.objects.size(); c++)
    if (X.size(c) != Y.size(c)) return std::nullopt;
  std::optional<Family> found;
  for_each_transformation(C, X, Y, [&](const Family& t) {
    for (Index c = 0; c < C.objects.size(); c++)
      if (!bijective(t[c], Y.size(c))) return true;
    found = t;
    return false;
  });
  return found;
}

// The Yoneda lemma at a: the natural transformations Hom(a, −) ⇒ X are in bijection with X(a), each sent to its
// value at the identity. Decided by listing the transformations.
inline Verdict yoneda(const Category& C, const Copresheaf& X, Index a) {
  const std::string claim = "the natural transformations Hom(" + C.objects[a] + ", −) ⇒ " + (X.name.empty() ? "X" : X.name) + " are the elements of " + (X.name.empty() ? "X" : X.name) + "(" + C.objects[a] + ")";
  const Copresheaf H = representable(C, a);
  Index one = none;  // the place of the identity among the arrows a → a
  for (Index k = 0, f = 0; f < C.size(); f++)
    if (C.dom(f) == a && C.cod(f) == a) {
      if (f == C.identity[a]) one = k;
      k++;
    }
  std::vector<std::size_t> hits(X.size(a), 0);
  const std::uint64_t count = for_each_transformation(C, H, X, [&](const Family& t) { return hits[t[a][one]]++, true; });
  for (Index x = 0; x < X.size(a); x++)
    if (hits[x] != 1)
      return Verdict::no(claim, X.elements[a][x] + " is the value at the identity of " + std::to_string(hits[x]) + " transformations", count).with("at", X.elements[a][x]);
  return Verdict::yes(claim, kernel::count(count, "transformation") + ", one for each element, each fixed by its value at the identity", count);
}

// ---- the category of elements -------------------------------------------------------------------------------------------------

// ∫X: its objects the (c, x) with x in X(c), its arrows (c, x) → (c′, X(f) x) the pairs (f, x).
struct Elements {
  Category category;
  Functor projection;                          // to C
  std::vector<std::pair<Index, Index>> objects; // (c, x)
};

inline Elements elements(const Category& C, const Copresheaf& X) {
  Elements E;
  std::vector<std::vector<Index>> place(C.objects.size());
  std::vector<std::string> names;
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index x = 0; x < X.size(c); x++) {
      place[c].push_back(static_cast<Index>(E.objects.size()));
      E.objects.push_back({c, x});
      names.push_back(X.elements[c][x]);
    }
  const Index m = static_cast<Index>(E.objects.size());
  std::vector<finite::Arrow> arrows;
  std::map<std::pair<Index, Index>, Index> at;  // (source object, arrow of C)
  E.projection = {"π", {}, {}};
  for (auto& [c, x] : E.objects) E.projection.objects.push_back(c);
  for (int pass = 0; pass < 2; pass++)
    for (Index o = 0; o < m; o++)
      for (Index f = 0; f < C.size(); f++) {
        const auto [c, x] = E.objects[o];
        if (C.dom(f) != c || C.is_identity(f) != (pass == 0)) continue;
        at[{o, f}] = static_cast<Index>(arrows.size());
        E.projection.arrows.push_back(f);
        arrows.push_back({pass == 0 ? "id_" + names[o] : C.arrows[f].name + "@" + names[o], o, place[C.cod(f)][X.action[f][x]]});
      }
  const auto under = E.projection.arrows;
  const auto ends = arrows;
  E.category = finite::assemble("∫" + (X.name.empty() ? "X" : X.name), std::move(names), std::move(arrows), finite::detail::iota(m),
                                [&](Index g, Index f) { return at.at({ends[f].dom, C.compose(under[g], under[f])}); });
  return E;
}

// ---- limits and colimits ------------------------------------------------------------------------------------------------------

// The limit of X: its sections, the choices of one element at each object that every arrow carries to one another.
inline std::vector<Function> sections(const Category& C, const Copresheaf& X) {
  std::vector<Function> out;
  for_each_transformation(C, constant(C, 1), X, [&](const Family& t) {
    Function s;
    for (auto& f : t) s.push_back(f[0]);
    return out.push_back(s), true;
  });
  return out;
}

// The colimit of X: the classes of the elements under x ~ X(f) x.
struct Classes {
  std::size_t count = 0;
  Family of;  // of[c][x]: the class of the element x of X(c)
};
inline Classes classes(const Category& C, const Copresheaf& X) {
  std::vector<Index> offset(C.objects.size() + 1, 0);
  for (Index c = 0; c < C.objects.size(); c++) offset[c + 1] = offset[c] + static_cast<Index>(X.size(c));
  std::vector<Index> parent = finite::detail::iota(offset.back());
  auto find = [&](Index a) {
    while (parent[a] != a) a = parent[a] = parent[parent[a]];
    return a;
  };
  for (Index f = 0; f < C.size(); f++)
    for (Index x = 0; x < X.size(C.dom(f)); x++) parent[find(offset[C.dom(f)] + x)] = find(offset[C.cod(f)] + X.action[f][x]);
  Classes K;
  std::vector<Index> label(offset.back(), none);
  K.of.resize(C.objects.size());
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index x = 0; x < X.size(c); x++) {
      const Index r = find(offset[c] + x);
      if (label[r] == none) label[r] = static_cast<Index>(K.count++);
      K.of[c].push_back(label[r]);
    }
  return K;
}

// ---- along a functor ----------------------------------------------------------------------------------------------------------

// The pullback of Y : D → FinSet along K : C → D: Y ∘ K.
inline Copresheaf pullback(const Functor& K, const Copresheaf& Y) {
  Copresheaf X{(Y.name.empty() ? "Y" : Y.name) + " ∘ " + (K.name.empty() ? "K" : K.name), {}, {}};
  for (Index d : K.objects) X.elements.push_back(Y.elements[d]);
  for (Index h : K.arrows) X.action.push_back(Y.action[h]);
  return X;
}

// A Kan extension with the transformation that makes it universal.
struct Kan {
  Copresheaf extension;  // on D
  Family comparison;     // left: the unit X ⇒ (Lan X) ∘ K; right: the counit (Ran X) ∘ K ⇒ X
};

// The left Kan extension of X along K, pointwise: (Lan X)(d) is the colimit of X over the arrows K c → d, the classes
// of the (c, h : K c → d, x) under (c, h′ ∘ K f, x) ~ (c′, h′, X(f) x).
inline Kan left_kan(const Category& C, const Category& D, const Functor& K, const Copresheaf& X) {
  Kan R;
  R.extension = {"Lan " + (X.name.empty() ? "X" : X.name), std::vector<std::vector<std::string>>(D.objects.size()), std::vector<Function>(D.size())};
  // The triples at d, numbered: place[d][(c, h, x)].
  std::vector<std::map<std::array<Index, 3>, Index>> place(D.objects.size());
  std::vector<std::vector<Index>> cls(D.objects.size());  // the class of each triple
  for (Index d = 0; d < D.objects.size(); d++) {
    std::vector<std::array<Index, 3>> triples;
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index h : D.hom(K.objects[c], d))
        for (Index x = 0; x < X.size(c); x++) place[d][{c, h, x}] = static_cast<Index>(triples.size()), triples.push_back({c, h, x});
    std::vector<Index> parent = finite::detail::iota(triples.size());
    auto find = [&](Index a) {
      while (parent[a] != a) a = parent[a] = parent[parent[a]];
      return a;
    };
    for (Index f = 0; f < C.size(); f++)
      for (Index h : D.hom(K.objects[C.cod(f)], d))
        for (Index x = 0; x < X.size(C.dom(f)); x++)
          parent[find(place[d].at({C.dom(f), D.compose(h, K.arrows[f]), x}))] = find(place[d].at({C.cod(f), h, X.action[f][x]}));
    std::vector<Index> label(triples.size(), none);
    cls[d].resize(triples.size());
    for (Index k = 0; k < triples.size(); k++) {
      const Index r = find(k);
      if (label[r] == none) {
        label[r] = static_cast<Index>(R.extension.elements[d].size());
        const auto& [c, h, x] = triples[r];
        R.extension.elements[d].push_back(D.is_identity(h) ? "⟨" + X.elements[c][x] + "⟩" : "⟨" + X.elements[c][x] + "," + D.arrows[h].name + "⟩");
      }
      cls[d][k] = label[r];
    }
  }
  for (Index g = 0; g < D.size(); g++) {
    R.extension.action[g].assign(R.extension.size(D.dom(g)), none);
    for (const auto& [triple, k] : place[D.dom(g)])
      R.extension.action[g][cls[D.dom(g)][k]] = cls[D.cod(g)][place[D.cod(g)].at({triple[0], D.compose(g, triple[1]), triple[2]})];
  }
  R.comparison.resize(C.objects.size());
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index x = 0; x < X.size(c); x++) R.comparison[c].push_back(cls[K.objects[c]][place[K.objects[c]].at({c, D.identity[K.objects[c]], x})]);
  return R;
}

// The right Kan extension of X along K, pointwise: (Ran X)(d) is the limit of X over the arrows d → K c, the families
// s(c, h) in X(c) with X(f) s(c, h) = s(c′, K f ∘ h). Throws std::length_error past `most` families at an object.
inline Kan right_kan(const Category& C, const Category& D, const Functor& K, const Copresheaf& X, std::size_t most = 20000) {
  Kan R;
  R.extension = {"Ran " + (X.name.empty() ? "X" : X.name), std::vector<std::vector<std::string>>(D.objects.size()), std::vector<Function>(D.size())};
  std::vector<std::vector<std::pair<Index, Index>>> index(D.objects.size());  // the (c, h : d → K c) at d
  std::vector<std::map<std::pair<Index, Index>, Index>> place(D.objects.size());
  std::vector<std::vector<Function>> families(D.objects.size());
  std::vector<std::map<Function, Index>> family_at(D.objects.size());
  for (Index d = 0; d < D.objects.size(); d++) {
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index h : D.hom(d, K.objects[c])) place[d][{c, h}] = static_cast<Index>(index[d].size()), index[d].push_back({c, h});
    const std::size_t n = index[d].size();
    Function s(n, none);
    std::vector<Index> trail;
    auto assign = [&](auto& self, Index k, Index x) -> bool {
      if (s[k] != none) return s[k] == x;
      s[k] = x, trail.push_back(k);
      const auto [c, h] = index[d][k];
      for (Index f = 0; f < C.size(); f++)
        if (C.dom(f) == c && !self(self, place[d].at({C.cod(f), D.compose(K.arrows[f], h)}), X.action[f][x])) return false;
      return true;
    };
    auto go = [&](auto& self, Index k) -> void {
      while (k < n && s[k] != none) k++;
      if (k == n) {
        if (families[d].size() >= most) throw std::length_error("kategoria::sets::right_kan: more than " + std::to_string(most) + " families at " + D.objects[d]);
        family_at[d][s] = static_cast<Index>(families[d].size());
        families[d].push_back(s);
        return;
      }
      for (Index x = 0; x < X.size(index[d][k].first); x++) {
        const std::size_t mark = trail.size();
        if (assign(assign, k, x)) self(self, k);
        for (; trail.size() > mark; trail.pop_back()) s[trail.back()] = none;
      }
    };
    go(go, 0);
    for (const auto& family : families[d]) {
      std::string w = "(";
      for (std::size_t k = 0; k < n; k++) w += (k ? "," : "") + X.elements[index[d][k].first][family[k]];
      R.extension.elements[d].push_back(w + ")");
    }
  }
  for (Index g = 0; g < D.size(); g++) {
    const Index d = D.dom(g), e = D.cod(g);
    for (const auto& family : families[d]) {
      Function moved(index[e].size());
      for (std::size_t k = 0; k < index[e].size(); k++) moved[k] = family[place[d].at({index[e][k].first, D.compose(index[e][k].second, g)})];
      R.extension.action[g].push_back(family_at[e].at(moved));
    }
  }
  R.comparison.resize(C.objects.size());
  for (Index c = 0; c < C.objects.size(); c++) {
    const Index d = K.objects[c], k = place[d].at({c, D.identity[d]});
    for (const auto& family : families[d]) R.comparison[c].push_back(family[k]);
  }
  return R;
}

// The universal property of a left Kan extension, for one Y : D → FinSet: β ↦ (β K) ∘ unit is a bijection from the
// transformations Lan X ⇒ Y to the transformations X ⇒ Y ∘ K. Decided by listing both.
inline Verdict left_kan_universal(const Category& C, const Category& D, const Functor& K, const Copresheaf& X, const Kan& L, const Copresheaf& Y) {
  const std::string claim = "the transformations " + L.extension.name + " ⇒ " + (Y.name.empty() ? "Y" : Y.name) + " are those " + (X.name.empty() ? "X" : X.name) + " ⇒ " + (Y.name.empty() ? "Y" : Y.name) + " ∘ " + (K.name.empty() ? "K" : K.name) + ", through the unit";
  const Copresheaf YK = pullback(K, Y);
  if (Verdict v = kernel::both(verify(D, L.extension), natural(C, X, pullback(K, L.extension), L.comparison)); !v.holds()) return Verdict::no(claim, v.claim + " fails: " + v.reason);
  std::map<Family, std::size_t> hits;
  for (auto& t : all_transformations(C, X, YK)) hits[t] = 0;
  const std::size_t below = hits.size();
  bool landed = true;
  const std::uint64_t above = for_each_transformation(D, L.extension, Y, [&](const Family& beta) {
    Family t(C.objects.size());
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index x = 0; x < X.size(c); x++) t[c].push_back(beta[K.objects[c]][L.comparison[c][x]]);
    const auto it = hits.find(t);
    if (it == hits.end()) return landed = false;
    return it->second++, true;
  });
  if (!landed) return Verdict::no(claim, "a transformation composed with the unit is not natural", above);
  for (auto& [t, k] : hits)
    if (k != 1) return Verdict::no(claim, "a transformation " + (X.name.empty() ? "X" : X.name) + " ⇒ " + YK.name + " comes from " + std::to_string(k) + " transformations out of the extension", above + below);
  return Verdict::yes(claim, std::to_string(above) + " transformations on each side, matched one to one", above + below);
}

// The universal property of a right Kan extension, for one Y: β ↦ counit ∘ (β K) is a bijection from the
// transformations Y ⇒ Ran X to the transformations Y ∘ K ⇒ X.
inline Verdict right_kan_universal(const Category& C, const Category& D, const Functor& K, const Copresheaf& X, const Kan& R, const Copresheaf& Y) {
  const std::string claim = "the transformations " + (Y.name.empty() ? "Y" : Y.name) + " ⇒ " + R.extension.name + " are those " + (Y.name.empty() ? "Y" : Y.name) + " ∘ " + (K.name.empty() ? "K" : K.name) + " ⇒ " + (X.name.empty() ? "X" : X.name) + ", through the counit";
  const Copresheaf YK = pullback(K, Y);
  if (Verdict v = kernel::both(verify(D, R.extension), natural(C, pullback(K, R.extension), X, R.comparison)); !v.holds()) return Verdict::no(claim, v.claim + " fails: " + v.reason);
  std::map<Family, std::size_t> hits;
  for (auto& t : all_transformations(C, YK, X)) hits[t] = 0;
  const std::size_t below = hits.size();
  bool landed = true;
  const std::uint64_t above = for_each_transformation(D, Y, R.extension, [&](const Family& beta) {
    Family t(C.objects.size());
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index y = 0; y < YK.size(c); y++) t[c].push_back(R.comparison[c][beta[K.objects[c]][y]]);
    const auto it = hits.find(t);
    if (it == hits.end()) return landed = false;
    return it->second++, true;
  });
  if (!landed) return Verdict::no(claim, "the counit composed with a transformation is not natural", above);
  for (auto& [t, k] : hits)
    if (k != 1) return Verdict::no(claim, "a transformation " + YK.name + " ⇒ " + (X.name.empty() ? "X" : X.name) + " comes from " + std::to_string(k) + " transformations into the extension", above + below);
  return Verdict::yes(claim, std::to_string(above) + " transformations on each side, matched one to one", above + below);
}

// ---- subobjects and their classifier ------------------------------------------------------------------------------------------

using Marks = std::vector<char>;

// The classifier of subobjects of [C, FinSet]: Ω(c) is the set of cosieves on c (sets of arrows out of c closed under
// composition on the left), and u : c → c′ sends S to { g | g ∘ u in S }.
struct Classifier {
  Copresheaf omega;
  std::vector<std::vector<Marks>> sieves;  // sieves[c][k]: the cosieve as a mark on each arrow of C
  std::vector<Index> truth;                // truth[c]: the cosieve of every arrow out of c
};

// Throws std::length_error past `most` cosieves on an object.
inline Classifier classifier(const Category& C, std::size_t most = 4096) {
  Classifier K;
  const std::size_t n = C.size();
  K.omega = {"Ω", std::vector<std::vector<std::string>>(C.objects.size()), std::vector<Function>(C.size())};
  K.sieves.resize(C.objects.size()), K.truth.assign(C.objects.size(), none);
  std::vector<std::map<Marks, Index>> at(C.objects.size());
  auto principal = [&](Index f) {  // every g ∘ f
    Marks S(n, 0);
    for (Index g = 0; g < n; g++)
      if (C.dom(g) == C.cod(f)) S[C.compose(g, f)] = 1;
    return S;
  };
  for (Index c = 0; c < C.objects.size(); c++) {
    std::vector<Marks> up;
    std::vector<Index> out;
    for (Index f = 0; f < n; f++)
      if (C.dom(f) == c) out.push_back(f), up.push_back(principal(f));
    // Every cosieve is a union of principal ones: close the empty one under adding them.
    std::set<Marks> seen{Marks(n, 0)};
    std::vector<Marks> all{Marks(n, 0)};
    for (std::size_t k = 0; k < all.size(); k++)
      for (auto& p : up) {
        Marks S = all[k];
        for (std::size_t i = 0; i < n; i++) S[i] |= p[i];
        if (seen.insert(S).second) {
          if (all.size() >= most) throw std::length_error("kategoria::sets::classifier: more than " + std::to_string(most) + " cosieves on " + C.objects[c]);
          all.push_back(S);
        }
      }
    std::sort(all.begin(), all.end(), [](const Marks& a, const Marks& b) {
      const auto na = std::count(a.begin(), a.end(), 1), nb = std::count(b.begin(), b.end(), 1);
      return na != nb ? na < nb : a < b;
    });
    for (Index k = 0; k < all.size(); k++) {
      const Marks& S = all[k];
      at[c][S] = k;
      std::string w;
      if (S[C.identity[c]]) {
        w = "⊤", K.truth[c] = k;
      } else if (std::count(S.begin(), S.end(), 1) == 0) {
        w = "∅";
      } else {  // by the arrows that generate it: those in no other's principal cosieve
        for (std::size_t i = 0; i < out.size(); i++) {
          if (!S[out[i]]) continue;
          bool least = true;
          for (std::size_t j = 0; j < out.size() && least; j++)
            if (j != i && S[out[j]] && up[j][out[i]] && !(up[i][out[j]] && i < j)) least = false;
          if (least) w += (w.empty() ? "↑" : "∪↑") + C.arrows[out[i]].name;
        }
      }
      K.omega.elements[c].push_back(w);
    }
    K.sieves[c] = std::move(all);
  }
  for (Index u = 0; u < n; u++)
    for (const Marks& S : K.sieves[C.dom(u)]) {
      Marks T(n, 0);
      for (Index g = 0; g < n; g++)
        if (C.dom(g) == C.cod(u) && S[C.compose(g, u)]) T[g] = 1;
      K.omega.action[u].push_back(at[C.cod(u)].at(T));
    }
  return K;
}

// A subfunctor of X: a mark on each element, kept by every arrow.
using Subfunctor = std::vector<Marks>;

// Every subfunctor of X, the least first. Throws std::length_error past `most`.
inline std::vector<Subfunctor> subfunctors(const Category& C, const Copresheaf& X, std::size_t most = 4096) {
  Subfunctor empty(C.objects.size());
  for (Index c = 0; c < C.objects.size(); c++) empty[c].assign(X.size(c), 0);
  std::vector<Subfunctor> orbit;  // the least subfunctor holding each element
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index x = 0; x < X.size(c); x++) {
      Subfunctor S = empty;
      for (Index f = 0; f < C.size(); f++)
        if (C.dom(f) == c) S[C.cod(f)][X.action[f][x]] = 1;
      orbit.push_back(S);
    }
  std::set<Subfunctor> seen{empty};
  std::vector<Subfunctor> all{empty};
  for (std::size_t k = 0; k < all.size(); k++)
    for (auto& o : orbit) {
      Subfunctor S = all[k];
      for (Index c = 0; c < C.objects.size(); c++)
        for (Index x = 0; x < X.size(c); x++) S[c][x] |= o[c][x];
      if (seen.insert(S).second) {
        if (all.size() >= most) throw std::length_error("kategoria::sets::subfunctors: more than " + std::to_string(most) + " subfunctors");
        all.push_back(S);
      }
    }
  auto weight = [](const Subfunctor& S) {
    std::size_t w = 0;
    for (auto& m : S) w += std::count(m.begin(), m.end(), 1);
    return w;
  };
  std::sort(all.begin(), all.end(), [&](const Subfunctor& a, const Subfunctor& b) { return weight(a) != weight(b) ? weight(a) < weight(b) : a < b; });
  return all;
}

// The characteristic map X ⇒ Ω of a subfunctor: x ↦ { f | X(f) x in S }.
inline Family characteristic(const Category& C, const Copresheaf& X, const Subfunctor& S, const Classifier& K) {
  Family chi(C.objects.size());
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index x = 0; x < X.size(c); x++) {
      Marks sieve(C.size(), 0);
      for (Index f = 0; f < C.size(); f++)
        if (C.dom(f) == c && S[C.cod(f)][X.action[f][x]]) sieve[f] = 1;
      const auto it = std::find(K.sieves[c].begin(), K.sieves[c].end(), sieve);
      chi[c].push_back(static_cast<Index>(it - K.sieves[c].begin()));
    }
  return chi;
}

// Ω classifies: the subfunctors of X and the transformations X ⇒ Ω are matched one to one by the characteristic map,
// and each subfunctor is what its map sends to "true". Decided by listing both.
inline Verdict classifies(const Category& C, const Copresheaf& X, const Classifier& K) {
  const std::string claim = "the subfunctors of " + (X.name.empty() ? "X" : X.name) + " are the transformations " + (X.name.empty() ? "X" : X.name) + " ⇒ Ω";
  const auto subs = subfunctors(C, X);
  std::map<Family, std::size_t> hits;
  for (auto& t : all_transformations(C, X, K.omega)) hits[t] = 0;
  for (auto& S : subs) {
    const Family chi = characteristic(C, X, S, K);
    const auto it = hits.find(chi);
    if (it == hits.end()) return Verdict::no(claim, "a characteristic map is not natural", subs.size());
    it->second++;
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index x = 0; x < X.size(c); x++)
        if ((chi[c][x] == K.truth[c]) != static_cast<bool>(S[c][x])) return Verdict::no(claim, "a subfunctor is not what its characteristic map sends to true", subs.size());
  }
  for (auto& [t, k] : hits)
    if (k != 1) return Verdict::no(claim, "a transformation to Ω is the characteristic map of " + std::to_string(k) + " subfunctors", subs.size() + hits.size());
  return Verdict::yes(claim, std::to_string(subs.size()) + " subfunctors and as many transformations, matched one to one", subs.size() + hits.size());
}

// The subfunctors of X under inclusion, as a category: a Heyting algebra.
inline Category subobjects(const Category& C, const Copresheaf& X) {
  const auto subs = subfunctors(C, X);
  std::vector<std::string> names;
  for (std::size_t k = 0; k < subs.size(); k++) {
    std::string w;
    for (Index c = 0; c < C.objects.size(); c++)
      for (Index x = 0; x < X.size(c); x++)
        if (subs[k][c][x]) w += (w.empty() ? "" : " ") + X.elements[c][x];
    names.push_back(w.empty() ? "∅" : "{" + w + "}");
  }
  std::vector<std::vector<char>> leq(subs.size(), std::vector<char>(subs.size(), 1));
  for (std::size_t a = 0; a < subs.size(); a++)
    for (std::size_t b = 0; b < subs.size(); b++)
      for (Index c = 0; c < C.objects.size(); c++)
        for (Index x = 0; x < X.size(c); x++)
          if (subs[a][c][x] && !subs[b][c][x]) leq[a][b] = 0;
  return finite::preorder(std::move(names), leq, "Sub(" + (X.name.empty() ? "X" : X.name) + ")");
}

}  // namespace kategoria::sets
