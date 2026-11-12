// Finite categories, given whole: every object, every arrow and the composite of every composable pair.
//
// A finite category is held as its table of composition, as a finite group is held as its table (Mac Lane 1971, I.1).
// Whether such a table is a category is a claim, answered by validate() with the place where an axiom fails. Every
// claim about a finite category is then decided by examining its instances.
//
// Conventions.
// - compose(g, f) is g ∘ f, "g after f", defined exactly when cod f = dom g.
// - An arrow has a name for those who read it; nothing computes with names.
// - In the categories built here the identities come first, identity[a] = a, unless said otherwise.

#pragma once

#include <kategoria/kernel/verdict.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

namespace kategoria::finite {

using Index = std::uint32_t;
inline constexpr Index none = std::numeric_limits<Index>::max();
using kernel::Verdict;

struct Arrow {
  std::string name;
  Index dom = 0, cod = 0;
};

struct Category {
  std::string name;
  std::vector<std::string> objects;
  std::vector<Arrow> arrows;    // every arrow, the identities among them
  std::vector<Index> identity;  // identity[a]: the identity of the object a
  std::vector<Index> table;     // table[g n + f] = g ∘ f, or none when cod f ≠ dom g
  std::vector<Index> basis;     // arrows that generate it, where its construction knows a natural choice (else empty)

  std::size_t size() const { return arrows.size(); }
  Index dom(Index f) const { return arrows[f].dom; }
  Index cod(Index f) const { return arrows[f].cod; }
  Index compose(Index g, Index f) const { return table[static_cast<std::size_t>(g) * arrows.size() + f]; }
  bool is_identity(Index f) const { return identity[arrows[f].dom] == f; }

  std::vector<Index> hom(Index a, Index b) const {
    std::vector<Index> out;
    for (Index f = 0; f < arrows.size(); f++)
      if (arrows[f].dom == a && arrows[f].cod == b) out.push_back(f);
    return out;
  }
  Index object(std::string_view n) const {
    for (Index a = 0; a < objects.size(); a++)
      if (objects[a] == n) return a;
    return none;
  }
  Index arrow(std::string_view n) const {
    for (Index f = 0; f < arrows.size(); f++)
      if (arrows[f].name == n) return f;
    return none;
  }
  // "f : A → B"
  std::string typed(Index f) const { return arrows[f].name + " : " + objects[arrows[f].dom] + " → " + objects[arrows[f].cod]; }
};

// The category of these objects and arrows whose composites are compose(g, f), asked for composable pairs only.
template <class Compose>
Category assemble(std::string name, std::vector<std::string> objects, std::vector<Arrow> arrows, std::vector<Index> identity, Compose compose) {
  Category C{std::move(name), std::move(objects), std::move(arrows), std::move(identity), {}, {}};
  const std::size_t n = C.arrows.size();
  C.table.assign(n * n, none);
  for (Index g = 0; g < n; g++)
    for (Index f = 0; f < n; f++)
      if (C.arrows[f].cod == C.arrows[g].dom) C.table[static_cast<std::size_t>(g) * n + f] = compose(g, f);
  return C;
}

// Whether the table is a category: the types of composites, the identities' laws, associativity; with the place where it fails.
inline Verdict validate(const Category& C) {
  const std::string claim = C.name + " is a category";
  const std::size_t n = C.arrows.size(), m = C.objects.size();
  if (C.identity.size() != m || C.table.size() != n * n) return Verdict::no(claim, "its identities or its table are not of the size of its objects and arrows");
  for (Index f = 0; f < n; f++)
    if (C.dom(f) >= m || C.cod(f) >= m) return Verdict::no(claim, "the arrow " + C.arrows[f].name + " begins or ends at no object");
  for (Index a = 0; a < m; a++)
    if (C.identity[a] >= n || C.dom(C.identity[a]) != a || C.cod(C.identity[a]) != a)
      return Verdict::no(claim, "the identity of " + C.objects[a] + " is not an arrow from it to itself").with("at", C.objects[a]);
  std::size_t examined = 0;
  for (Index g = 0; g < n; g++)
    for (Index f = 0; f < n; f++) {
      const Index h = C.compose(g, f);
      if (C.cod(f) != C.dom(g)) {
        if (h != none) return Verdict::no(claim, C.arrows[g].name + " ∘ " + C.arrows[f].name + " is given, yet the two do not meet");
        continue;
      }
      examined++;
      if (h >= n) return Verdict::no(claim, C.arrows[g].name + " ∘ " + C.arrows[f].name + " is not given").with("at", C.arrows[g].name + ", " + C.arrows[f].name);
      if (C.dom(h) != C.dom(f) || C.cod(h) != C.cod(g))
        return Verdict::no(claim, C.arrows[g].name + " ∘ " + C.arrows[f].name + " = " + C.arrows[h].name + " does not run from the first's source to the second's target");
    }
  for (Index f = 0; f < n; f++) {
    if (C.compose(f, C.identity[C.dom(f)]) != f)
      return Verdict::no(claim, "the right identity law fails at " + C.arrows[f].name).with("at", C.arrows[f].name).with("left", C.arrows[C.compose(f, C.identity[C.dom(f)])].name).with("right", C.arrows[f].name);
    if (C.compose(C.identity[C.cod(f)], f) != f)
      return Verdict::no(claim, "the left identity law fails at " + C.arrows[f].name).with("at", C.arrows[f].name).with("left", C.arrows[C.compose(C.identity[C.cod(f)], f)].name).with("right", C.arrows[f].name);
  }
  for (Index f = 0; f < n; f++)
    for (Index g = 0; g < n; g++) {
      if (C.cod(f) != C.dom(g)) continue;
      const Index gf = C.compose(g, f);
      for (Index h = 0; h < n; h++) {
        if (C.cod(g) != C.dom(h)) continue;
        examined++;
        const Index left = C.compose(h, gf), right = C.compose(C.compose(h, g), f);
        if (left != right)
          return Verdict::no(claim, "composition is not associative at " + C.arrows[h].name + ", " + C.arrows[g].name + ", " + C.arrows[f].name)
              .with("at", C.arrows[h].name + ", " + C.arrows[g].name + ", " + C.arrows[f].name)
              .with("left", C.arrows[h].name + " ∘ (" + C.arrows[g].name + " ∘ " + C.arrows[f].name + ") = " + C.arrows[left].name)
              .with("right", "(" + C.arrows[h].name + " ∘ " + C.arrows[g].name + ") ∘ " + C.arrows[f].name + " = " + C.arrows[right].name);
      }
    }
  return Verdict::yes(claim, kernel::count(m, "object") + ", " + kernel::count(n, "arrow") + "; the identities' laws and associativity hold at every instance", examined);
}

// ---- families -----------------------------------------------------------------------------------------------------------------

namespace detail {
inline std::vector<Arrow> identities(const std::vector<std::string>& objects) {
  std::vector<Arrow> arrows;
  for (Index a = 0; a < objects.size(); a++) arrows.push_back({"id_" + objects[a], a, a});
  return arrows;
}
inline std::vector<Index> iota(std::size_t n) {
  std::vector<Index> v(n);
  std::iota(v.begin(), v.end(), Index{0});
  return v;
}
inline std::vector<std::string> numbered(std::size_t n, const std::string& prefix = "") {
  std::vector<std::string> names;
  for (std::size_t i = 0; i < n; i++) names.push_back(prefix + std::to_string(i));
  return names;
}
}  // namespace detail

// The discrete category on these objects: identities only.
inline Category discrete(std::vector<std::string> objects, std::string name = "discrete") {
  auto arrows = detail::identities(objects);
  auto id = detail::iota(objects.size());
  return assemble(std::move(name), std::move(objects), std::move(arrows), std::move(id), [](Index g, Index) { return g; });
}
inline Category discrete(std::size_t n) { return discrete(detail::numbered(n), "discrete " + std::to_string(n)); }

// A preorder as a category: one arrow a → b exactly when leq[a][b]. Throws unless leq is reflexive and transitive.
inline Category preorder(std::vector<std::string> objects, const std::vector<std::vector<char>>& leq, std::string name = "preorder") {
  const std::size_t m = objects.size();
  for (std::size_t a = 0; a < m; a++) {
    if (!leq[a][a]) throw std::invalid_argument("kategoria::finite::preorder: the relation is not reflexive at " + objects[a]);
    for (std::size_t b = 0; b < m; b++)
      for (std::size_t c = 0; c < m; c++)
        if (leq[a][b] && leq[b][c] && !leq[a][c]) throw std::invalid_argument("kategoria::finite::preorder: the relation is not transitive at " + objects[a] + ", " + objects[b] + ", " + objects[c]);
  }
  auto arrows = detail::identities(objects);
  std::vector<std::vector<Index>> at(m, std::vector<Index>(m, none));
  for (Index a = 0; a < m; a++) at[a][a] = a;
  for (Index a = 0; a < m; a++)
    for (Index b = 0; b < m; b++)
      if (a != b && leq[a][b]) {
        at[a][b] = static_cast<Index>(arrows.size());
        arrows.push_back({objects[a] + "≤" + objects[b], a, b});
      }
  const auto ends = arrows;
  Category C = assemble(std::move(name), std::move(objects), std::move(arrows), detail::iota(m), [&](Index g, Index f) { return at[ends[f].dom][ends[g].cod]; });
  // A partial order is generated by its covers: a < b with nothing strictly between.
  bool partial = true;
  for (std::size_t a = 0; a < m; a++)
    for (std::size_t b = a + 1; b < m; b++) partial = partial && !(leq[a][b] && leq[b][a]);
  if (partial)
    for (Index f = static_cast<Index>(m); f < C.size(); f++) {
      bool cover = true;
      for (std::size_t c = 0; c < m && cover; c++) cover = c == C.dom(f) || c == C.cod(f) || !(leq[C.dom(f)][c] && leq[c][C.cod(f)]);
      if (cover) C.basis.push_back(f);
    }
  return C;
}

// The ordinal n: 0 ≤ 1 ≤ … ≤ n − 1.
inline Category chain(std::size_t n) {
  std::vector<std::vector<char>> leq(n, std::vector<char>(n, 0));
  for (std::size_t a = 0; a < n; a++)
    for (std::size_t b = a; b < n; b++) leq[a][b] = 1;
  return preorder(detail::numbered(n), leq, "chain " + std::to_string(n));
}

// The divisors of n under divisibility: a lattice, its meets the greatest common divisors.
inline Category divisors(std::uint64_t n) {
  std::vector<std::uint64_t> d;
  for (std::uint64_t k = 1; k <= n; k++)
    if (n % k == 0) d.push_back(k);
  std::vector<std::string> names;
  for (auto k : d) names.push_back(std::to_string(k));
  std::vector<std::vector<char>> leq(d.size(), std::vector<char>(d.size(), 0));
  for (std::size_t a = 0; a < d.size(); a++)
    for (std::size_t b = 0; b < d.size(); b++) leq[a][b] = d[b] % d[a] == 0;
  return preorder(std::move(names), leq, "divisors " + std::to_string(n));
}

// The subsets of an n-element set under inclusion: a Boolean algebra. The subset with mask s is object s.
inline Category subsets(std::size_t n) {
  if (n > 5) throw std::invalid_argument("kategoria::finite::subsets: at most 5 elements");
  const std::size_t m = std::size_t{1} << n;
  std::vector<std::string> names;
  for (std::size_t s = 0; s < m; s++) {
    std::string w;
    for (std::size_t i = 0; i < n; i++)
      if (s >> i & 1) w += static_cast<char>('a' + i);
    names.push_back(w.empty() ? "∅" : w);
  }
  std::vector<std::vector<char>> leq(m, std::vector<char>(m, 0));
  for (std::size_t a = 0; a < m; a++)
    for (std::size_t b = 0; b < m; b++) leq[a][b] = (a & b) == a;
  return preorder(std::move(names), leq, "subsets " + std::to_string(n));
}

// A monoid as a category with one object: table[a n + b] = a b. Throws unless one element is a two-sided identity.
inline Category monoid(std::vector<std::string> elements, const std::vector<Index>& table, std::string name = "monoid") {
  const std::size_t n = elements.size();
  if (table.size() != n * n) throw std::invalid_argument("kategoria::finite::monoid: the table is not n × n");
  Index e = none;
  for (Index a = 0; a < n && e == none; a++) {
    bool unit = true;
    for (Index b = 0; b < n && unit; b++) unit = table[a * n + b] == b && table[b * n + a] == b;
    if (unit) e = a;
  }
  if (e == none) throw std::invalid_argument("kategoria::finite::monoid: no element is an identity");
  std::vector<Arrow> arrows;
  for (auto& w : elements) arrows.push_back({std::move(w), 0, 0});
  return assemble(std::move(name), {"∗"}, std::move(arrows), {e}, [&](Index g, Index f) { return table[g * n + f]; });
}

// The integers modulo n under multiplication, a monoid with one object.
inline Category multiplicative(std::size_t n) {
  std::vector<Index> table(n * n);
  for (std::size_t a = 0; a < n; a++)
    for (std::size_t b = 0; b < n; b++) table[a * n + b] = static_cast<Index>(a * b % n);
  return monoid(detail::numbered(n), table, "(ℤ/" + std::to_string(n) + ", ×)");
}

// A group given by its table (element 0 the identity), as a category with one object in which every arrow is invertible.
inline Category group(std::size_t n, const std::vector<std::uint32_t>& table, std::string name, std::vector<std::string> elements = {}) {
  if (elements.empty()) {
    elements = detail::numbered(n, "g");
    elements[0] = "e";
  }
  return monoid(std::move(elements), std::vector<Index>(table.begin(), table.end()), std::move(name));
}

// A category of functions between finite sets: the arrows listed, composed as functions. Throws unless the list holds
// every identity and every composite.
struct Map {
  Index dom = 0, cod = 0;
  std::vector<Index> values;  // values[x]: the image of x
  std::string name;
};
inline Category concrete(std::string name, std::vector<std::string> objects, const std::vector<std::size_t>& sizes, std::vector<Map> maps) {
  // Identities first.
  std::stable_partition(maps.begin(), maps.end(), [&](const Map& f) { return f.dom == f.cod && f.values == detail::iota(sizes[f.dom]); });
  std::map<std::tuple<Index, Index, std::vector<Index>>, Index> at;
  std::vector<Arrow> arrows;
  std::vector<Index> identity(objects.size(), none);
  for (Index k = 0; k < maps.size(); k++) {
    const Map& f = maps[k];
    if (f.values.size() != sizes[f.dom]) throw std::invalid_argument("kategoria::finite::concrete: a function is not defined on its whole domain");
    if (!at.emplace(std::make_tuple(f.dom, f.cod, f.values), k).second) throw std::invalid_argument("kategoria::finite::concrete: a function is listed twice");
    if (f.dom == f.cod && f.values == detail::iota(sizes[f.dom])) identity[f.dom] = k;
    arrows.push_back({f.name, f.dom, f.cod});
  }
  for (Index a = 0; a < objects.size(); a++)
    if (identity[a] == none) throw std::invalid_argument("kategoria::finite::concrete: the identity of " + objects[a] + " is not listed");
  return assemble(std::move(name), std::move(objects), std::move(arrows), std::move(identity), [&](Index g, Index f) {
    std::vector<Index> v(maps[f].values.size());
    for (std::size_t x = 0; x < v.size(); x++) v[x] = maps[g].values[maps[f].values[x]];
    const auto it = at.find(std::make_tuple(maps[f].dom, maps[g].cod, v));
    if (it == at.end()) throw std::invalid_argument("kategoria::finite::concrete: the list is not closed under composition");
    return it->second;
  });
}

namespace detail {
inline std::string map_name(const std::string& from, const std::string& to, const std::vector<Index>& values, bool identity) {
  if (identity) return "id_" + from;
  std::string w = "[" + from + "→" + to + "|";
  for (auto v : values) w += std::to_string(v);
  return w + "]";
}
// Every function (or every monotone function) from m to k.
inline void functions(std::size_t m, std::size_t k, bool monotone, std::vector<std::vector<Index>>& out) {
  std::vector<Index> v(m, 0);
  if (k == 0) {
    if (m == 0) out.push_back({});
    return;
  }
  while (true) {
    bool ok = true;
    if (monotone)
      for (std::size_t i = 1; i < m && ok; i++) ok = v[i - 1] <= v[i];
    if (ok) out.push_back(v);
    std::size_t i = m;
    while (i > 0 && v[i - 1] + 1 == k) v[--i] = 0;
    if (i == 0) break;
    v[i - 1]++;
  }
}
}  // namespace detail

// The finite sets 0, 1, …, n (the set k has the elements 0 … k − 1) and every function between them: the full
// subcategory of FinSet on its first n + 1 objects, of Σ k^m arrows.
inline Category finset(std::size_t n) {
  if (n > 3) throw std::invalid_argument("kategoria::finite::finset: sets of at most 3 elements");
  std::vector<std::string> objects = detail::numbered(n + 1);
  std::vector<std::size_t> sizes(n + 1);
  std::iota(sizes.begin(), sizes.end(), std::size_t{0});
  std::vector<Map> maps;
  for (Index m = 0; m <= n; m++)
    for (Index k = 0; k <= n; k++) {
      std::vector<std::vector<Index>> all;
      detail::functions(m, k, false, all);
      for (auto& v : all) {
        const bool id = m == k && v == detail::iota(m);
        maps.push_back({m, k, v, detail::map_name(objects[m], objects[k], v, id)});
      }
    }
  return concrete("FinSet≤" + std::to_string(n), std::move(objects), sizes, std::move(maps));
}

// The simplex category up to [n]: the ordinals [0], …, [n] ([k] has k + 1 elements) and the monotone functions.
inline Category simplex(std::size_t n) {
  if (n > 3) throw std::invalid_argument("kategoria::finite::simplex: ordinals up to [3]");
  std::vector<std::string> objects;
  std::vector<std::size_t> sizes;
  for (std::size_t k = 0; k <= n; k++) objects.push_back("[" + std::to_string(k) + "]"), sizes.push_back(k + 1);
  std::vector<Map> maps;
  std::vector<std::string> basis;  // the faces (injections [k − 1] → [k]) and the degeneracies (surjections [k + 1] → [k])
  for (Index m = 0; m <= n; m++)
    for (Index k = 0; k <= n; k++) {
      std::vector<std::vector<Index>> all;
      detail::functions(m + 1, k + 1, true, all);
      for (auto& v : all) {
        const bool id = m == k && v == detail::iota(m + 1);
        maps.push_back({m, k, v, detail::map_name(std::to_string(m), std::to_string(k), v, id)});
        const std::size_t distinct = static_cast<std::size_t>(std::unique(v.begin(), v.end()) - v.begin());
        if ((k == m + 1 && distinct == m + 1) || (m == k + 1 && distinct == k + 1)) basis.push_back(maps.back().name);
      }
    }
  Category C = concrete("Δ≤" + std::to_string(n), std::move(objects), sizes, std::move(maps));
  for (auto& w : basis) C.basis.push_back(C.arrow(w));
  return C;
}

// ---- constructions ------------------------------------------------------------------------------------------------------------

// The opposite category: the same objects and arrows, each arrow turned. Arrow f of C is arrow f of its opposite.
inline Category opposite(const Category& C) {
  Category O = C;
  O.name = C.name + "ᵒᵖ";
  const std::size_t n = C.size();
  for (Index f = 0; f < n; f++) std::swap(O.arrows[f].dom, O.arrows[f].cod);
  for (Index g = 0; g < n; g++)
    for (Index f = 0; f < n; f++) O.table[static_cast<std::size_t>(g) * n + f] = C.table[static_cast<std::size_t>(f) * n + g];
  return O;
}

// The product C × D: the object (c, d) is c |D| + d, the arrow (f, g) is f |D| + g, with |D| the objects, the arrows of D.
inline Category product(const Category& C, const Category& D) {
  std::vector<std::string> objects;
  for (auto& c : C.objects)
    for (auto& d : D.objects) objects.push_back("(" + c + "," + d + ")");
  const Index m = static_cast<Index>(D.objects.size()), n = static_cast<Index>(D.size());
  std::vector<Arrow> arrows;
  for (Index f = 0; f < C.size(); f++)
    for (Index g = 0; g < D.size(); g++)
      arrows.push_back({C.is_identity(f) && D.is_identity(g) ? "id_(" + C.objects[C.dom(f)] + "," + D.objects[D.dom(g)] + ")" : "(" + C.arrows[f].name + "," + D.arrows[g].name + ")",
                        C.dom(f) * m + D.dom(g), C.cod(f) * m + D.cod(g)});
  std::vector<Index> identity;
  for (Index c = 0; c < C.objects.size(); c++)
    for (Index d = 0; d < D.objects.size(); d++) identity.push_back(C.identity[c] * n + D.identity[d]);
  Category P = assemble(C.name + " × " + D.name, std::move(objects), std::move(arrows), std::move(identity),
                        [&](Index g, Index f) { return C.compose(g / n, f / n) * n + D.compose(g % n, f % n); });
  if ((!C.basis.empty() || C.size() == C.objects.size()) && (!D.basis.empty() || D.size() == D.objects.size())) {  // (f, 1) and (1, g)
    for (Index f : C.basis)
      for (Index d : D.identity) P.basis.push_back(f * n + d);
    for (Index c : C.identity)
      for (Index g : D.basis) P.basis.push_back(c * n + g);
  }
  return P;
}

// The disjoint union C + D: the objects and arrows of C, then those of D.
inline Category coproduct(const Category& C, const Category& D) {
  std::vector<std::string> objects = C.objects;
  objects.insert(objects.end(), D.objects.begin(), D.objects.end());
  const Index m = static_cast<Index>(C.objects.size()), n = static_cast<Index>(C.size());
  std::vector<Arrow> arrows = C.arrows;
  for (auto f : D.arrows) arrows.push_back({f.name, f.dom + m, f.cod + m});
  std::vector<Index> identity = C.identity;
  for (auto i : D.identity) identity.push_back(i + n);
  Category S = assemble(C.name + " + " + D.name, std::move(objects), std::move(arrows), std::move(identity),
                        [&](Index g, Index f) { return g < n ? C.compose(g, f) : D.compose(g - n, f - n) + n; });
  if ((!C.basis.empty() || C.size() == C.objects.size()) && (!D.basis.empty() || D.size() == D.objects.size())) {
    S.basis = C.basis;
    for (Index g : D.basis) S.basis.push_back(g + n);
  }
  return S;
}

// A category with the places in another of its objects and arrows.
struct Within {
  Category category;
  std::vector<Index> objects, arrows;  // objects[a], arrows[f]: what a and f are in the larger category (or, for a slice, see there)
};

// The full subcategory on these objects.
inline Within full_subcategory(const Category& C, const std::vector<Index>& objects, std::string name = {}) {
  std::vector<Index> place(C.objects.size(), none), arrow_place(C.size(), none);
  Within S;
  S.objects = objects;
  std::vector<std::string> names;
  for (Index k = 0; k < objects.size(); k++) place[objects[k]] = k, names.push_back(C.objects[objects[k]]);
  std::vector<Arrow> arrows;
  std::vector<Index> identity(objects.size());
  // Identities first, in the order of the objects.
  for (Index k = 0; k < objects.size(); k++) {
    const Index i = C.identity[objects[k]];
    arrow_place[i] = static_cast<Index>(S.arrows.size()), identity[k] = arrow_place[i];
    S.arrows.push_back(i), arrows.push_back({C.arrows[i].name, k, k});
  }
  for (Index f = 0; f < C.size(); f++)
    if (!C.is_identity(f) && place[C.dom(f)] != none && place[C.cod(f)] != none) {
      arrow_place[f] = static_cast<Index>(S.arrows.size());
      S.arrows.push_back(f), arrows.push_back({C.arrows[f].name, place[C.dom(f)], place[C.cod(f)]});
    }
  S.category = assemble(name.empty() ? "a full subcategory of " + C.name : std::move(name), std::move(names), std::move(arrows), std::move(identity),
                        [&](Index g, Index f) { return arrow_place[C.compose(S.arrows[g], S.arrows[f])]; });
  return S;
}

// The slice C / c: its objects are the arrows into c, its arrows from f to g the u with g ∘ u = f.
// objects[k] is the arrow of C that the object k is; arrows[k] is the u of C beneath the arrow k.
inline Within slice(const Category& C, Index c) {
  Within S;
  std::vector<std::string> names;
  for (Index f = 0; f < C.size(); f++)
    if (C.cod(f) == c) S.objects.push_back(f), names.push_back(C.arrows[f].name);
  std::vector<Arrow> arrows;
  std::vector<Index> identity(S.objects.size());
  std::map<std::tuple<Index, Index, Index>, Index> at;  // (source object, target object, u) → arrow
  for (int pass = 0; pass < 2; pass++)  // identities first
    for (Index a = 0; a < S.objects.size(); a++)
      for (Index b = 0; b < S.objects.size(); b++)
        for (Index u : C.hom(C.dom(S.objects[a]), C.dom(S.objects[b]))) {
          if (C.compose(S.objects[b], u) != S.objects[a]) continue;
          const bool id = a == b && C.is_identity(u);
          if (id != (pass == 0)) continue;
          if (id) identity[a] = static_cast<Index>(arrows.size());
          at[{a, b, u}] = static_cast<Index>(arrows.size());
          S.arrows.push_back(u);
          arrows.push_back({id ? "id_" + names[a] : C.arrows[u].name + ":" + names[a] + "→" + names[b], a, b});
        }
  const auto ends = arrows;
  S.category = assemble(C.name + "/" + C.objects[c], std::move(names), std::move(arrows), std::move(identity),
                        [&](Index g, Index f) { return at.at({ends[f].dom, ends[g].cod, C.compose(S.arrows[g], S.arrows[f])}); });
  return S;
}

// The coslice c / C: its objects are the arrows out of c, its arrows from f to g the u with u ∘ f = g.
inline Within coslice(const Category& C, Index c) {
  Within S = slice(opposite(C), c);
  S.category = opposite(S.category);
  S.category.name = C.objects[c] + "/" + C.name;
  for (Index k = 0; k < S.category.size(); k++)
    if (!S.category.is_identity(k)) {
      const Arrow& a = S.category.arrows[k];
      S.category.arrows[k].name = C.arrows[S.arrows[k]].name + ":" + S.category.objects[a.dom] + "→" + S.category.objects[a.cod];
    }
  return S;
}

// ---- properties ---------------------------------------------------------------------------------------------------------------

// The inverse of f, or none.
inline Index inverse(const Category& C, Index f) {
  for (Index g : C.hom(C.cod(f), C.dom(f)))
    if (C.compose(g, f) == C.identity[C.dom(f)] && C.compose(f, g) == C.identity[C.cod(f)]) return g;
  return none;
}
inline bool is_iso(const Category& C, Index f) { return inverse(C, f) != none; }

// f is monic: g ≠ h implies f ∘ g ≠ f ∘ h. A failure names the two it identifies.
inline Verdict monic(const Category& C, Index f) {
  const std::string claim = C.arrows[f].name + " is monic in " + C.name;
  std::size_t examined = 0;
  for (Index g = 0; g < C.size(); g++)
    for (Index h = g + 1; h < C.size(); h++) {
      if (C.cod(g) != C.dom(f) || C.cod(h) != C.dom(f) || C.dom(g) != C.dom(h)) continue;
      examined++;
      if (C.compose(f, g) == C.compose(f, h))
        return Verdict::no(claim, "it does not tell " + C.arrows[g].name + " from " + C.arrows[h].name, examined).with("at", C.arrows[g].name + ", " + C.arrows[h].name).with("both", C.arrows[C.compose(f, g)].name);
    }
  return Verdict::yes(claim, "it tells apart every pair of arrows into its source", examined);
}
// f is epic: g ≠ h implies g ∘ f ≠ h ∘ f.
inline Verdict epic(const Category& C, Index f) {
  const std::string claim = C.arrows[f].name + " is epic in " + C.name;
  std::size_t examined = 0;
  for (Index g = 0; g < C.size(); g++)
    for (Index h = g + 1; h < C.size(); h++) {
      if (C.dom(g) != C.cod(f) || C.dom(h) != C.cod(f) || C.cod(g) != C.cod(h)) continue;
      examined++;
      if (C.compose(g, f) == C.compose(h, f))
        return Verdict::no(claim, "it does not tell " + C.arrows[g].name + " from " + C.arrows[h].name, examined).with("at", C.arrows[g].name + ", " + C.arrows[h].name).with("both", C.arrows[C.compose(g, f)].name);
    }
  return Verdict::yes(claim, "it tells apart every pair of arrows out of its target", examined);
}

// The objects with exactly one arrow to every object, and from every object.
inline std::vector<Index> initial_objects(const Category& C) {
  std::vector<Index> out;
  std::vector<std::vector<std::size_t>> count(C.objects.size(), std::vector<std::size_t>(C.objects.size(), 0));
  for (auto& f : C.arrows) count[f.dom][f.cod]++;
  for (Index a = 0; a < C.objects.size(); a++)
    if (std::all_of(count[a].begin(), count[a].end(), [](std::size_t k) { return k == 1; })) out.push_back(a);
  return out;
}
inline std::vector<Index> terminal_objects(const Category& C) { return initial_objects(opposite(C)); }

// The class of each object under isomorphism, numbered in order of first appearance.
inline std::vector<Index> isomorphism_classes(const Category& C) {
  std::vector<Index> cls(C.objects.size(), none);
  Index next = 0;
  for (Index a = 0; a < C.objects.size(); a++) {
    if (cls[a] != none) continue;
    cls[a] = next;
    for (Index b = a + 1; b < C.objects.size(); b++) {
      if (cls[b] != none) continue;
      for (Index f : C.hom(a, b))
        if (is_iso(C, f)) {
          cls[b] = next;
          break;
        }
    }
    next++;
  }
  return cls;
}

// A skeleton: the full subcategory on the first object of each class of isomorphic objects.
inline Within skeleton(const Category& C) {
  const auto cls = isomorphism_classes(C);
  std::vector<Index> first;
  for (Index a = 0; a < C.objects.size(); a++)
    if (cls[a] == first.size()) first.push_back(a);
  return full_subcategory(C, first, "a skeleton of " + C.name);
}

inline bool is_thin(const Category& C) {  // at most one arrow between any two objects: a preorder
  std::map<std::pair<Index, Index>, int> count;
  for (auto& f : C.arrows)
    if (++count[{f.dom, f.cod}] > 1) return false;
  return true;
}
inline bool is_groupoid(const Category& C) {
  for (Index f = 0; f < C.size(); f++)
    if (!is_iso(C, f)) return false;
  return true;
}
inline bool is_discrete(const Category& C) { return C.size() == C.objects.size(); }

// The connected component of each object: objects joined by a zigzag of arrows.
inline std::vector<Index> components(const Category& C) {
  std::vector<Index> parent = detail::iota(C.objects.size());
  auto find = [&](Index a) {
    while (parent[a] != a) a = parent[a] = parent[parent[a]];
    return a;
  };
  for (auto& f : C.arrows) parent[find(f.dom)] = find(f.cod);
  std::vector<Index> label(C.objects.size(), none), out(C.objects.size());
  Index next = 0;
  for (Index a = 0; a < C.objects.size(); a++) {
    const Index r = find(a);
    if (label[r] == none) label[r] = next++;
    out[a] = label[r];
  }
  return out;
}

// The subcategory generated by some arrows: every identity and every composite of them, as a mark on each arrow.
inline std::vector<char> generated(const Category& C, const std::vector<Index>& by) {
  std::vector<char> in(C.size(), 0);
  std::vector<Index> have;
  for (Index i : C.identity) in[i] = 1;
  for (Index f : by)
    if (!in[f]) in[f] = 1, have.push_back(f);
  // Every composite is a generator after a composite: close under composition with the generators on the left.
  for (std::size_t k = 0; k < have.size(); k++)
    for (Index g : by) {
      if (C.cod(have[k]) != C.dom(g)) continue;
      const Index h = C.compose(g, have[k]);
      if (!in[h]) in[h] = 1, have.push_back(h);
    }
  return in;
}

// Arrows that generate the category under composition. Where its construction gave a basis, that; otherwise the arrows
// that are no composite of two arrows other than identities (the covers of a partial order), then as many more, in
// order, as are needed. Where arrows have retractions every arrow is such a composite (d = (d ∘ s) ∘ d), and the choice
// is then only one that generates, neither least nor canonical.
inline std::vector<Index> generators(const Category& C) {
  if (!C.basis.empty() || C.size() == C.objects.size()) return C.basis;
  const std::size_t n = C.size();
  std::vector<char> composite(n, 0);
  for (Index g = 0; g < n; g++)
    for (Index f = 0; f < n; f++)
      if (C.cod(f) == C.dom(g) && !C.is_identity(f) && !C.is_identity(g)) composite[C.compose(g, f)] = 1;
  std::vector<Index> gens;
  for (Index f = 0; f < n; f++)
    if (!C.is_identity(f) && !composite[f]) gens.push_back(f);
  std::vector<char> in = generated(C, gens);
  for (Index f = 0; f < n; f++)
    if (!in[f]) gens.push_back(f), in = generated(C, gens);
  return gens;
}

}  // namespace kategoria::finite
