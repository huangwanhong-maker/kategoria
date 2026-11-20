// Finite resource algebras: a carrier declared whole, with a partial combination, a unit and an order, and its laws
// decided by looking at every case. A finite model's verdict is a proof for that model only, never for an infinite
// structure it approximates.
//
// A partial commutative monoid becomes a total one by adjoining an absorbing element ⊤ for every undefined combination,
// and the partial monoid satisfies the laws in the strong sense (both sides defined together, and then equal) exactly when
// the totalisation is a commutative monoid with ⊤ absorbing. So the monoid laws of a finite resource algebra are decided by
// kategoria's own validation of the totalisation as a one-object category (finite::monoid, finite::validate). Its order is
// built as a preorder category (finite::preorder, which refuses a relation that is not reflexive and transitive), and
// compatibility with combination is the statement that combination is a functor from the product of the order with itself
// (on the pairs whose combination is defined) to the order: on thin categories, a monotone map. It is checked case by case
// and, for small carriers, also as a functor by functors::verify, the two required to agree.
//
// The declared properties, each decided on the model: quantity-like (some a + a ≠ a) or quality-like (a + a = a for every
// a) (Coecke, Fritz and Spekkens 2016, Def. 4.13); cancellative (a + c = b + c ⇒ a = b); catalysis-free (a + c ≽ b + c ⇒
// a ≽ b, ibid. Def. 4.10); splittable, the Riesz decomposition property (a ≽ b₁ + b₂ ⇒ a = a₁ + a₂ with aᵢ ≽ bᵢ; CFS call
// such theories non-interacting, ibid. Def. 4.18). A counterexample is definitive whatever the model; a positive verdict is
// the model's.
//
// truncation() makes a finite model of a declared type: its bundles on a grid (each kind from a least to a greatest amount
// in steps), with partial addition (a combination that leaves the grid is undefined) and the type's order restricted to the
// grid. Saturating or wrapping additions are not offered for a type, since they change the algebra; a person may still
// declare such an algebra whole, and the checks say which laws it keeps.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/functors/functor.hpp>
#include <kategoria/resources/algebra.hpp>

#include <cstddef>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::resources {

using finite::Index;
using finite::none;

struct FiniteAlgebra {
  std::string name;
  std::vector<std::string> elements;
  std::vector<std::vector<Index>> combine;   // combine[a][b], or none where the combination is undefined
  Index unit = 0;
  std::vector<std::vector<char>> converts;   // converts[a][b]: a ≽ b, a can be converted into b
  std::vector<std::pair<Index, Index>> undecided;  // pairs whose order the search could not decide (a truncation's)

  std::size_t size() const { return elements.size(); }
};

namespace detail {

inline std::string scope(const FiniteAlgebra& A) {
  return "exhaustively on the finite model " + A.name + " (" + std::to_string(A.size()) + " elements): a proof for this model only";
}

inline std::optional<std::string> malformed(const FiniteAlgebra& A) {
  const std::size_t n = A.size();
  if (n == 0) return "it has no elements";
  if (A.combine.size() != n || A.converts.size() != n) return "its tables are not of its size";
  for (std::size_t a = 0; a < n; a++) {
    if (A.combine[a].size() != n || A.converts[a].size() != n) return "its tables are not square";
    for (std::size_t b = 0; b < n; b++)
      if (A.combine[a][b] != none && A.combine[a][b] >= n) return "a combination names no element";
  }
  if (A.unit >= n) return "its unit is not one of its elements";
  return std::nullopt;
}

}  // namespace detail

// The monoid laws in the strong sense, decided by validating the totalisation as a category.
inline Verdict monoid_laws(const FiniteAlgebra& A) {
  const std::string claim = "combination in " + A.name + " is associative, with " + (A.size() ? A.elements[A.unit] : std::string("?")) + " as its unit";
  if (auto why = detail::malformed(A)) return Verdict::no(claim, *why);
  const std::size_t n = A.size(), top = n;  // ⊤ is the element n
  std::vector<std::string> names = A.elements;
  names.push_back("⊤");
  std::vector<Index> table((n + 1) * (n + 1));
  for (std::size_t a = 0; a <= n; a++)
    for (std::size_t b = 0; b <= n; b++) table[a * (n + 1) + b] = (a == top || b == top || A.combine[a][b] == none) ? top : A.combine[a][b];
  for (std::size_t a = 0; a < n; a++)
    if (A.combine[A.unit][a] != a || A.combine[a][A.unit] != a)
      return Verdict::no(claim, "combining " + A.elements[A.unit] + " with " + A.elements[a] + " does not give " + A.elements[a]).with("at", A.elements[a]);
  try {
    const auto C = finite::monoid(names, table, "the totalisation of " + A.name);
    const Verdict v = finite::validate(C);
    if (!v.holds()) {
      Verdict out = Verdict::no(claim, "the totalisation with ⊤ for each undefined combination is not a monoid: " + v.reason, v.examined);
      for (const auto& e : v.evidence) out.with(e.role, e.value);
      return out;
    }
    return Verdict::yes(claim, "its totalisation, ⊤ standing for every undefined combination, is a monoid as kategoria validates it; " + detail::scope(A), v.examined);
  } catch (const std::exception& e) {
    return Verdict::no(claim, e.what());
  }
}

inline Verdict commutative(const FiniteAlgebra& A) {
  const std::string claim = "combination in " + A.name + " is commutative";
  if (auto why = detail::malformed(A)) return Verdict::no(claim, *why);
  std::size_t examined = 0;
  for (std::size_t a = 0; a < A.size(); a++)
    for (std::size_t b = a + 1; b < A.size(); b++) {
      examined++;
      if (A.combine[a][b] != A.combine[b][a])
        return Verdict::no(claim, A.elements[a] + " with " + A.elements[b] + " differs from the other order", examined).with("at", A.elements[a] + ", " + A.elements[b]);
    }
  return Verdict::yes(claim, detail::scope(A), examined);
}

// The order as a preorder category; refused (with the reason) unless reflexive and transitive.
inline std::pair<Verdict, std::optional<finite::Category>> order(const FiniteAlgebra& A) {
  const std::string claim = "convertibility in " + A.name + " is a preorder";
  if (auto why = detail::malformed(A)) return {Verdict::no(claim, *why), std::nullopt};
  if (!A.undecided.empty())
    return {Verdict::unknown(claim, std::to_string(A.undecided.size()) + " pairs were not decided, among them " + A.elements[A.undecided[0].first] + " ≽ " + A.elements[A.undecided[0].second]), std::nullopt};
  try {
    auto P = finite::preorder(A.elements, A.converts, "convertibility in " + A.name);
    return {Verdict::yes(claim, "built as a preorder category: reflexive and transitive; " + detail::scope(A), A.size() * A.size()), std::move(P)};
  } catch (const std::exception& e) {
    return {Verdict::no(claim, e.what()), std::nullopt};
  }
}

// Compatibility of the order with combination: combination is a functor from (pairs with a defined combination) of P × P
// to P, which on thin categories is monotonicity. For small carriers the functor is also built and verified by kategoria.
inline Verdict monotone(const FiniteAlgebra& A) {
  const std::string claim = "the order of " + A.name + " is compatible with combination (combination is a functor P × P → P)";
  auto [ov, P] = order(A);
  if (!ov.holds()) return Verdict{ov.status, claim, "the order is not a preorder: " + ov.reason, {}, ov.examined};
  const std::size_t n = A.size();
  std::size_t examined = 0;
  for (std::size_t a = 0; a < n; a++)
    for (std::size_t a2 = 0; a2 < n; a2++) {
      if (!A.converts[a][a2]) continue;
      for (std::size_t b = 0; b < n; b++)
        for (std::size_t b2 = 0; b2 < n; b2++) {
          if (!A.converts[b][b2]) continue;
          const Index s = A.combine[a][b], t = A.combine[a2][b2];
          if (s == none || t == none) continue;
          examined++;
          if (!A.converts[s][t])
            return Verdict::no(claim, A.elements[a] + " ≽ " + A.elements[a2] + " and " + A.elements[b] + " ≽ " + A.elements[b2] + ", but " + A.elements[s] + " ⋡ " + A.elements[t], examined)
                .with("at", A.elements[a] + " + " + A.elements[b])
                .with("left", A.elements[s]).with("right", A.elements[t]);
        }
    }
  // For a small carrier, the same as a functor verified by kategoria.
  if (n <= 6) {
    const auto PP = finite::product(*P, *P);
    std::vector<Index> objects;
    for (Index o = 0; o < PP.objects.size(); o++) {
      const Index a = o / n, b = o % n;  // the product lists objects as pairs in this order
      if (A.combine[a][b] != none) objects.push_back(o);
    }
    const auto S = finite::full_subcategory(PP, objects, "defined pairs");
    functors::Functor F;
    F.name = "combination";
    for (Index o : S.objects) F.objects.push_back(A.combine[o / n][o % n]);
    auto arrow_of = [&](Index from, Index to) {
      for (Index f = 0; f < P->size(); f++)
        if (P->dom(f) == from && P->cod(f) == to) return f;
      return none;
    };
    for (Index f : S.arrows) {
      // An arrow of the product is a pair of arrows of P; its ends are pairs, read through the product's objects.
      const Index d = PP.dom(f), c = PP.cod(f);
      F.arrows.push_back(arrow_of(A.combine[d / n][d % n], A.combine[c / n][c % n]));
    }
    const Verdict fv = functors::verify(S.category, *P, F);
    if (!fv.holds()) return Verdict::no(claim, "the case-by-case check passed but the functor check failed: " + fv.reason + " (the product's layout differs from the one assumed)", examined);
    return Verdict::yes(claim, "every pair of conversions combines into a conversion, and combination is verified a functor by kategoria; " + detail::scope(A), examined + fv.examined);
  }
  return Verdict::yes(claim, "every pair of conversions combines into a conversion, which on thin categories is functoriality; " + detail::scope(A), examined);
}

inline Verdict quality_like(const FiniteAlgebra& A) {
  const std::string claim = A.name + " is quality-like: a + a = a for every a";
  std::size_t examined = 0;
  for (std::size_t a = 0; a < A.size(); a++) {
    examined++;
    if (A.combine[a][a] != a) return Verdict::no(claim, A.elements[a] + " + " + A.elements[a] + " is " + (A.combine[a][a] == none ? std::string("undefined") : A.elements[A.combine[a][a]]), examined).with("at", A.elements[a]);
  }
  return Verdict::yes(claim, detail::scope(A), examined);
}

inline Verdict quantity_like(const FiniteAlgebra& A) {
  const std::string claim = A.name + " is quantity-like: some a + a differs from a";
  for (std::size_t a = 0; a < A.size(); a++)
    if (A.combine[a][a] != a) return Verdict::yes(claim, A.elements[a] + " + " + A.elements[a] + " differs from " + A.elements[a] + "; " + detail::scope(A), a + 1).with("witness", A.elements[a]);
  return Verdict::no(claim, "a + a = a for every element", A.size());
}

inline Verdict cancellative(const FiniteAlgebra& A) {
  const std::string claim = A.name + " is cancellative: a + c = b + c implies a = b";
  std::size_t examined = 0;
  for (std::size_t a = 0; a < A.size(); a++)
    for (std::size_t b = a + 1; b < A.size(); b++)
      for (std::size_t c = 0; c < A.size(); c++) {
        examined++;
        if (A.combine[a][c] != none && A.combine[a][c] == A.combine[b][c])
          return Verdict::no(claim, A.elements[a] + " + " + A.elements[c] + " = " + A.elements[b] + " + " + A.elements[c] + " though " + A.elements[a] + " ≠ " + A.elements[b], examined)
              .with("at", A.elements[a] + ", " + A.elements[b] + ", " + A.elements[c]);
      }
  return Verdict::yes(claim, detail::scope(A), examined);
}

inline Verdict catalysis_free(const FiniteAlgebra& A) {
  const std::string claim = A.name + " is catalysis-free: a + c ≽ b + c implies a ≽ b";
  if (!A.undecided.empty()) return Verdict::unknown(claim, "its order is not decided on every pair");
  std::size_t examined = 0;
  for (std::size_t a = 0; a < A.size(); a++)
    for (std::size_t b = 0; b < A.size(); b++) {
      if (A.converts[a][b]) continue;
      for (std::size_t c = 0; c < A.size(); c++) {
        const Index s = A.combine[a][c], t = A.combine[b][c];
        if (s == none || t == none) continue;
        examined++;
        if (A.converts[s][t])
          return Verdict::no(claim, A.elements[c] + " is a catalyst: " + A.elements[s] + " ≽ " + A.elements[t] + " though " + A.elements[a] + " ⋡ " + A.elements[b], examined)
              .with("catalyst", A.elements[c]).with("at", A.elements[a] + ", " + A.elements[b]);
      }
    }
  return Verdict::yes(claim, detail::scope(A), examined);
}

// The Riesz decomposition property: whatever a converts into a combination b₁ + b₂, a itself splits into parts that convert
// into b₁ and b₂ separately.
inline Verdict splittable(const FiniteAlgebra& A) {
  const std::string claim = A.name + " is splittable: a ≽ b₁ + b₂ implies a = a₁ + a₂ with a₁ ≽ b₁ and a₂ ≽ b₂";
  if (!A.undecided.empty()) return Verdict::unknown(claim, "its order is not decided on every pair");
  const std::size_t n = A.size();
  std::size_t examined = 0;
  for (std::size_t a = 0; a < n; a++)
    for (std::size_t b1 = 0; b1 < n; b1++)
      for (std::size_t b2 = 0; b2 < n; b2++) {
        const Index s = A.combine[b1][b2];
        if (s == none || !A.converts[a][s]) continue;
        examined++;
        bool split = false;
        for (std::size_t a1 = 0; a1 < n && !split; a1++)
          for (std::size_t a2 = 0; a2 < n && !split; a2++)
            split = A.combine[a1][a2] == a && A.converts[a1][b1] && A.converts[a2][b2];
        if (!split)
          return Verdict::no(claim, A.elements[a] + " ≽ " + A.elements[b1] + " + " + A.elements[b2] + ", but no way of splitting " + A.elements[a] + " gives parts that convert into each", examined)
              .with("at", A.elements[a]).with("left", A.elements[b1]).with("right", A.elements[b2]);
      }
  return Verdict::yes(claim, detail::scope(A), examined);
}

// ---- A finite model of a declared type ------------------------------------------------------------------------------------

struct Grid {
  Rational least = Rational(0), greatest = Rational(2), step = Rational(1);  // for every kind, unless the kind's own is narrower
  std::size_t limit = 64;                                                   // the most bundles a model may hold
  std::size_t budget = 4000;                                                // for each convertibility asked
};

inline FiniteAlgebra truncation(const Type& T, const Grid& g = {}) {
  if (!well_formed(T).holds()) throw std::invalid_argument("kategoria::resources::truncation: " + well_formed(T).reason);
  if (!(g.step > Rational(0))) throw std::invalid_argument("kategoria::resources::truncation: the step must be positive");
  // The amounts each kind takes on the grid.
  std::vector<std::vector<Rational>> values(T.size());
  for (std::size_t k = 0; k < T.size(); k++) {
    const auto [c, kind] = T.at(k);
    Rational lo = signed_(c->quantity) ? g.least : std::max(g.least, Rational(0)), hi = g.greatest, step = g.step;
    if (c->quantity == Quantity::boolean) lo = 0, hi = 1, step = 1;
    if (kind->distinct) hi = std::min(hi, Rational(1));
    if (c->quantity == Quantity::natural || c->quantity == Quantity::integer) step = std::max(step, Rational(1));
    for (Rational x = lo; x <= hi; x += step)
      if (member(T, [&] { Bundle b = T.zero(); b[k] = x; return b; }())) values[k].push_back(x);
    if (values[k].empty()) throw std::invalid_argument("kategoria::resources::truncation: the grid holds no amount of " + T.kind_name(k));
  }
  std::size_t count = 1;
  for (const auto& v : values) {
    count *= v.size();
    if (count > g.limit) throw std::invalid_argument("kategoria::resources::truncation: the grid has more than " + std::to_string(g.limit) + " bundles; narrow it");
  }
  FiniteAlgebra A;
  A.name = "the truncation of " + T.name;
  std::vector<Bundle> bundles;
  std::vector<std::size_t> digit(T.size(), 0);
  for (std::size_t i = 0; i < count; i++) {
    Bundle b(T.size());
    for (std::size_t k = 0; k < T.size(); k++) b[k] = values[k][digit[k]];
    bundles.push_back(b);
    for (std::size_t k = 0; k < T.size(); k++) {
      if (++digit[k] < values[k].size()) break;
      digit[k] = 0;
    }
  }
  auto find = [&](const Bundle& b) -> Index {
    for (Index i = 0; i < bundles.size(); i++)
      if (bundles[i] == b) return i;
    return none;
  };
  for (const auto& b : bundles) A.elements.push_back(words(T, b));
  const std::size_t n = bundles.size();
  A.combine.assign(n, std::vector<Index>(n, none));
  A.converts.assign(n, std::vector<char>(n, 0));
  for (Index a = 0; a < n; a++)
    for (Index b = 0; b < n; b++) A.combine[a][b] = find(combine(T, bundles[a], bundles[b]));
  A.unit = find(T.zero());
  if (A.unit == none) throw std::invalid_argument("kategoria::resources::truncation: the grid does not hold the empty bundle");
  for (Index a = 0; a < n; a++)
    for (Index b = 0; b < n; b++) {
      const auto r = convertible(T, bundles[a], bundles[b], g.budget);
      if (r.verdict.holds()) A.converts[a][b] = 1;
      else if (!r.verdict.fails()) A.undecided.push_back({a, b});
    }
  return A;
}

}  // namespace kategoria::resources
