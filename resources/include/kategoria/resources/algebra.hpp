// Resource types: what an amount of a resource is, how amounts combine, how they compare, and whether they divide.
//
// A resource theory is a symmetric monoidal category whose objects are resources and whose arrows are the conversions
// allowed for free; its shadow is an ordered commutative monoid in which a ≽ b when a can be converted into b
// (Coecke, Fritz and Spekkens 2016, A mathematical theory of resources, Information and Computation 250, Def. 2.1 and
// Thm 4.2; Fritz 2017, Resource convertibility and ordered commutative monoids, Mathematical Structures in Computer
// Science 27, Def. 3.1). In the language of Fong and Spivak (2019, Seven Sketches in Compositionality, ch. 2), a resource
// theory's shadow is a symmetric monoidal preorder. Here a resource type declares that shadow by its parts:
//
//   - components, combined componentwise (a finite product), each with its kinds and a quantity semiring that fixes
//     divisibility: natural (ℕ, identical units), granular ((1/q)ℕ), nonnegative (ℚ≥0, divisible; exact rationals stand
//     for ℝ≥0, since no law is checked in floating point), integer and rational (signed: balances and debts, which
//     Fritz's theory admits by not assuming x ≥ 0), boolean (0 or 1 under ∨) and maximum (ℚ≥0 under max), the last two
//     quality-like, a + a = a (CFS Examples 4.3–4.4);
//   - conversions, the generating free processes, each from one bundle to another (the transitions of a Petri net:
//     Meseguer and Montanari 1990), and free disposal declared kind by kind, refused for chores and waste (Fritz 2017,
//     §3; CFS Remark 4.19);
//   - validity: capacities and distinct items (a labelled item held at most once), which make combination partial, as
//     resource algebras do (Jung, Krebbers, Jung, Bizjak, Birkedal and Dreyer 2018, Iris from the ground up, JFP 28);
//   - laws: conservation laws and monotones, homomorphisms to ℚ given by weights on the kinds.
//
// The order a ≽ b is the least preorder compatible with combination that contains the declared conversions and the
// disposals: b is reached from a by applying conversions (each to part of the bundle, the rest kept as context) and then
// disposing of disposable kinds. Deciding it in general is hard (equality in finitely presented commutative semigroups
// needs exponential space, Mayr and Meyer 1982; reachability in Petri nets is Ackermann-complete, Czerwiński and Orlikowski
// 2021, Leroux 2021), so convertible() answers with a witness, refutes with a violated monotone, or says it is undecided
// within its budget. Conversions are applied in whole multiples; a fractional application on divisible components is
// not searched, and an answer that would need one is undecided, said so.
//
// Conventions. A bundle lists one amount for each kind of the type, the components' kinds in order. Every amount is a
// morphe Rational whose numerator and denominator fit in 64 bits; an amount, or a result, beyond that is refused, never
// carried (kategoria's invariant 7). A witness found by the search is replayed by check_witness, which shares none of the
// search's code, before it is reported (invariant 5).

#pragma once

#include <kategoria/kernel/verdict.hpp>

#include <morphe/arithmetic/rational.hpp>

#include <algorithm>
#include <cstddef>
#include <map>
#include <optional>
#include <queue>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::resources {

using kernel::Verdict;
using morphe::arithmetic::Integer;
using morphe::arithmetic::Rational;

enum class Quantity { natural, granular, nonnegative, integer, rational, boolean, maximum };

inline const char* name_of(Quantity q) {
  switch (q) {
    case Quantity::natural: return "natural numbers (identical units)";
    case Quantity::granular: return "multiples of a grain";
    case Quantity::nonnegative: return "nonnegative rationals (divisible)";
    case Quantity::integer: return "integers (signed balances)";
    case Quantity::rational: return "rationals (signed, divisible)";
    case Quantity::boolean: return "0 or 1 under or (a quality)";
    case Quantity::maximum: return "nonnegative rationals under max (a quality)";
  }
  return "";
}

inline bool quality(Quantity q) { return q == Quantity::boolean || q == Quantity::maximum; }
inline bool signed_(Quantity q) { return q == Quantity::integer || q == Quantity::rational; }
inline bool divisible(Quantity q) { return q == Quantity::nonnegative || q == Quantity::rational; }

struct Kind {
  std::string name;
  bool disposable = true;              // may be thrown away freely (refuse for chores and waste)
  std::optional<Rational> capacity;    // the most a valid bundle may hold of it
  bool distinct = false;               // a labelled item: held at most once (natural components only)
};

struct Component {
  std::string name;
  Quantity quantity = Quantity::nonnegative;
  Integer grain = 1;                   // granular: amounts are multiples of 1/grain
  std::vector<Kind> kinds;
};

using Bundle = std::vector<Rational>;

struct Conversion {
  std::string name;
  Bundle from, to;                     // over every kind of the type
};

struct Law {
  std::string name;
  std::vector<Rational> weights;       // one per kind: the law's value of a bundle is Σ weights · amounts
  bool conserved = true;               // conserved: unchanged by every free process; else a monotone: never increased
};

struct Type {
  std::string name;
  std::vector<Component> components;
  std::vector<Conversion> conversions;
  std::vector<Law> laws;
  std::vector<std::string> declared;   // properties declared, each checked: quantity-like, quality-like, cancellative,
                                       // catalysis-free, splittable

  std::size_t size() const {
    std::size_t n = 0;
    for (const auto& c : components) n += c.kinds.size();
    return n;
  }
  // The component of each kind, and the kind itself.
  std::pair<const Component*, const Kind*> at(std::size_t k) const {
    for (const auto& c : components) {
      if (k < c.kinds.size()) return {&c, &c.kinds[k]};
      k -= c.kinds.size();
    }
    throw std::out_of_range("kategoria::resources: no such kind");
  }
  std::string kind_name(std::size_t k) const {
    const auto [c, kind] = at(k);
    return c->name + "." + kind->name;
  }
  std::size_t index(const std::string& qualified) const {
    for (std::size_t k = 0; k < size(); k++)
      if (kind_name(k) == qualified || at(k).second->name == qualified) return k;
    throw std::invalid_argument("kategoria::resources: no kind named " + qualified + " in " + name);
  }
  Bundle zero() const { return Bundle(size(), Rational(0)); }
};

// ---- Bundles in words -----------------------------------------------------------------------------------------------------

inline std::string words(const Type& T, const Bundle& b) {
  std::string s;
  for (std::size_t k = 0; k < b.size() && k < T.size(); k++)
    if (!b[k].is_zero()) s += (s.empty() ? "" : ", ") + b[k].str() + " " + T.kind_name(k);
  return s.empty() ? "nothing" : s;
}

// ---- Well-formedness and membership ---------------------------------------------------------------------------------------

namespace detail {

inline bool on_grain(const Rational& x, const Integer& grain) { return (x * Rational(grain)).is_integer(); }

inline bool fits(const Rational& x) { return x.numerator().fits_int64() && x.denominator().fits_int64(); }

inline const Rational& checked(const Rational& x, const std::string& what) {
  if (!fits(x)) throw std::overflow_error("kategoria::resources: " + what + " is " + x.str() + ", beyond 64 bits; refused rather than carried");
  return x;
}

inline std::optional<std::string> not_in_carrier(const Type& T, const Bundle& b, const std::string& what) {
  if (b.size() != T.size()) return what + " does not give an amount for every kind of " + T.name;
  for (std::size_t k = 0; k < b.size(); k++) {
    const auto [c, kind] = T.at(k);
    const Rational& x = b[k];
    const std::string at = what + " holds " + x.str() + " of " + T.kind_name(k);
    if (!fits(x)) return at + ", beyond 64 bits";
    switch (c->quantity) {
      case Quantity::natural:
        if (!x.is_integer() || x.sign() < 0) return at + ", which is not a natural number";
        break;
      case Quantity::granular:
        if (x.sign() < 0 || !on_grain(x, c->grain)) return at + ", which is not a nonnegative multiple of 1/" + c->grain.str();
        break;
      case Quantity::nonnegative:
      case Quantity::maximum:
        if (x.sign() < 0) return at + ", which is negative";
        break;
      case Quantity::integer:
        if (!x.is_integer()) return at + ", which is not an integer";
        break;
      case Quantity::rational: break;
      case Quantity::boolean:
        if (!(x == Rational(0) || x == Rational(1))) return at + ", which is neither 0 nor 1";
        break;
    }
  }
  return std::nullopt;
}

}  // namespace detail

inline Verdict well_formed(const Type& T) {
  const std::string claim = T.name + " is a well-formed resource type";
  std::set<std::string> names;
  for (const auto& c : T.components) {
    if (c.kinds.empty()) return Verdict::no(claim, "the component " + c.name + " has no kinds");
    if (c.quantity == Quantity::granular && !(c.grain > Integer(0))) return Verdict::no(claim, "the component " + c.name + " has no positive grain");
    for (const auto& k : c.kinds) {
      if (!names.insert(c.name + "." + k.name).second) return Verdict::no(claim, "the kind " + c.name + "." + k.name + " is declared twice");
      if (k.distinct && c.quantity != Quantity::natural) return Verdict::no(claim, "the kind " + c.name + "." + k.name + " is a distinct item, which only a component of natural numbers can hold");
      if (k.capacity && quality(c.quantity) && *k.capacity < Rational(0)) return Verdict::no(claim, "the capacity of " + c.name + "." + k.name + " is negative");
    }
  }
  for (const auto& v : T.conversions) {
    if (auto why = detail::not_in_carrier(T, v.from, "the conversion " + v.name + "'s input")) return Verdict::no(claim, *why);
    if (auto why = detail::not_in_carrier(T, v.to, "the conversion " + v.name + "'s output")) return Verdict::no(claim, *why);
  }
  for (const auto& l : T.laws)
    if (l.weights.size() != T.size()) return Verdict::no(claim, "the law " + l.name + " does not weigh every kind");
  return Verdict::yes(claim, std::to_string(T.components.size()) + " components, " + std::to_string(T.size()) + " kinds, " + std::to_string(T.conversions.size()) + " conversions");
}

inline bool member(const Type& T, const Bundle& b) { return !detail::not_in_carrier(T, b, "the bundle").has_value(); }

// ---- Combination, validity and scaling ------------------------------------------------------------------------------------

inline Bundle combine(const Type& T, const Bundle& a, const Bundle& b) {
  if (a.size() != T.size() || b.size() != T.size()) throw std::invalid_argument("kategoria::resources::combine: bundles of another type");
  Bundle c(T.size());
  for (std::size_t k = 0; k < T.size(); k++) c[k] = detail::checked(quality(T.at(k).first->quantity) ? std::max(a[k], b[k]) : a[k] + b[k], "a combined amount of " + T.kind_name(k));
  return c;
}

inline Bundle combine_all(const Type& T, const std::vector<Bundle>& parts) {
  Bundle s = T.zero();
  for (const auto& p : parts) s = combine(T, s, p);
  return s;
}

// Why a bundle is not valid (beyond a capacity, or a distinct item held more than once), or nothing.
inline std::optional<std::string> invalid(const Type& T, const Bundle& b) {
  if (auto why = detail::not_in_carrier(T, b, "the bundle")) return why;
  for (std::size_t k = 0; k < T.size(); k++) {
    const Kind& kind = *T.at(k).second;
    if (kind.capacity && b[k] > *kind.capacity) return "it holds " + b[k].str() + " of " + T.kind_name(k) + ", beyond its capacity of " + kind.capacity->str();
    if (kind.distinct && b[k] > Rational(1)) return "it holds the distinct item " + T.kind_name(k) + " " + b[k].str() + " times";
  }
  return std::nullopt;
}

inline bool valid(const Type& T, const Bundle& b) { return !invalid(T, b).has_value(); }

// r · b for a rational r ≥ 0: refused where a component does not divide (units, items, grains not met, qualities).
inline Bundle scale(const Type& T, const Bundle& b, const Rational& r) {
  if (r.sign() < 0) throw std::invalid_argument("kategoria::resources::scale: a negative multiple");
  Bundle c(T.size());
  for (std::size_t k = 0; k < T.size(); k++) {
    const auto [comp, kind] = T.at(k);
    if (quality(comp->quantity)) {
      c[k] = r.is_zero() ? Rational(0) : b[k];
      continue;
    }
    c[k] = detail::checked(b[k] * r, "a scaled amount of " + T.kind_name(k));
    if ((comp->quantity == Quantity::natural || comp->quantity == Quantity::integer) && !c[k].is_integer())
      throw std::invalid_argument("kategoria::resources::scale: " + T.kind_name(k) + " comes in whole units and does not divide by " + r.str());
    if (comp->quantity == Quantity::granular && !detail::on_grain(c[k], comp->grain))
      throw std::invalid_argument("kategoria::resources::scale: " + T.kind_name(k) + " comes in grains of 1/" + comp->grain.str() + " and does not divide by " + r.str());
  }
  return c;
}

// ---- Laws -----------------------------------------------------------------------------------------------------------------

inline Rational value(const Law& L, const Bundle& b) {
  Rational s(0);
  for (std::size_t k = 0; k < b.size() && k < L.weights.size(); k++) s = detail::checked(s + L.weights[k] * b[k], "the value of the law " + L.name);
  return s;
}

// A law checked on the generating free processes: each conversion and each disposal. A homomorphism that a generator
// leaves unchanged (or does not increase) is left unchanged (not increased) by every free process, since every free process
// is a composite of generators each applied with the rest of the bundle as context, and the law adds over the context:
// L(x + pre) − L(x + post) = L(pre) − L(post). So the verdict is a proof for every bundle, from finitely many checks.
// Laws on quality components are refused, since their combination is a join, not a sum, and the argument fails.
inline Verdict verify_law(const Type& T, const Law& L) {
  const std::string claim = "the law " + L.name + (L.conserved ? " is conserved by every free process of " : " never increases under a free process of ") + T.name;
  if (L.weights.size() != T.size()) return Verdict::no(claim, "it does not weigh every kind");
  for (std::size_t k = 0; k < T.size(); k++)
    if (quality(T.at(k).first->quantity) && !L.weights[k].is_zero())
      return Verdict::no(claim, "it weighs " + T.kind_name(k) + ", a quality whose amounts combine by a join, so the law does not add");
  std::size_t examined = 0;
  for (const auto& v : T.conversions) {
    examined++;
    const Rational before = value(L, v.from), after = value(L, v.to);
    if (L.conserved ? before != after : after > before)
      return Verdict::no(claim, "the conversion " + v.name + " takes it from " + before.str() + " to " + after.str(), examined)
          .with("at", v.name).with("left", before.str()).with("right", after.str());
  }
  for (std::size_t k = 0; k < T.size(); k++) {
    if (!T.at(k).second->disposable) continue;
    examined++;
    if (L.conserved && !L.weights[k].is_zero())
      return Verdict::no(claim, "disposing of " + T.kind_name(k) + ", which is free, changes it (weight " + L.weights[k].str() + "); it can be at most a monotone", examined).with("at", T.kind_name(k));
    if (!L.conserved && L.weights[k].sign() < 0)
      return Verdict::no(claim, "disposing of " + T.kind_name(k) + ", which is free, increases it (weight " + L.weights[k].str() + ")", examined).with("at", T.kind_name(k));
  }
  return Verdict::yes(claim, "checked on each of the " + std::to_string(T.conversions.size()) + " conversions and every free disposal; a homomorphism that respects the generating processes respects every free process", examined);
}

// ---- Convertibility -------------------------------------------------------------------------------------------------------

struct Step {
  std::string what;    // a conversion's name, or "dispose"
  Bundle after;
};

struct Conversion_search {
  Verdict verdict;
  std::vector<Step> witness;  // when it holds: the conversions applied, in order, then the disposal
};

namespace detail {

// b is reached from x by disposal alone: equal on non-disposable kinds, at most x on disposable ones (for a quality, its
// join order: a smaller quality can be had by disposing of the difference only when the kind is disposable).
inline bool disposes_to(const Type& T, const Bundle& x, const Bundle& b) {
  for (std::size_t k = 0; k < T.size(); k++) {
    if (T.at(k).second->disposable ? b[k] > x[k] : b[k] != x[k]) return false;
  }
  return true;
}

inline std::string key(const Bundle& b) {
  std::string s;
  for (const auto& x : b) s += x.str() + "|";
  return s;
}

}  // namespace detail

// Replays a witness step by step, sharing none of the search's code: each conversion must be one of the type's, must find
// its input in the bundle (a quality need only be present), and must leave the bundle it records; the last step, a
// disposal, may only lower disposable kinds and must end at the target.
inline Verdict check_witness(const Type& T, const Bundle& a, const std::vector<Step>& steps, const Bundle& b) {
  const std::string claim = "the witness converts " + words(T, a) + " into " + words(T, b);
  Bundle x = a;
  for (std::size_t i = 0; i < steps.size(); i++) {
    const Step& s = steps[i];
    if (s.what == "dispose") {
      if (i + 1 != steps.size()) return Verdict::no(claim, "a disposal that is not the last step", i + 1);
      for (std::size_t k = 0; k < T.size(); k++) {
        const bool lowered = s.after[k] < x[k], changed = s.after[k] != x[k];
        if (changed && (!lowered || !T.at(k).second->disposable))
          return Verdict::no(claim, "the disposal changes " + T.kind_name(k) + ", which may not be thrown away or is raised", i + 1).with("at", T.kind_name(k));
      }
      x = s.after;
      continue;
    }
    const Conversion* v = nullptr;
    for (const auto& c : T.conversions)
      if (c.name == s.what) v = &c;
    if (!v) return Verdict::no(claim, "step " + std::to_string(i + 1) + " names no conversion of the type: " + s.what, i + 1);
    Bundle y = x;
    for (std::size_t k = 0; k < T.size(); k++) {
      const Quantity q = T.at(k).first->quantity;
      if (x[k] < v->from[k] && !signed_(q)) return Verdict::no(claim, "step " + std::to_string(i + 1) + " (" + v->name + ") needs " + v->from[k].str() + " of " + T.kind_name(k) + " and finds " + x[k].str(), i + 1);
      y[k] = quality(q) ? (x[k] < v->to[k] ? v->to[k] : x[k]) : x[k] - v->from[k] + v->to[k];
    }
    if (y != s.after) return Verdict::no(claim, "step " + std::to_string(i + 1) + " (" + v->name + ") does not leave the bundle it records", i + 1);
    x = y;
  }
  if (x != b) return Verdict::no(claim, "it ends at " + words(T, x) + ", not at the target", steps.size());
  return Verdict::yes(claim, "each of its " + std::to_string(steps.size()) + " steps replayed", steps.size());
}

// Whether a ≽ b: b reached from a by conversions (whole multiples, each with the rest of the bundle as context) and then
// disposal. A witness when it holds; a valid monotone or invariant that a has less of than b (or a different value of) when
// it fails; else undecided within `budget` bundles explored.
inline Conversion_search convertible(const Type& T, const Bundle& a, const Bundle& b, std::size_t budget = 20000) {
  const std::string claim = words(T, a) + " can be converted into " + words(T, b) + " in " + T.name;
  if (auto why = detail::not_in_carrier(T, a, "the source")) return {Verdict::no(claim, *why), {}};
  if (auto why = detail::not_in_carrier(T, b, "the target")) return {Verdict::no(claim, *why), {}};
  // Impossibility by a declared law that holds on the generators.
  for (const auto& L : T.laws) {
    if (!verify_law(T, L).holds()) continue;
    const Rational va = value(L, a), vb = value(L, b);
    if (L.conserved ? va != vb : va < vb)
      return {Verdict::no(claim, "the " + std::string(L.conserved ? "conserved law " : "monotone ") + L.name + " is " + va.str() + " for the source and " + vb.str() + " for the target, and no free process " +
                                     (L.conserved ? "changes it" : "increases it"))
                  .with("monotone", L.name).with("left", va.str()).with("right", vb.str()),
              {}};
  }
  // Breadth-first search over bundles reached by conversions.
  std::map<std::string, std::pair<std::string, std::string>> parent;  // key → (parent key, conversion)
  std::map<std::string, Bundle> seen;
  std::queue<Bundle> queue;
  seen.emplace(detail::key(a), a);
  parent.emplace(detail::key(a), std::make_pair(std::string(), std::string()));
  queue.push(a);
  std::size_t explored = 0;
  bool fractional = false;
  for (const auto& v : T.conversions)
    for (std::size_t k = 0; k < T.size(); k++)
      if (divisible(T.at(k).first->quantity) && (!v.from[k].is_zero() || !v.to[k].is_zero())) fractional = true;
  while (!queue.empty() && explored < budget) {
    Bundle x = queue.front();
    queue.pop();
    explored++;
    if (detail::disposes_to(T, x, b)) {
      std::vector<Step> path;
      std::string at = detail::key(x);
      while (!parent[at].first.empty() || !parent[at].second.empty()) {
        path.push_back({parent[at].second, seen[at]});
        at = parent[at].first;
      }
      std::reverse(path.begin(), path.end());
      if (x != b) path.push_back({"dispose", b});
      std::string how;
      for (const auto& s : path) how += (how.empty() ? "" : ", then ") + s.what;
      const Verdict replay = check_witness(T, a, path, b);
      if (!replay.holds()) return {Verdict::unknown(claim, "the search proposed a witness that did not replay: " + replay.reason, explored), {}};
      return {Verdict::yes(claim, path.empty() ? "it is the same bundle" : "by " + how + ", the witness replayed step by step", explored).with("witness", how.empty() ? "nothing to do" : how), path};
    }
    for (const auto& v : T.conversions) {
      Bundle y(T.size());
      bool fits = true;
      for (std::size_t k = 0; k < T.size() && fits; k++) {
        if (quality(T.at(k).first->quantity)) {
          if (x[k] < v.from[k]) fits = false;          // a quality is used, not spent: it must be there
          y[k] = std::max(x[k], v.to[k]);
        } else {
          y[k] = x[k] - v.from[k] + v.to[k];
          if (!signed_(T.at(k).first->quantity) && x[k] < v.from[k]) fits = false;
        }
      }
      if (!fits) continue;
      const std::string ky = detail::key(y);
      if (seen.count(ky)) continue;
      seen.emplace(ky, y);
      parent.emplace(ky, std::make_pair(detail::key(x), v.name));
      queue.push(y);
    }
  }
  const bool exhausted = queue.empty();
  if (exhausted && !fractional)
    return {Verdict::no(claim, "every bundle reachable from the source (" + std::to_string(explored) + ") was examined, and none disposes to the target", explored), {}};
  return {Verdict::unknown(claim, exhausted ? "no whole-multiple sequence of conversions reaches it, and conversions on divisible components could also be applied in fractions, which is not searched"
                                            : "not found among the first " + std::to_string(explored) + " bundles reachable, and no declared law rules it out",
                           explored),
          {}};
}

}  // namespace kategoria::resources
