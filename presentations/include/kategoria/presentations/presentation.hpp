// Categories presented by generators and equations: a quiver and equations between parallel paths.
//
// The category presented is the free category on the quiver (its arrows the paths) modulo the congruence the equations
// generate (Mac Lane 1971, II.8). Whether two paths are equal in it is the word problem of a monoid with several
// objects, undecidable in general. It is attacked here by Knuth–Bendix completion on paths in the shortlex order
// (Knuth and Bendix 1970; for paths, as for words: Book and Otto 1993, ch. 2):
//
//   - when completion ends, the rules are confluent and terminating: every path has one normal form, two paths are
//     equal exactly when their normal forms coincide, and, when the normal forms are finitely many, the category is
//     built whole from them;
//   - when it does not end within its bounds, paths whose normal forms coincide are still equal, and the rest is
//     undecided and said to be.
//
// Evidence. Equality is answered with a derivation: a chain of steps, each replacing one side of one of the
// presentation's own equations by the other inside the path. check() verifies a derivation knowing only the
// equations; nothing of the completion is trusted. Inequality rests on confluence, which certify() verifies on the
// rules as they stand: each rule decreases, each follows from the equations by its own derivation, and every critical
// pair is joinable (Newman's lemma).
//
// Conventions. A path lists its edges in the order they are travelled: {f, g} is "f then g", g ∘ f.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/kernel/verdict.hpp>

#include <algorithm>
#include <cstddef>
#include <deque>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::presentations {

using finite::Index;
using finite::none;
using kernel::Verdict;

struct Edge {
  std::string name;
  Index dom = 0, cod = 0;
};
struct Quiver {
  std::vector<std::string> objects;
  std::vector<Edge> edges;
};

// A path from `source`: its edges in the order travelled. The empty path is the identity of its source.
struct Path {
  Index source = 0;
  std::vector<Index> edges;
  bool operator==(const Path&) const = default;
};
struct Equation {
  Path left, right;
};
struct Presentation {
  std::string name;
  Quiver quiver;
  std::vector<Equation> equations;
};

inline Index target(const Quiver& Q, const Path& p) { return p.edges.empty() ? p.source : Q.edges[p.edges.back()].cod; }

// Whether the edges follow one another from the source.
inline bool composable(const Quiver& Q, const Path& p) {
  Index at = p.source;
  if (at >= Q.objects.size()) return false;
  for (Index e : p.edges) {
    if (e >= Q.edges.size() || Q.edges[e].dom != at) return false;
    at = Q.edges[e].cod;
  }
  return true;
}

// "h ∘ g ∘ f" for the path f, g, h; "id_A" for the empty path at A.
inline std::string words(const Quiver& Q, const Path& p) {
  if (p.edges.empty()) return "id_" + Q.objects[p.source];
  std::string w;
  for (std::size_t k = p.edges.size(); k-- > 0;) w += Q.edges[p.edges[k]].name + (k ? " ∘ " : "");
  return w;
}

inline Verdict well_formed(const Presentation& P) {
  const std::string claim = P.name + " is a presentation";
  for (auto& e : P.quiver.edges)
    if (e.dom >= P.quiver.objects.size() || e.cod >= P.quiver.objects.size()) return Verdict::no(claim, "the generator " + e.name + " begins or ends at no object");
  for (std::size_t k = 0; k < P.equations.size(); k++) {
    const auto& [l, r] = P.equations[k];
    if (!composable(P.quiver, l) || !composable(P.quiver, r)) return Verdict::no(claim, "a side of equation " + std::to_string(k + 1) + " is not a path");
    if (l.source != r.source || target(P.quiver, l) != target(P.quiver, r))
      return Verdict::no(claim, "the sides of equation " + std::to_string(k + 1) + ", " + words(P.quiver, l) + " = " + words(P.quiver, r) + ", are not parallel");
  }
  return Verdict::yes(claim, kernel::count(P.quiver.objects.size(), "object") + ", " + kernel::count(P.quiver.edges.size(), "generator") + ", " + kernel::count(P.equations.size(), "equation"));
}

// ---- derivations and their checker --------------------------------------------------------------------------------------------

// One step: inside the path, at position `at`, the left side of an equation is replaced by its right (forward), or its
// right by its left.
struct Step {
  std::size_t at = 0, equation = 0;
  bool forward = true;
};
using Derivation = std::vector<Step>;

// The path after one step, or nothing when the step does not apply. Knows only the equations.
inline std::optional<Path> apply(const Presentation& P, const Path& p, const Step& s) {
  if (s.equation >= P.equations.size()) return std::nullopt;
  const Path& from = s.forward ? P.equations[s.equation].left : P.equations[s.equation].right;
  const Path& to = s.forward ? P.equations[s.equation].right : P.equations[s.equation].left;
  if (s.at + from.edges.size() > p.edges.size()) return std::nullopt;
  if (!std::equal(from.edges.begin(), from.edges.end(), p.edges.begin() + static_cast<std::ptrdiff_t>(s.at))) return std::nullopt;
  Index object = p.source;  // where the path stands at position `at`
  for (std::size_t k = 0; k < s.at; k++) object = P.quiver.edges[p.edges[k]].cod;
  if (object != from.source) return std::nullopt;
  Path q{p.source, {}};
  q.edges.insert(q.edges.end(), p.edges.begin(), p.edges.begin() + static_cast<std::ptrdiff_t>(s.at));
  q.edges.insert(q.edges.end(), to.edges.begin(), to.edges.end());
  q.edges.insert(q.edges.end(), p.edges.begin() + static_cast<std::ptrdiff_t>(s.at + from.edges.size()), p.edges.end());
  return q;
}

// The checker: whether the derivation leads from one path to the other by the presentation's equations.
inline Verdict check(const Presentation& P, const Path& from, const Path& to, const Derivation& d) {
  const std::string claim = words(P.quiver, from) + " = " + words(P.quiver, to) + " in " + P.name;
  if (!composable(P.quiver, from) || !composable(P.quiver, to)) return Verdict::no(claim, "a side is not a path");
  Path p = from;
  for (std::size_t k = 0; k < d.size(); k++) {
    auto q = apply(P, p, d[k]);
    if (!q) return Verdict::no(claim, "step " + std::to_string(k + 1) + " of the derivation does not apply to " + words(P.quiver, p), k).with("at", "step " + std::to_string(k + 1));
    p = std::move(*q);
  }
  if (!(p == to)) return Verdict::no(claim, "the derivation ends at " + words(P.quiver, p), d.size());
  return Verdict::yes(claim, d.empty() ? "the two are one path" : "a derivation of " + std::to_string(d.size()) + (d.size() == 1 ? " step" : " steps") + " by the equations leads from one to the other", d.size());
}

// The paths a derivation passes through, the first and the last among them.
inline std::vector<Path> trace(const Presentation& P, const Path& from, const Derivation& d) {
  std::vector<Path> out{from};
  for (auto& s : d) {
    auto q = apply(P, out.back(), s);
    if (!q) break;
    out.push_back(std::move(*q));
  }
  return out;
}

// The derivation without its detours: where it passes twice through one path, the steps between are dropped.
inline Derivation shortened(const Presentation& P, const Path& from, const Derivation& d) {
  const auto paths = trace(P, from, d);
  if (paths.size() != d.size() + 1) return d;
  Derivation out;
  for (std::size_t k = 0; k < d.size();) {
    std::size_t last = k;  // the last place the path at k is passed again
    for (std::size_t j = paths.size() - 1; j > k; j--)
      if (paths[j] == paths[k]) {
        last = j;
        break;
      }
    if (last > k) {
      k = last;
    } else {
      out.push_back(d[k]), k++;
    }
  }
  return out;
}

inline Derivation reversed(const Derivation& d) {
  Derivation r(d.rbegin(), d.rend());
  for (auto& s : r) s.forward = !s.forward;
  return r;
}

// ---- completion ---------------------------------------------------------------------------------------------------------------

// A rule left → right with left greater in the shortlex order, and the derivation of it from the equations.
struct Rule {
  Path left, right;
  Derivation why;  // from left to right
};

struct Completion {
  std::vector<Rule> rules;
  bool complete = false;  // every critical pair was joined: the rules are confluent
  std::string reason;     // when not complete, why
  std::size_t pairs = 0;  // the critical pairs examined
};

struct Bounds {
  std::size_t rules = 400;       // at most this many rules
  std::size_t length = 64;       // no rule longer than this
  std::size_t derivation = 4000; // no rule's derivation longer than this
};

namespace detail {

// Shortlex: shorter first, then by the edges in order.
inline bool less(const Path& a, const Path& b) { return a.edges.size() != b.edges.size() ? a.edges.size() < b.edges.size() : a.edges < b.edges; }

inline void append(Derivation& d, const Derivation& more, std::size_t shift = 0) {
  for (Step s : more) s.at += shift, d.push_back(s);
}

// The path reduced by the rules until none applies; the steps taken are added to `log`, in the equations' terms.
inline Path reduce(const std::vector<Rule>& rules, Path p, Derivation* log = nullptr) {
  for (bool again = true; again;) {
    again = false;
    for (std::size_t at = 0; at < p.edges.size() && !again; at++)
      for (const Rule& r : rules) {
        const auto& l = r.left.edges;
        if (at + l.size() > p.edges.size() || !std::equal(l.begin(), l.end(), p.edges.begin() + static_cast<std::ptrdiff_t>(at))) continue;
        p.edges.erase(p.edges.begin() + static_cast<std::ptrdiff_t>(at), p.edges.begin() + static_cast<std::ptrdiff_t>(at + l.size()));
        p.edges.insert(p.edges.begin() + static_cast<std::ptrdiff_t>(at), r.right.edges.begin(), r.right.edges.end());
        if (log) append(*log, r.why, at);
        again = true;
        break;
      }
  }
  return p;
}

// The critical pairs of two rules: the two reducts of each least path on which both apply, with the place of the second.
struct Peak {
  Path first, second;  // the path after rule a at 0 (or at its place), and after rule b
  std::size_t at_b = 0;
  Path top;
};
inline std::vector<Peak> peaks(const Rule& a, const Rule& b, bool same) {
  std::vector<Peak> out;
  const auto &la = a.left.edges, &lb = b.left.edges;
  // A proper suffix of a's left is a proper prefix of b's.
  for (std::size_t k = 1; k < std::min(la.size(), lb.size()); k++) {
    if (!std::equal(lb.begin(), lb.begin() + static_cast<std::ptrdiff_t>(k), la.end() - static_cast<std::ptrdiff_t>(k))) continue;
    Peak p;
    p.top = a.left, p.top.edges.insert(p.top.edges.end(), lb.begin() + static_cast<std::ptrdiff_t>(k), lb.end());
    p.first = {a.left.source, a.right.edges}, p.first.edges.insert(p.first.edges.end(), lb.begin() + static_cast<std::ptrdiff_t>(k), lb.end());
    p.at_b = la.size() - k;
    p.second = {a.left.source, {la.begin(), la.begin() + static_cast<std::ptrdiff_t>(p.at_b)}}, p.second.edges.insert(p.second.edges.end(), b.right.edges.begin(), b.right.edges.end());
    out.push_back(std::move(p));
  }
  // b's left lies inside a's.
  if (!same)
    for (std::size_t at = 0; at + lb.size() <= la.size(); at++) {
      if (!std::equal(lb.begin(), lb.end(), la.begin() + static_cast<std::ptrdiff_t>(at))) continue;
      Peak p;
      p.top = a.left, p.first = a.right, p.at_b = at;
      p.second = {a.left.source, {la.begin(), la.begin() + static_cast<std::ptrdiff_t>(at)}};
      p.second.edges.insert(p.second.edges.end(), b.right.edges.begin(), b.right.edges.end());
      p.second.edges.insert(p.second.edges.end(), la.begin() + static_cast<std::ptrdiff_t>(at + lb.size()), la.end());
      out.push_back(std::move(p));
    }
  return out;
}

}  // namespace detail

// Knuth–Bendix completion of the presentation's equations into rules, within the bounds.
inline Completion complete(const Presentation& P, const Bounds& bounds = {}) {
  Completion K;
  struct Pending {
    Path u, v;
    Derivation why;  // from u to v
  };
  std::deque<Pending> queue;
  for (std::size_t k = 0; k < P.equations.size(); k++) queue.push_back({P.equations[k].left, P.equations[k].right, {Step{0, k, true}}});
  while (!queue.empty()) {
    Pending e = std::move(queue.front());
    queue.pop_front();
    Derivation du, dv;
    const Path u = detail::reduce(K.rules, e.u, &du), v = detail::reduce(K.rules, e.v, &dv);
    if (u == v) continue;
    Rule r;
    if (detail::less(v, u)) {  // u → v, by u ⇐ e.u ⇒ e.v ⇒ v
      r.left = u, r.right = v;
      r.why = reversed(du), detail::append(r.why, e.why), detail::append(r.why, dv);
    } else {
      r.left = v, r.right = u;
      r.why = reversed(dv), detail::append(r.why, reversed(e.why)), detail::append(r.why, du);
    }
    r.why = shortened(P, r.left, r.why);
    if (K.rules.size() >= bounds.rules || r.left.edges.size() > bounds.length || r.why.size() > bounds.derivation) {
      K.reason = "completion did not end within its bounds (" + kernel::count(K.rules.size(), "rule") + " so far)";
      return K;
    }
    K.rules.push_back(r);
    const std::size_t n = K.rules.size() - 1;
    for (std::size_t k = 0; k <= n; k++)
      for (int turn = 0; turn < (k == n ? 1 : 2); turn++) {
        const Rule &a = K.rules[turn == 0 ? n : k], &b = K.rules[turn == 0 ? k : n];
        for (auto& p : detail::peaks(a, b, k == n)) {
          K.pairs++;
          Derivation why = reversed(a.why);            // first ⇐ top
          detail::append(why, b.why, p.at_b);          // top ⇒ second
          queue.push_back({std::move(p.first), std::move(p.second), std::move(why)});
        }
      }
  }
  K.complete = true;
  return K;
}

inline Path normal_form(const Completion& K, const Path& p, Derivation* log = nullptr) { return detail::reduce(K.rules, p, log); }

// What stands behind an answer of inequality: the rules decrease, follow from the equations, and are confluent.
inline Verdict certify(const Presentation& P, const Completion& K) {
  const std::string claim = "the rules of " + P.name + " are a complete rewriting system for it";
  if (!K.complete) return Verdict::unknown(claim, K.reason);
  std::size_t examined = 0;
  for (std::size_t k = 0; k < K.rules.size(); k++) {
    const Rule& r = K.rules[k];
    if (!detail::less(r.right, r.left)) return Verdict::no(claim, "rule " + std::to_string(k + 1) + " does not decrease");
    if (Verdict v = check(P, r.left, r.right, r.why); !v.holds()) return Verdict::no(claim, "rule " + std::to_string(k + 1) + " does not follow from the equations: " + v.reason);
    examined++;
  }
  for (std::size_t i = 0; i < K.rules.size(); i++)
    for (std::size_t j = 0; j < K.rules.size(); j++)
      for (auto& p : detail::peaks(K.rules[i], K.rules[j], i == j)) {
        examined++;
        if (!(detail::reduce(K.rules, p.first) == detail::reduce(K.rules, p.second)))
          return Verdict::no(claim, "the two reducts of " + words(P.quiver, p.top) + " have different normal forms", examined).with("at", words(P.quiver, p.top));
      }
  for (std::size_t k = 0; k < P.equations.size(); k++)
    if (!(detail::reduce(K.rules, P.equations[k].left) == detail::reduce(K.rules, P.equations[k].right)))
      return Verdict::no(claim, "the sides of equation " + std::to_string(k + 1) + " have different normal forms", examined);
  return Verdict::yes(claim, kernel::count(K.rules.size(), "rule") + ", each decreasing and derived from the equations; every critical pair is joinable", examined);
}

// Whether two paths are equal in the presented category, with the derivation when they are.
struct Proof {
  Verdict verdict;
  Derivation derivation;  // from the first path to the second, when it holds
};

inline Proof prove(const Presentation& P, const Completion& K, const Path& u, const Path& v) {
  const std::string claim = words(P.quiver, u) + " = " + words(P.quiver, v) + " in " + P.name;
  if (!composable(P.quiver, u) || !composable(P.quiver, v)) return {Verdict::no(claim, "a side is not a path"), {}};
  if (u.source != v.source || target(P.quiver, u) != target(P.quiver, v)) return {Verdict::no(claim, "the two are not parallel"), {}};
  Derivation du, dv;
  const Path nu = normal_form(K, u, &du), nv = normal_form(K, v, &dv);
  if (nu == nv) {
    detail::append(du, reversed(dv));
    du = shortened(P, u, du);
    Verdict checked = check(P, u, v, du);
    if (!checked.holds()) return {Verdict::unknown(claim, "the derivation found did not check: " + checked.reason), {}};
    return {checked, du};
  }
  if (K.complete)
    return {Verdict::no(claim, "their normal forms differ, and the rules are confluent", K.rules.size()).with("left", words(P.quiver, nu)).with("right", words(P.quiver, nv)), {}};
  return {Verdict::unknown(claim, "their normal forms so far differ, and " + K.reason).with("left", words(P.quiver, nu)).with("right", words(P.quiver, nv)), {}};
}

// ---- the category presented, when it is finite --------------------------------------------------------------------------------

struct Presented {
  finite::Category category;
  std::vector<Path> paths;       // the normal form of each arrow
  std::vector<Index> generator;  // the arrow each generator is
  std::map<std::pair<Index, std::vector<Index>>, Index> at;  // a normal form's arrow

  // The arrow a path is.
  Index arrow(const Completion& K, const Path& p) const {
    const Path n = normal_form(K, p);
    const auto it = at.find({n.source, n.edges});
    return it == at.end() ? none : it->second;
  }
};

// The category whose arrows are the normal forms, when completion ended and they are at most `most`; nothing otherwise.
inline std::optional<Presented> category(const Presentation& P, const Completion& K, std::size_t most = 2000) {
  if (!K.complete) return std::nullopt;
  const Quiver& Q = P.quiver;
  Presented R;
  std::vector<finite::Arrow> arrows;
  auto add = [&](const Path& p) {
    R.at[{p.source, p.edges}] = static_cast<Index>(R.paths.size());
    R.paths.push_back(p);
    arrows.push_back({words(Q, p), p.source, target(Q, p)});
  };
  for (Index a = 0; a < Q.objects.size(); a++) add({a, {}});
  auto irreducible = [&](const Path& p) {  // no rule's left ends the path; its beginnings are irreducible already
    for (const Rule& r : K.rules) {
      const auto& l = r.left.edges;
      if (l.size() <= p.edges.size() && std::equal(l.begin(), l.end(), p.edges.end() - static_cast<std::ptrdiff_t>(l.size()))) return false;
    }
    return true;
  };
  for (std::size_t k = 0; k < R.paths.size(); k++) {
    const Index end = target(Q, R.paths[k]);
    for (Index e = 0; e < Q.edges.size(); e++) {
      if (Q.edges[e].dom != end) continue;
      Path p = R.paths[k];
      p.edges.push_back(e);
      if (!irreducible(p)) continue;
      if (R.paths.size() >= most) return std::nullopt;
      add(p);
    }
  }
  for (Index e = 0; e < Q.edges.size(); e++) R.generator.push_back(R.arrow(K, {Q.edges[e].dom, {e}}));
  R.category = finite::assemble(P.name, Q.objects, std::move(arrows), finite::detail::iota(Q.objects.size()), [&](Index g, Index f) {
    Path p = R.paths[f];
    p.edges.insert(p.edges.end(), R.paths[g].edges.begin(), R.paths[g].edges.end());
    return R.arrow(K, p);
  });
  for (Index g : R.generator)  // the generators that are no identity, each once: what the category is drawn by
    if (!R.category.is_identity(g) && std::find(R.category.basis.begin(), R.category.basis.end(), g) == R.category.basis.end()) R.category.basis.push_back(g);
  return R;
}

}  // namespace kategoria::presentations
