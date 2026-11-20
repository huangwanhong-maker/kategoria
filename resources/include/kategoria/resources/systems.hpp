// Whether the order of grants matters, decided on a finite system; and whether an operator treats renamed things alike.
//
// A grant system on a finite set of states is a partial action of grants on states (a grant may not apply in a state). A
// word of grants acts by applying them in turn, first to last. Order does not matter from an initial state exactly when
// every two grants commute on every state reachable from it, undefinedness included (a grant possible in one order and not
// in the other is an effect of order): then words with the same grants, counted, reach the same state from any reachable
// state, that is, the action factors through the free commutative monoid (the survey Evolutionary heterogeneous resource
// allocation, Part II §6 and Part IV §3). Where only some grants commute, the commuting pairs are the independence relation
// of a trace monoid (Mazurkiewicz 1977; Diekert and Rozenberg 1995), which a search can use to evaluate each trace once.
//
// The action is made total by a sink for undefinedness, and the maps the words induce on states form the transition monoid
// (a finite monoid; Rhodes and Steinberg 2009, The q-theory of Finite Semigroups, ch. 1). It is built by closing the
// grants' maps under composition and then validated by kategoria as a one-object category, the search and the check apart.
// Order-independence from the initial state is commutativity of the monoid restricted to the reachable states.
//
// An operator of a search on a finite set of genotypes is a kernel: a probability for each outcome from each input (or each
// pair of inputs, for a crossover). It treats renamed items or recipients alike when it is equivariant: renaming the input
// and then applying the operator gives the renamed outcome, K(σx, σy) = K(x, y), the naturality of K for the renaming in the
// Kleisli category of distributions. The survey found no prior categorical treatment of evolutionary operators (Part IV §5);
// this is the finite, decidable part of one.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/resources/algebra.hpp>

#include <algorithm>
#include <cstddef>
#include <map>
#include <queue>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace kategoria::resources {

struct System {
  std::string name;
  std::vector<std::string> states, grants;
  std::vector<std::vector<Index>> action;  // action[g][x]: the state after grant g in state x, or none where it does not apply
  Index initial = 0;
};

struct TransitionMonoid {
  std::vector<std::vector<Index>> maps;    // each element as a map on the states and the sink (the last index)
  std::vector<std::string> words;          // a shortest word inducing it ("1" for the empty word)
  std::vector<Index> table;                // table[g n + f] = g ∘ f, g after f
  Verdict verdict;                         // the monoid as kategoria validates it
};

struct Independence {
  Verdict verdict;                         // whether order does not matter from the initial state
  std::vector<std::vector<char>> commute;  // commute[g][h]: g and h commute on every reachable state
  std::vector<Index> reachable;            // the states reachable from the initial one
};

namespace detail {

inline std::optional<std::string> malformed(const System& S) {
  if (S.states.empty()) return "it has no states";
  if (S.initial >= S.states.size()) return "its initial state is not one of its states";
  if (S.action.size() != S.grants.size()) return "it does not give the action of every grant";
  for (std::size_t g = 0; g < S.action.size(); g++) {
    if (S.action[g].size() != S.states.size()) return "the grant " + S.grants[g] + " is not given in every state";
    for (Index y : S.action[g])
      if (y != none && y >= S.states.size()) return "the grant " + S.grants[g] + " leads to no state";
  }
  return std::nullopt;
}

inline std::vector<Index> total(const System& S, std::size_t g) {
  const Index sink = static_cast<Index>(S.states.size());
  std::vector<Index> m(S.states.size() + 1, sink);
  for (std::size_t x = 0; x < S.states.size(); x++) m[x] = S.action[g][x] == none ? sink : S.action[g][x];
  return m;
}

inline std::string state_name(const System& S, Index x) { return x >= S.states.size() ? std::string("(not possible)") : S.states[x]; }

}  // namespace detail

inline std::vector<Index> reachable(const System& S) {
  std::vector<Index> out;
  if (detail::malformed(S)) return out;
  std::vector<char> seen(S.states.size(), 0);
  std::queue<Index> q;
  q.push(S.initial);
  seen[S.initial] = 1;
  while (!q.empty()) {
    const Index x = q.front();
    q.pop();
    out.push_back(x);
    for (const auto& a : S.action)
      if (a[x] != none && !seen[a[x]]) seen[a[x]] = 1, q.push(a[x]);
  }
  std::sort(out.begin(), out.end());
  return out;
}

// The transition monoid, closed under composition up to `limit` elements, and validated by kategoria.
inline TransitionMonoid transition_monoid(const System& S, std::size_t limit = 1500) {
  TransitionMonoid M;
  const std::string claim = "the maps the words of " + S.name + " induce form a monoid";
  if (auto why = detail::malformed(S)) {
    M.verdict = Verdict::no(claim, *why);
    return M;
  }
  const std::size_t n = S.states.size() + 1;
  std::vector<Index> id(n);
  for (Index x = 0; x < n; x++) id[x] = x;
  std::map<std::vector<Index>, Index> index;
  M.maps.push_back(id);
  M.words.push_back("1");
  index.emplace(id, 0);
  std::vector<std::vector<Index>> generators;
  for (std::size_t g = 0; g < S.grants.size(); g++) generators.push_back(detail::total(S, g));
  for (std::size_t i = 0; i < M.maps.size(); i++) {
    for (std::size_t g = 0; g < generators.size(); g++) {
      std::vector<Index> m(n);
      for (Index x = 0; x < n; x++) m[x] = generators[g][M.maps[i][x]];  // the word, then g
      if (index.count(m)) continue;
      if (M.maps.size() >= limit) {
        M.verdict = Verdict::unknown(claim, "the monoid has more than " + std::to_string(limit) + " elements; not closed");
        return M;
      }
      index.emplace(m, static_cast<Index>(M.maps.size()));
      M.words.push_back(M.words[i] == "1" ? S.grants[g] : M.words[i] + " " + S.grants[g]);
      M.maps.push_back(std::move(m));
    }
  }
  const std::size_t k = M.maps.size();
  M.table.assign(k * k, 0);
  for (std::size_t a = 0; a < k; a++)
    for (std::size_t b = 0; b < k; b++) {
      std::vector<Index> m(n);
      for (Index x = 0; x < n; x++) m[x] = M.maps[a][M.maps[b][x]];  // a after b
      M.table[a * k + b] = index.at(m);
    }
  try {
    const auto C = finite::monoid(M.words, M.table, "the transition monoid of " + S.name);
    const Verdict v = finite::validate(C);
    M.verdict = v.holds() ? Verdict::yes(claim, std::to_string(k) + " elements, validated by kategoria as a one-object category", v.examined)
                          : Verdict::no(claim, "the closure is not a monoid: " + v.reason, v.examined);
  } catch (const std::exception& e) {
    M.verdict = Verdict::no(claim, e.what());
  }
  return M;
}

// Whether the order of grants matters from the initial state, and which pairs commute.
inline Independence independence(const System& S) {
  Independence I;
  const std::string claim = "in " + S.name + ", the order of grants does not matter from " + (S.states.empty() ? std::string("?") : S.states[S.initial]);
  if (auto why = detail::malformed(S)) {
    I.verdict = Verdict::no(claim, *why);
    return I;
  }
  I.reachable = reachable(S);
  const std::size_t G = S.grants.size();
  I.commute.assign(G, std::vector<char>(G, 1));
  std::size_t examined = 0;
  std::string first;
  std::vector<std::string> witness;
  for (std::size_t g = 0; g < G; g++)
    for (std::size_t h = g + 1; h < G; h++) {
      const auto mg = detail::total(S, g), mh = detail::total(S, h);
      for (Index x : I.reachable) {
        examined++;
        const Index gh = mh[mg[x]], hg = mg[mh[x]];   // g then h; h then g
        if (gh != hg) {
          I.commute[g][h] = I.commute[h][g] = 0;
          if (first.empty()) {
            first = "from " + S.states[x] + ", " + S.grants[g] + " then " + S.grants[h] + " gives " + detail::state_name(S, gh) + ", but " + S.grants[h] + " then " + S.grants[g] + " gives " + detail::state_name(S, hg);
            witness = {S.states[x], S.grants[g] + ", " + S.grants[h], detail::state_name(S, gh), detail::state_name(S, hg)};
          }
          break;
        }
      }
    }
  if (first.empty())
    I.verdict = Verdict::yes(claim, "every two grants commute on each of the " + std::to_string(I.reachable.size()) + " reachable states, so the action factors through the free commutative monoid", examined);
  else
    I.verdict = Verdict::no(claim, first, examined).with("at", witness[0]).with("grants", witness[1]).with("left", witness[2]).with("right", witness[3]);
  return I;
}

// ---- Operators as kernels -------------------------------------------------------------------------------------------------

struct Kernel {
  std::string name;
  std::vector<std::string> points;
  std::vector<std::vector<Rational>> p;                  // p[x][y]: the probability of y from x (a mutation)
};

struct Kernel2 {
  std::string name;
  std::vector<std::string> points;
  std::vector<std::vector<std::vector<Rational>>> p;     // p[x][y][z]: the probability of z from the parents x, y (a crossover)
};

inline Verdict is_kernel(const Kernel& K) {
  const std::string claim = K.name + " is a kernel on its " + std::to_string(K.points.size()) + " points";
  if (K.p.size() != K.points.size()) return Verdict::no(claim, "it does not give a row for every point");
  for (std::size_t x = 0; x < K.p.size(); x++) {
    if (K.p[x].size() != K.points.size()) return Verdict::no(claim, "the row of " + K.points[x] + " is not of the size of the points");
    Rational s(0);
    for (const auto& q : K.p[x]) {
      if (q.sign() < 0) return Verdict::no(claim, "a probability from " + K.points[x] + " is negative").with("at", K.points[x]);
      s += q;
    }
    if (s != Rational(1)) return Verdict::no(claim, "the probabilities from " + K.points[x] + " sum to " + s.str()).with("at", K.points[x]);
  }
  return Verdict::yes(claim, "every row is a distribution", K.points.size());
}

namespace detail {

inline std::optional<std::string> not_permutations(const std::vector<std::vector<Index>>& actions, std::size_t n) {
  for (std::size_t a = 0; a < actions.size(); a++) {
    if (actions[a].size() != n) return "renaming " + std::to_string(a + 1) + " does not act on every point";
    std::vector<char> hit(n, 0);
    for (Index y : actions[a]) {
      if (y >= n || hit[y]) return "renaming " + std::to_string(a + 1) + " is not a permutation of the points";
      hit[y] = 1;
    }
  }
  return std::nullopt;
}

}  // namespace detail

// K(σx, σy) = K(x, y) for every renaming σ given (generators of the group suffice).
inline Verdict equivariant(const Kernel& K, const std::vector<std::vector<Index>>& renamings) {
  const std::string claim = K.name + " treats renamed points alike (it is natural for the renamings)";
  const Verdict kv = is_kernel(K);
  if (!kv.holds()) return Verdict::no(claim, kv.reason);
  if (auto why = detail::not_permutations(renamings, K.points.size())) return Verdict::no(claim, *why);
  std::size_t examined = 0;
  for (std::size_t a = 0; a < renamings.size(); a++)
    for (std::size_t x = 0; x < K.points.size(); x++)
      for (std::size_t y = 0; y < K.points.size(); y++) {
        examined++;
        const auto& s = renamings[a];
        if (K.p[s[x]][s[y]] != K.p[x][y])
          return Verdict::no(claim, "from " + K.points[x] + " it gives " + K.points[y] + " with probability " + K.p[x][y].str() + ", but from " + K.points[s[x]] + " it gives " + K.points[s[y]] + " with " + K.p[s[x]][s[y]].str(), examined)
              .with("at", K.points[x] + " → " + K.points[y]).with("renaming", std::to_string(a + 1));
      }
  return Verdict::yes(claim, "checked for each renaming given, at every pair of points", examined);
}

inline Verdict equivariant(const Kernel2& K, const std::vector<std::vector<Index>>& renamings) {
  const std::string claim = K.name + " treats renamed points alike (it is natural for the renamings)";
  const std::size_t n = K.points.size();
  if (K.p.size() != n) return Verdict::no(claim, "it is not given for every pair of parents");
  for (std::size_t x = 0; x < n; x++) {
    if (K.p[x].size() != n) return Verdict::no(claim, "it is not given for every pair of parents");
    for (std::size_t y = 0; y < n; y++) {
      if (K.p[x][y].size() != n) return Verdict::no(claim, "it is not given for every outcome");
      Rational s(0);
      for (const auto& q : K.p[x][y]) {
        if (q.sign() < 0) return Verdict::no(claim, "a probability is negative");
        s += q;
      }
      if (s != Rational(1)) return Verdict::no(claim, "the probabilities from the parents " + K.points[x] + ", " + K.points[y] + " sum to " + s.str());
    }
  }
  if (auto why = detail::not_permutations(renamings, n)) return Verdict::no(claim, *why);
  std::size_t examined = 0;
  for (std::size_t a = 0; a < renamings.size(); a++) {
    const auto& s = renamings[a];
    for (std::size_t x = 0; x < n; x++)
      for (std::size_t y = 0; y < n; y++)
        for (std::size_t z = 0; z < n; z++) {
          examined++;
          if (K.p[s[x]][s[y]][s[z]] != K.p[x][y][z])
            return Verdict::no(claim, "from the parents " + K.points[x] + ", " + K.points[y] + " it gives " + K.points[z] + " with " + K.p[x][y][z].str() + ", but renamed, with " + K.p[s[x]][s[y]][s[z]].str(), examined)
                .with("at", K.points[x] + ", " + K.points[y] + " → " + K.points[z]).with("renaming", std::to_string(a + 1));
        }
  }
  return Verdict::yes(claim, "checked for each renaming given, at every pair of parents and outcome", examined);
}

}  // namespace kategoria::resources
