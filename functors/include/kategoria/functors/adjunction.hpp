// Adjunctions and monads on finite categories: verified, and found from universal arrows.
//
// An adjunction L ⊣ R between C and D is given by its unit and counit and verified by the triangle identities
// (Mac Lane 1971, IV.1, Theorem 2). A left adjoint of a given R is found object by object: R has one exactly when
// every c has a universal arrow to R (IV.1, Theorem 2 (ii)); the search either builds L with its unit and counit,
// which verify_adjunction() then checks, or names an object with no universal arrow.
//
// A monad is verified by its unit and associativity laws (VI.1); every adjunction gives one, and a monad's
// Eilenberg–Moore and Kleisli categories are built (VI.2, VI.5).

#pragma once

#include <kategoria/functors/functor.hpp>

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::functors {

// left : C → D, right : D → C, unit : 1 ⇒ right ∘ left, counit : left ∘ right ⇒ 1.
struct Adjunction {
  Functor left, right;
  Transformation unit, counit;
};

inline Verdict verify_adjunction(const Category& C, const Category& D, const Adjunction& A) {
  const std::string claim = (A.left.name.empty() ? "L" : A.left.name) + " ⊣ " + (A.right.name.empty() ? "R" : A.right.name);
  const Functor RL = compose(A.right, A.left), LR = compose(A.left, A.right);
  Verdict v = kernel::both(kernel::both(verify(C, D, A.left), verify(D, C, A.right)),
                           kernel::both(natural(C, C, identity(C), RL, A.unit), natural(D, D, LR, identity(D), A.counit)));
  if (!v.holds()) {
    v.reason = v.claim + " fails: " + v.reason, v.claim = claim;
    return v;
  }
  for (Index c = 0; c < C.objects.size(); c++) {  // ε_{L c} ∘ L(η_c) = 1_{L c}
    const Index left = D.compose(A.counit.components[A.left.objects[c]], A.left.arrows[A.unit.components[c]]);
    if (left != D.identity[A.left.objects[c]])
      return Verdict::no(claim, "the first triangle identity fails at " + C.objects[c], v.examined).with("at", C.objects[c]).with("left", D.arrows[left].name).with("right", D.arrows[D.identity[A.left.objects[c]]].name);
  }
  for (Index d = 0; d < D.objects.size(); d++) {  // R(ε_d) ∘ η_{R d} = 1_{R d}
    const Index left = C.compose(A.right.arrows[A.counit.components[d]], A.unit.components[A.right.objects[d]]);
    if (left != C.identity[A.right.objects[d]])
      return Verdict::no(claim, "the second triangle identity fails at " + D.objects[d], v.examined).with("at", D.objects[d]).with("left", C.arrows[left].name).with("right", C.arrows[C.identity[A.right.objects[d]]].name);
  }
  return Verdict::yes(claim, "the unit and the counit are natural and both triangle identities hold at every object", v.examined + C.objects.size() + D.objects.size());
}

struct FoundAdjunction {
  Verdict verdict;
  std::optional<Adjunction> adjunction;
};

// A left adjoint of R : D → C. Where some object of C has no universal arrow to R, the verdict names it.
inline FoundAdjunction left_adjoint(const Category& C, const Category& D, const Functor& R) {
  const std::string name = R.name.empty() ? "R" : R.name;
  const std::string claim = name + " has a left adjoint";
  if (Verdict v = verify(D, C, R); !v.holds()) return {v, std::nullopt};
  const std::size_t m = C.objects.size();
  // The h : d → d′ with R h ∘ eta = g, when there is exactly one; none otherwise.
  auto mediating = [&](Index d, Index eta, Index d2, Index g) {
    Index found = none;
    for (Index h : D.hom(d, d2))
      if (C.compose(R.arrows[h], eta) == g) {
        if (found != none) return none;
        found = h;
      }
    return found;
  };
  std::vector<Index> L(m, none), eta(m, none);
  std::size_t examined = 0;
  for (Index c = 0; c < m; c++) {
    for (Index d = 0; d < D.objects.size() && L[c] == none; d++)
      for (Index e : C.hom(c, R.objects[d])) {
        bool universal = true;
        for (Index d2 = 0; d2 < D.objects.size() && universal; d2++)
          for (Index g : C.hom(c, R.objects[d2])) {
            examined++;
            if (mediating(d, e, d2, g) == none) {
              universal = false;
              break;
            }
          }
        if (universal) {
          L[c] = d, eta[c] = e;
          break;
        }
      }
    if (L[c] == none)
      return {Verdict::no(claim, C.objects[c] + " has no universal arrow to " + name + ": no arrow " + C.objects[c] + " → " + name + "(d) through which every other factors once", examined).with("at", C.objects[c]), std::nullopt};
  }
  Adjunction A;
  A.right = R;
  A.left = {"L", L, std::vector<Index>(C.size(), none)};
  for (Index f = 0; f < C.size(); f++) A.left.arrows[f] = mediating(L[C.dom(f)], eta[C.dom(f)], L[C.cod(f)], C.compose(eta[C.cod(f)], f));
  A.unit = {"η", eta};
  A.counit = {"ε", {}};
  for (Index d = 0; d < D.objects.size(); d++) A.counit.components.push_back(mediating(L[R.objects[d]], eta[R.objects[d]], d, C.identity[R.objects[d]]));
  Verdict v = verify_adjunction(C, D, A);
  if (!v.holds()) return {Verdict::unknown(claim, "the adjoint built from the universal arrows did not verify: " + v.reason), std::nullopt};
  std::string where;
  for (Index c = 0; c < m; c++) where += (c ? ", " : "") + C.objects[c] + " ↦ " + D.objects[L[c]];
  return {Verdict::yes(claim, "every object has a universal arrow; the adjoint built from them verifies, with both triangle identities", examined + v.examined).with("witness", where), A};
}

// A right adjoint of L : C → D: a left adjoint of L between the opposite categories, read back.
inline FoundAdjunction right_adjoint(const Category& C, const Category& D, const Functor& L) {
  const std::string name = L.name.empty() ? "L" : L.name;
  FoundAdjunction found = left_adjoint(finite::opposite(D), finite::opposite(C), L);
  found.verdict.claim = name + " has a right adjoint";
  if (!found.adjunction) {
    if (found.verdict.fails()) found.verdict.reason = std::string(found.verdict.piece("at")) + " has no universal arrow from " + name + ": no arrow " + name + "(c) → " + std::string(found.verdict.piece("at")) + " through which every other factors once";
    return found;
  }
  Adjunction A;
  A.left = L;
  A.right = found.adjunction->left, A.right.name = "R";
  A.unit = found.adjunction->counit, A.unit.name = "η";
  A.counit = found.adjunction->unit, A.counit.name = "ε";
  Verdict v = verify_adjunction(C, D, A);
  if (!v.holds()) return {Verdict::unknown(found.verdict.claim, "the adjoint read back from the opposite categories did not verify: " + v.reason), std::nullopt};
  found.verdict.reason = "every object has a universal arrow; the adjoint built from them verifies, with both triangle identities";
  found.adjunction = A;
  return found;
}

// ---- monads -------------------------------------------------------------------------------------------------------------------

// T : C → C with unit : 1 ⇒ T and mult : T T ⇒ T.
struct Monad {
  Functor T;
  Transformation unit, mult;
};

inline Verdict verify_monad(const Category& C, const Monad& M) {
  const std::string claim = (M.T.name.empty() ? "T" : M.T.name) + " is a monad on " + C.name;
  const Functor TT = compose(M.T, M.T);
  Verdict v = kernel::both(verify(C, C, M.T), kernel::both(natural(C, C, identity(C), M.T, M.unit), natural(C, C, TT, M.T, M.mult)));
  if (!v.holds()) {
    v.reason = v.claim + " fails: " + v.reason, v.claim = claim;
    return v;
  }
  for (Index c = 0; c < C.objects.size(); c++) {
    const Index Tc = M.T.objects[c], mu = M.mult.components[c], id = C.identity[Tc];
    if (C.compose(mu, M.unit.components[Tc]) != id) return Verdict::no(claim, "the left unit law fails at " + C.objects[c], v.examined).with("at", C.objects[c]);   // μ ∘ η_T = 1
    if (C.compose(mu, M.T.arrows[M.unit.components[c]]) != id) return Verdict::no(claim, "the right unit law fails at " + C.objects[c], v.examined).with("at", C.objects[c]);  // μ ∘ T η = 1
    if (C.compose(mu, M.mult.components[Tc]) != C.compose(mu, M.T.arrows[mu]))  // μ ∘ μ_T = μ ∘ T μ
      return Verdict::no(claim, "associativity fails at " + C.objects[c], v.examined).with("at", C.objects[c]);
  }
  return Verdict::yes(claim, "its unit and multiplication are natural, and the unit laws and associativity hold at every object", v.examined + 3 * C.objects.size());
}

// The monad R L of an adjunction, with unit η and multiplication R ε L.
inline Monad monad_of(const Adjunction& A) {
  Monad M;
  M.T = compose(A.right, A.left), M.T.name = "T";
  M.unit = A.unit;
  M.mult = {"μ", {}};
  for (Index Lc : A.left.objects) M.mult.components.push_back(A.right.arrows[A.counit.components[Lc]]);
  return M;
}
inline Monad identity_monad(const Category& C) { return {identity(C), identity_transformation(C, C, identity(C)), identity_transformation(C, C, identity(C))}; }

// The Eilenberg–Moore category of a monad: its objects the algebras (a, h : T a → a) with h ∘ η_a = 1 and
// h ∘ μ_a = h ∘ T h, its arrows the f : a → b with f ∘ h = k ∘ T f.
struct Algebras {
  Category category;
  std::vector<std::pair<Index, Index>> algebras;  // (a, h)
  std::vector<Index> arrows;                      // the arrow of C beneath each arrow
  Functor forgetful;                              // to C
};

inline Algebras eilenberg_moore(const Category& C, const Monad& M) {
  Algebras E;
  std::vector<std::string> names;
  for (Index a = 0; a < C.objects.size(); a++)
    for (Index h : C.hom(M.T.objects[a], a))
      if (C.compose(h, M.unit.components[a]) == C.identity[a] && C.compose(h, M.mult.components[a]) == C.compose(h, M.T.arrows[h])) {
        E.algebras.push_back({a, h});
        names.push_back("(" + C.objects[a] + "," + C.arrows[h].name + ")");
      }
  const Index m = static_cast<Index>(E.algebras.size());
  std::vector<finite::Arrow> arrows;
  std::map<std::array<Index, 3>, Index> at;
  for (int pass = 0; pass < 2; pass++)
    for (Index x = 0; x < m; x++)
      for (Index y = 0; y < m; y++)
        for (Index f : C.hom(E.algebras[x].first, E.algebras[y].first)) {
          if (C.compose(f, E.algebras[x].second) != C.compose(E.algebras[y].second, M.T.arrows[f])) continue;
          const bool id = x == y && C.is_identity(f);
          if (id != (pass == 0)) continue;
          at[{x, y, f}] = static_cast<Index>(arrows.size());
          E.arrows.push_back(f);
          arrows.push_back({id ? "id_" + names[x] : C.arrows[f].name + ":" + names[x] + "→" + names[y], x, y});
        }
  const auto ends = arrows;
  E.forgetful = {"U", {}, E.arrows};
  for (auto& [a, h] : E.algebras) E.forgetful.objects.push_back(a);
  E.category = finite::assemble(C.name + "^" + (M.T.name.empty() ? "T" : M.T.name), std::move(names), std::move(arrows), finite::detail::iota(m),
                                [&](Index g, Index f) { return at.at({ends[f].dom, ends[g].cod, C.compose(E.arrows[g], E.arrows[f])}); });
  return E;
}

// The Kleisli category of a monad: the objects of C, an arrow a ⇸ b for each arrow a → T b of C, composed as
// g • f = μ ∘ T g ∘ f, with the units as identities.
struct Kleisli {
  Category category;
  std::vector<Index> arrows;  // the arrow a → T b of C beneath each arrow
  Functor free;               // C → the Kleisli category: f ↦ η ∘ f
};

inline Kleisli kleisli(const Category& C, const Monad& M) {
  Kleisli K;
  const Index m = static_cast<Index>(C.objects.size());
  std::vector<finite::Arrow> arrows;
  std::map<std::array<Index, 3>, Index> at;  // (source, target, arrow of C)
  for (Index a = 0; a < m; a++) {
    at[{a, a, M.unit.components[a]}] = a;
    K.arrows.push_back(M.unit.components[a]);
    arrows.push_back({"id_" + C.objects[a], a, a});
  }
  for (Index a = 0; a < m; a++)
    for (Index b = 0; b < m; b++)
      for (Index f : C.hom(a, M.T.objects[b])) {
        if (at.count({a, b, f})) continue;
        at[{a, b, f}] = static_cast<Index>(arrows.size());
        K.arrows.push_back(f);
        arrows.push_back({C.arrows[f].name + ":" + C.objects[a] + "⇸" + C.objects[b], a, b});
      }
  const auto ends = arrows;
  K.category = finite::assemble(C.name + "_" + (M.T.name.empty() ? "T" : M.T.name), C.objects, std::move(arrows), finite::detail::iota(m), [&](Index g, Index f) {
    return at.at({ends[f].dom, ends[g].cod, C.compose(M.mult.components[ends[g].cod], C.compose(M.T.arrows[K.arrows[g]], K.arrows[f]))});
  });
  K.free = {"F", finite::detail::iota(m), {}};
  for (Index f = 0; f < C.size(); f++) K.free.arrows.push_back(at.at({C.dom(f), C.cod(f), C.compose(M.unit.components[C.cod(f)], f)}));
  return K;
}

}  // namespace kategoria::functors
