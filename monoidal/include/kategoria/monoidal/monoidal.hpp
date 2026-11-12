// Symmetric monoidal theories: string diagrams, their equality, and their models.
//
// A signature gives types (the kinds of wire) and generators (boxes, each with wires in and wires out). A term is
// built from generators, identities and the symmetry by composition and by the tensor. Held here:
//
//   - typing: whether a term is well formed, with the place where two parts do not meet;
//   - the diagram of a term: wires and boxes, each wire leaving at most one box and entering at most one, with the
//     diagram's own wires in and out in order;
//   - equality of diagrams. Two terms are equal in the free symmetric monoidal category on the signature, that is, by
//     the axioms of symmetric monoidal categories alone, exactly when their diagrams are isomorphic as hypergraphs
//     with interfaces (Joyal and Street 1991; in this form Bonchi, Gadducci, Kissinger, Sobociński and
//     Zanasi 2022). same() decides that by morphe's canonical forms of labelled graphs;
//   - models: a model sends each type to a dimension and each generator to a matrix over a semiring, with the tensor
//     the Kronecker product (functions between finite sets with ×, relations, linear maps with ⊗) or the direct sum
//     (matrices as a PROP). A law of a theory holds in a model when both sides evaluate to one matrix; a failure names
//     the entry at which they differ.
//
// Not here: equality modulo a theory's laws by rewriting (convex double-pushout matches), which is planned. A law
// holding in a model says nothing of the theory at large; a law failing in a model shows it does not follow from laws
// the model satisfies.
//
// Conventions. A sequence lists its parts in the order the wires pass through them. A matrix has a row for each
// output and a column for each input; under the Kronecker product the pair (i, j) is the index i·n + j.

#pragma once

#include <kategoria/finite/category.hpp>
#include <kategoria/kernel/verdict.hpp>

#include <morphe/combinatorics/canonical.hpp>

#include <cstddef>
#include <cstdlib>
#include <limits>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace kategoria::monoidal {

using finite::Index;
using finite::none;
using kernel::Verdict;

struct Generator {
  std::string name;
  std::vector<Index> inputs, outputs;  // types
};
struct Signature {
  std::string name;
  std::vector<std::string> types;
  std::vector<Generator> generators;

  Index type(std::string_view n) const {
    for (Index k = 0; k < types.size(); k++)
      if (types[k] == n) return k;
    return none;
  }
  Index generator(std::string_view n) const {
    for (Index k = 0; k < generators.size(); k++)
      if (generators[k].name == n) return k;
    return none;
  }
};

struct Term {
  enum class Kind { identity, generator, swap, sequence, tensor };
  Kind kind = Kind::identity;
  std::vector<Index> on;    // identity: the types it is on (none: the unit); swap: the two types; generator: the generator
  std::vector<Term> parts;  // sequence and tensor
};

inline Term id(std::vector<Index> types = {}) { return {Term::Kind::identity, std::move(types), {}}; }
inline Term gen(Index g) { return {Term::Kind::generator, {g}, {}}; }
inline Term swap(Index a, Index b) { return {Term::Kind::swap, {a, b}, {}}; }
inline Term seq(std::vector<Term> parts) { return {Term::Kind::sequence, {}, std::move(parts)}; }
inline Term par(std::vector<Term> parts) { return {Term::Kind::tensor, {}, std::move(parts)}; }

inline std::string words(const Signature& S, const Term& t, bool inner = false) {
  switch (t.kind) {
    case Term::Kind::identity: {
      if (t.on.empty()) return "I";
      std::string w;
      for (Index a : t.on) w += (w.empty() ? "" : " ⊗ ") + S.types[a];
      return inner && t.on.size() > 1 ? "(" + w + ")" : w;
    }
    case Term::Kind::generator: return S.generators[t.on[0]].name;
    case Term::Kind::swap: return "σ(" + S.types[t.on[0]] + "," + S.types[t.on[1]] + ")";
    default: {
      std::string w;
      for (auto& p : t.parts) w += (w.empty() ? "" : t.kind == Term::Kind::sequence ? " ; " : " ⊗ ") + words(S, p, true);
      return inner ? "(" + w + ")" : w;
    }
  }
}

inline std::string words(const Signature& S, const std::vector<Index>& types) {
  if (types.empty()) return "I";
  std::string w;
  for (Index a : types) w += (w.empty() ? "" : " ⊗ ") + S.types[a];
  return w;
}

// A term's type, or the place where it is not well formed.
struct Typed {
  Verdict verdict;
  std::vector<Index> in, out;
};

inline Typed type(const Signature& S, const Term& t) {
  const std::string claim = words(S, t) + " is well formed";
  switch (t.kind) {
    case Term::Kind::identity: return {Verdict::yes(claim), t.on, t.on};
    case Term::Kind::generator: return {Verdict::yes(claim), S.generators[t.on[0]].inputs, S.generators[t.on[0]].outputs};
    case Term::Kind::swap: return {Verdict::yes(claim), {t.on[0], t.on[1]}, {t.on[1], t.on[0]}};
    case Term::Kind::tensor: {
      Typed all{Verdict::yes(claim), {}, {}};
      for (auto& p : t.parts) {
        Typed one = type(S, p);
        if (!one.verdict.holds()) return one;
        all.in.insert(all.in.end(), one.in.begin(), one.in.end()), all.out.insert(all.out.end(), one.out.begin(), one.out.end());
      }
      return all;
    }
    default: {
      Typed all{Verdict::yes(claim), {}, {}};
      for (std::size_t k = 0; k < t.parts.size(); k++) {
        Typed one = type(S, t.parts[k]);
        if (!one.verdict.holds()) return one;
        if (k == 0) {
          all.in = one.in;
        } else if (all.out != one.in) {
          return {Verdict::no(claim, words(S, t.parts[k - 1], true) + " ends on " + words(S, all.out) + ", and " + words(S, t.parts[k], true) + " begins on " + words(S, one.in)).with("at", words(S, t.parts[k], true)), {}, {}};
        }
        all.out = one.out;
      }
      return all;
    }
  }
}

// ---- diagrams -----------------------------------------------------------------------------------------------------------------

struct Box {
  Index generator = none;
  std::vector<Index> in, out;  // wires
};
// The wires (each with its type) and boxes of a term, with its wires in and out in order.
struct Diagram {
  std::vector<Index> wires;  // the type of each wire
  std::vector<Box> boxes;
  std::vector<Index> inputs, outputs;
};

// The diagram of a well-formed term.
inline Diagram diagram(const Signature& S, const Term& t) {
  Diagram D;
  auto wire = [&](Index type) { return D.wires.push_back(type), static_cast<Index>(D.wires.size() - 1); };
  switch (t.kind) {
    case Term::Kind::identity:
      for (Index a : t.on) D.inputs.push_back(wire(a));
      D.outputs = D.inputs;
      return D;
    case Term::Kind::generator: {
      Box b{t.on[0], {}, {}};
      for (Index a : S.generators[t.on[0]].inputs) b.in.push_back(wire(a));
      for (Index a : S.generators[t.on[0]].outputs) b.out.push_back(wire(a));
      D.inputs = b.in, D.outputs = b.out, D.boxes.push_back(b);
      return D;
    }
    case Term::Kind::swap: {
      const Index x = wire(t.on[0]), y = wire(t.on[1]);
      D.inputs = {x, y}, D.outputs = {y, x};
      return D;
    }
    case Term::Kind::tensor:
      for (auto& p : t.parts) {
        const Diagram E = diagram(S, p);
        const Index shift = static_cast<Index>(D.wires.size());
        D.wires.insert(D.wires.end(), E.wires.begin(), E.wires.end());
        for (Box b : E.boxes) {
          for (Index& w : b.in) w += shift;
          for (Index& w : b.out) w += shift;
          D.boxes.push_back(b);
        }
        for (Index w : E.inputs) D.inputs.push_back(w + shift);
        for (Index w : E.outputs) D.outputs.push_back(w + shift);
      }
      return D;
    default:
      for (std::size_t k = 0; k < t.parts.size(); k++) {
        const Diagram E = diagram(S, t.parts[k]);
        if (k == 0) {
          D = E;
          continue;
        }
        // The wires into E are the wires out of what stands so far; its others are new.
        std::vector<Index> to(E.wires.size(), none);
        for (std::size_t i = 0; i < E.inputs.size(); i++) to[E.inputs[i]] = D.outputs[i];
        for (Index w = 0; w < E.wires.size(); w++)
          if (to[w] == none) to[w] = wire(E.wires[w]);
        for (Box b : E.boxes) {
          for (Index& w : b.in) w = to[w];
          for (Index& w : b.out) w = to[w];
          D.boxes.push_back(b);
        }
        std::vector<Index> out;
        for (Index w : E.outputs) out.push_back(to[w]);
        D.outputs = out;
      }
      return D;
  }
}

// The depth of each box: one more than the deepest box that feeds it. Boxes of one depth can be drawn side by side.
inline std::vector<Index> depths(const Diagram& D) {
  std::vector<Index> producer(D.wires.size(), none), depth(D.boxes.size(), 0);
  for (Index b = 0; b < D.boxes.size(); b++)
    for (Index w : D.boxes[b].out) producer[w] = b;
  for (bool changed = true; changed;) {
    changed = false;
    for (Index b = 0; b < D.boxes.size(); b++)
      for (Index w : D.boxes[b].in)
        if (producer[w] != none && depth[b] < depth[producer[w]] + 1) depth[b] = depth[producer[w]] + 1, changed = true;
  }
  return depth;
}

// A code equal for two diagrams exactly when they are isomorphic with their interfaces kept; `exact` is false where
// morphe's search gave up, and then nothing is concluded.
struct Code {
  std::string code;
  bool exact = true;
};
inline Code canonical(const Signature& S, const Diagram& D) {
  morphe::combinatorics::LabelledGraph G;
  std::vector<std::string> label(D.wires.size());
  for (Index w = 0; w < D.wires.size(); w++) label[w] = "w:" + S.types[D.wires[w]];
  for (std::size_t k = 0; k < D.inputs.size(); k++) label[D.inputs[k]] += "|in" + std::to_string(k);
  for (std::size_t k = 0; k < D.outputs.size(); k++) label[D.outputs[k]] += "|out" + std::to_string(k);
  G.vertex = label;
  for (const Box& b : D.boxes) {
    const std::size_t v = G.vertex.size();
    G.vertex.push_back("b:" + S.generators[b.generator].name);
    for (std::size_t k = 0; k < b.in.size(); k++) G.edges.emplace_back(v, b.in[k], "i" + std::to_string(k));
    for (std::size_t k = 0; k < b.out.size(); k++) G.edges.emplace_back(v, b.out[k], "o" + std::to_string(k));
  }
  const auto form = morphe::combinatorics::canonical_form(G);
  return {form.code, form.exact};
}

// Whether two terms are equal by the axioms of symmetric monoidal categories alone.
inline Verdict same(const Signature& S, const Term& a, const Term& b) {
  const std::string claim = words(S, a) + " = " + words(S, b) + " in every symmetric monoidal category";
  const Typed ta = type(S, a), tb = type(S, b);
  if (!ta.verdict.holds()) return Verdict::no(claim, "the left side is not well formed: " + ta.verdict.reason);
  if (!tb.verdict.holds()) return Verdict::no(claim, "the right side is not well formed: " + tb.verdict.reason);
  if (ta.in != tb.in || ta.out != tb.out)
    return Verdict::no(claim, "the two have different types").with("left", words(S, ta.in) + " → " + words(S, ta.out)).with("right", words(S, tb.in) + " → " + words(S, tb.out));
  const Diagram da = diagram(S, a), db = diagram(S, b);
  const Code ca = canonical(S, da), cb = canonical(S, db);
  if (!ca.exact || !cb.exact) return Verdict::unknown(claim, "the diagrams are too symmetric for their canonical forms to be found within the bound");
  if (ca.code == cb.code)
    return Verdict::yes(claim, "the two are one diagram: " + std::to_string(da.boxes.size()) + " boxes and " + std::to_string(da.wires.size()) + " wires, joined alike", da.boxes.size() + da.wires.size());
  return Verdict::no(claim, "their diagrams differ, and in the free symmetric monoidal category on " + S.name + " terms are equal only when their diagrams are", da.boxes.size() + db.boxes.size())
      .with("left", std::to_string(da.boxes.size()) + " boxes, " + std::to_string(da.wires.size()) + " wires").with("right", std::to_string(db.boxes.size()) + " boxes, " + std::to_string(db.wires.size()) + " wires");
}

// ---- models -------------------------------------------------------------------------------------------------------------------

enum class Semiring { integer, boolean, modular };

struct Matrix {
  std::size_t rows = 0, cols = 0;  // outputs, inputs
  std::vector<long long> v;        // v[i cols + j]
  long long at(std::size_t i, std::size_t j) const { return v[i * cols + j]; }
  long long& at(std::size_t i, std::size_t j) { return v[i * cols + j]; }
  bool operator==(const Matrix&) const = default;
};

struct Model {
  std::string name;
  Semiring semiring = Semiring::integer;
  long long modulus = 0;                // for Semiring::modular
  bool kronecker = true;                // the tensor: the Kronecker product, or the direct sum
  std::vector<std::size_t> dimension;   // of each type
  std::vector<Matrix> generators;       // of each generator

  long long reduce(long long x) const {
    if (semiring == Semiring::boolean) return x != 0;
    if (semiring == Semiring::modular) return ((x % modulus) + modulus) % modulus;
    return x;
  }
  std::size_t dimension_of(const std::vector<Index>& types) const {
    std::size_t d = kronecker ? 1 : 0;
    for (Index a : types) d = kronecker ? d * dimension[a] : d + dimension[a];
    return d;
  }
};

// A function between finite sets as a matrix: a one in column x at row f(x).
inline Matrix function(const std::vector<Index>& f, std::size_t onto) {
  Matrix M{onto, f.size(), std::vector<long long>(onto * f.size(), 0)};
  for (std::size_t x = 0; x < f.size(); x++) {
    if (f[x] >= onto) throw std::invalid_argument("kategoria::monoidal::function: a value outside the target");
    M.at(f[x], x) = 1;
  }
  return M;
}

inline Verdict well_formed(const Signature& S, const Model& M) {
  const std::string claim = M.name + " is a model of the signature " + S.name;
  if (M.dimension.size() != S.types.size() || M.generators.size() != S.generators.size()) return Verdict::no(claim, "it does not give a dimension to every type and a matrix to every generator");
  if (M.semiring == Semiring::modular && M.modulus < 2) return Verdict::no(claim, "its modulus is less than 2");
  for (Index g = 0; g < S.generators.size(); g++) {
    const std::size_t rows = M.dimension_of(S.generators[g].outputs), cols = M.dimension_of(S.generators[g].inputs);
    if (M.generators[g].rows != rows || M.generators[g].cols != cols || M.generators[g].v.size() != rows * cols)
      return Verdict::no(claim, S.generators[g].name + " is given a matrix of " + std::to_string(M.generators[g].rows) + " × " + std::to_string(M.generators[g].cols) + " where its type asks " + std::to_string(rows) + " × " + std::to_string(cols)).with("at", S.generators[g].name);
  }
  return Verdict::yes(claim, std::string("its tensor is the ") + (M.kronecker ? "Kronecker product" : "direct sum"));
}

namespace detail {
// Products and sums of entries, refused where they outgrow 64 bits.
inline long long times(long long a, long long b) {
  const long long most = std::numeric_limits<long long>::max();
  if (a != 0 && b != 0 && (a == std::numeric_limits<long long>::min() || b == std::numeric_limits<long long>::min() || std::llabs(a) > most / std::llabs(b)))
    throw std::overflow_error("kategoria::monoidal: a matrix entry outgrew 64 bits");
  return a * b;
}
inline long long plus(long long a, long long b) {
  if ((b > 0 && a > std::numeric_limits<long long>::max() - b) || (b < 0 && a < std::numeric_limits<long long>::min() - b))
    throw std::overflow_error("kategoria::monoidal: a matrix entry outgrew 64 bits");
  return a + b;
}
inline Matrix identity(std::size_t n) {
  Matrix I{n, n, std::vector<long long>(n * n, 0)};
  for (std::size_t i = 0; i < n; i++) I.at(i, i) = 1;
  return I;
}
// B after A.
inline Matrix times(const Model& M, const Matrix& B, const Matrix& A) {
  Matrix R{B.rows, A.cols, std::vector<long long>(B.rows * A.cols, 0)};
  for (std::size_t i = 0; i < B.rows; i++)
    for (std::size_t k = 0; k < B.cols; k++) {
      if (!B.at(i, k)) continue;
      for (std::size_t j = 0; j < A.cols; j++) {
        R.at(i, j) = M.reduce(plus(R.at(i, j), times(B.at(i, k), A.at(k, j))));
      }
    }
  return R;
}
inline Matrix tensor(const Model& M, const Matrix& A, const Matrix& B) {
  if (M.kronecker) {
    Matrix R{A.rows * B.rows, A.cols * B.cols, std::vector<long long>(A.rows * B.rows * A.cols * B.cols, 0)};
    for (std::size_t i = 0; i < A.rows; i++)
      for (std::size_t j = 0; j < A.cols; j++)
        for (std::size_t k = 0; k < B.rows; k++)
          for (std::size_t l = 0; l < B.cols; l++) R.at(i * B.rows + k, j * B.cols + l) = M.reduce(times(A.at(i, j), B.at(k, l)));
    return R;
  }
  Matrix R{A.rows + B.rows, A.cols + B.cols, std::vector<long long>((A.rows + B.rows) * (A.cols + B.cols), 0)};
  for (std::size_t i = 0; i < A.rows; i++)
    for (std::size_t j = 0; j < A.cols; j++) R.at(i, j) = A.at(i, j);
  for (std::size_t i = 0; i < B.rows; i++)
    for (std::size_t j = 0; j < B.cols; j++) R.at(A.rows + i, A.cols + j) = B.at(i, j);
  return R;
}
// The symmetry on spaces of dimensions m and n.
inline Matrix symmetry(const Model& M, std::size_t m, std::size_t n) {
  if (M.kronecker) {
    Matrix R{m * n, m * n, std::vector<long long>(m * n * m * n, 0)};
    for (std::size_t i = 0; i < m; i++)
      for (std::size_t j = 0; j < n; j++) R.at(j * m + i, i * n + j) = 1;
    return R;
  }
  Matrix R{m + n, m + n, std::vector<long long>((m + n) * (m + n), 0)};
  for (std::size_t i = 0; i < m; i++) R.at(n + i, i) = 1;
  for (std::size_t j = 0; j < n; j++) R.at(j, m + j) = 1;
  return R;
}
}  // namespace detail

// The matrix a well-formed term denotes in a model.
inline Matrix evaluate(const Signature& S, const Model& M, const Term& t) {
  switch (t.kind) {
    case Term::Kind::identity: return detail::identity(M.dimension_of(t.on));
    case Term::Kind::generator: {
      Matrix G = M.generators[t.on[0]];
      for (auto& x : G.v) x = M.reduce(x);
      return G;
    }
    case Term::Kind::swap: return detail::symmetry(M, M.dimension[t.on[0]], M.dimension[t.on[1]]);
    case Term::Kind::tensor: {
      Matrix R = detail::identity(M.kronecker ? 1 : 0);
      for (auto& p : t.parts) R = detail::tensor(M, R, evaluate(S, M, p));
      return R;
    }
    default: {
      Matrix R = evaluate(S, M, t.parts.front());
      for (std::size_t k = 1; k < t.parts.size(); k++) R = detail::times(M, evaluate(S, M, t.parts[k]), R);
      return R;
    }
  }
}

struct Law {
  std::string name;
  Term left, right;
};
struct Theory {
  Signature signature;
  std::vector<Law> laws;
};

// Whether the laws are well formed: each side typed, the two of one type.
inline Verdict well_formed(const Theory& T) {
  const std::string claim = T.signature.name + " is a theory";
  for (auto& law : T.laws) {
    const Typed l = type(T.signature, law.left), r = type(T.signature, law.right);
    if (!l.verdict.holds()) return Verdict::no(claim, "in the law " + law.name + ": " + l.verdict.reason).with("at", law.name);
    if (!r.verdict.holds()) return Verdict::no(claim, "in the law " + law.name + ": " + r.verdict.reason).with("at", law.name);
    if (l.in != r.in || l.out != r.out)
      return Verdict::no(claim, "the sides of the law " + law.name + " have different types: " + words(T.signature, l.in) + " → " + words(T.signature, l.out) + " and " + words(T.signature, r.in) + " → " + words(T.signature, r.out)).with("at", law.name);
  }
  return Verdict::yes(claim, kernel::count(T.signature.types.size(), "type") + ", " + kernel::count(T.signature.generators.size(), "generator") + ", " + kernel::count(T.laws.size(), "law"));
}

// Whether one equation holds in a model.
inline Verdict holds_in(const Signature& S, const Model& M, const Term& left, const Term& right, const std::string& name = {}) {
  const std::string claim = (name.empty() ? words(S, left) + " = " + words(S, right) : name) + " holds in " + M.name;
  const Typed l = type(S, left), r = type(S, right);
  if (!l.verdict.holds()) return Verdict::no(claim, l.verdict.reason);
  if (!r.verdict.holds()) return Verdict::no(claim, r.verdict.reason);
  if (l.in != r.in || l.out != r.out) return Verdict::no(claim, "the two sides have different types");
  const Matrix A = evaluate(S, M, left), B = evaluate(S, M, right);
  for (std::size_t i = 0; i < A.rows; i++)
    for (std::size_t j = 0; j < A.cols; j++)
      if (A.at(i, j) != B.at(i, j))
        return Verdict::no(claim, "the two sides differ at output " + std::to_string(i) + ", input " + std::to_string(j) + ": " + std::to_string(A.at(i, j)) + " and " + std::to_string(B.at(i, j)), A.v.size())
            .with("at", "output " + std::to_string(i) + ", input " + std::to_string(j)).with("left", std::to_string(A.at(i, j))).with("right", std::to_string(B.at(i, j)));
  return Verdict::yes(claim, "both sides are one matrix of " + std::to_string(A.rows) + " × " + std::to_string(A.cols), A.v.size());
}

// Each law of a theory in a model.
inline std::vector<Verdict> laws_in(const Theory& T, const Model& M) {
  std::vector<Verdict> out;
  for (auto& law : T.laws) out.push_back(holds_in(T.signature, M, law.left, law.right, law.name));
  return out;
}
// Whether a model satisfies a theory: the first law that fails, or none.
inline Verdict satisfies(const Theory& T, const Model& M) {
  const std::string claim = M.name + " is a model of " + T.signature.name;
  if (Verdict v = well_formed(T.signature, M); !v.holds()) return Verdict::no(claim, v.reason);
  std::size_t examined = 0;
  const auto verdicts = laws_in(T, M);
  for (std::size_t k = 0; k < verdicts.size(); k++) {
    examined += verdicts[k].examined;
    if (!verdicts[k].holds()) {
      Verdict out = Verdict::no(claim, "the law " + T.laws[k].name + " fails: " + verdicts[k].reason, examined);
      out.evidence = verdicts[k].evidence;
      return out.with("law", T.laws[k].name);
    }
  }
  return Verdict::yes(claim, T.laws.empty() ? "the theory has no laws" : T.laws.size() == 1 ? "its one law holds, entry by entry" : "each of its " + std::to_string(T.laws.size()) + " laws holds, entry by entry", examined);
}

}  // namespace kategoria::monoidal
