// A session: a script's statements carried out one after another, each answered with a verdict and what there is to draw.
//
// The grammar is language.hpp's; the meaning of each statement is given here, on the library's modules. A statement
// that defines something (a category, a functor, …) is answered with the verdict that it is one, and it is kept under
// its name only when it is. A statement that cannot be carried out (an unknown name, an arrow that does not compose)
// is answered with the reason, and the script goes on.
//
// The answer of a script is a list of outcomes, each a map:
//   line, text       where the statement stands, and its text
//   kind, name       what it is: "category", "functor", …, "check", "find"; and what it names
//   status           "holds", "fails", "undecided", or "error" when it could not be carried out
//   claim, reason    the verdict's
//   evidence         [{role, value}], examined
//   view             what there is to draw, by its "type": category, functor, transformation, adjunction, sets, cone,
//                    derivation, string, theory, laws, table

#pragma once

#include <kategoria/functors/adjunction.hpp>
#include <kategoria/functors/functor.hpp>
#include <kategoria/limits/limits.hpp>
#include <kategoria/monoidal/monoidal.hpp>
#include <kategoria/presentations/presentation.hpp>
#include <kategoria/script/document.hpp>
#include <kategoria/script/language.hpp>
#include <kategoria/sets/copresheaf.hpp>

#include <morphe/algebra/finite_group.hpp>

#include <cstdlib>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace kategoria::script {

using finite::Category;
using finite::Index;
using finite::none;
using kernel::Verdict;
using morphe::formal::ParseNode;

// A statement that cannot be carried out, with the reason.
struct Refusal : std::runtime_error {
  using std::runtime_error::runtime_error;
};

class Session {
 public:
  // The largest category a statement may build.
  std::size_t most_arrows = 3000;

  // Carries out a script; the list of its outcomes.
  Value run(std::string_view script) {
    Value out = Value::list();
    for (const Statement& s : statements(script)) {
      Value o = Value::map();
      try {
        const auto parsed = grammar().parse(s.text);
        if (!parsed.accepted) throw Refusal(syntax(s, parsed));
        o = carry_out(parsed.tree.children.at(0));
      } catch (const std::exception& e) {
        o = Value::map();
        o.set("kind", "error").set("status", "error").set("reason", std::string(e.what()));
      }
      o.set("line", s.line).set("text", s.text);
      out.push(std::move(o));
    }
    return out;
  }

 private:
  struct Cat {
    Category C;
    bool finite = true;
    std::optional<presentations::Presentation> P;
    presentations::Completion K;
    std::optional<presentations::Presented> built;
    std::vector<std::string> factors;                                      // of a product
    std::optional<std::pair<functors::Functor, std::string>> projection;   // to the category it was made from
  };
  struct Fun {
    functors::Functor F;
    std::string source, target;
  };
  struct Nat {
    functors::Transformation t;
    std::string from, to;
  };
  struct Set {
    sets::Copresheaf X;
    std::string on;
  };
  struct Mod {
    monoidal::Model M;
    std::string theory;
  };
  struct Dia {
    monoidal::Term term;
    std::string theory;
  };

  std::map<std::string, Cat> cats_;
  std::map<std::string, Fun> funs_;
  std::map<std::string, Nat> nats_;
  std::map<std::string, Set> sets_;
  std::map<std::string, monoidal::Theory> theories_;
  std::map<std::string, Mod> models_;
  std::map<std::string, Dia> diagrams_;

  // ---- names --------------------------------------------------------------------------------------------------------------------

  void forget(const std::string& name) { cats_.erase(name), funs_.erase(name), nats_.erase(name), sets_.erase(name), theories_.erase(name), models_.erase(name), diagrams_.erase(name); }

  template <class Map>
  static const typename Map::mapped_type& named(const Map& map, const std::string& name, const char* what) {
    const auto it = map.find(name);
    if (it != map.end()) return it->second;
    std::string known;
    for (auto& [k, v] : map) known += (known.empty() ? "" : ", ") + k;
    throw Refusal(std::string("there is no ") + what + " named " + name + (known.empty() ? std::string("; none has been defined") : "; those defined are " + known));
  }
  const Cat& cat(const std::string& name) const {
    const Cat& e = named(cats_, name, "category");
    if (!e.finite) throw Refusal(name + " is not built whole (its arrows are too many, or its completion did not end); only equalities of paths can be asked of it");
    return e;
  }
  const Fun& fun(const std::string& name) const { return named(funs_, name, "functor"); }
  const Set& set(const std::string& name) const { return named(sets_, name, "set-valued functor"); }

  static Index object_of(const Category& C, const std::string& name) {
    const Index a = C.object(name);
    if (a == none) throw Refusal(C.name + " has no object named " + name);
    return a;
  }
  // The arrow of this name: a generator of a presented category by its own name, else an arrow by its name.
  static Index arrow_named(const Cat& e, const std::string& name) {
    if (e.P && e.built)
      for (Index k = 0; k < e.P->quiver.edges.size(); k++)
        if (e.P->quiver.edges[k].name == name) return e.built->generator[k];
    return e.C.arrow(name);
  }
  static std::string syntax(const Statement& s, const morphe::formal::BnfParse& p) {
    std::size_t line = s.line, column = 1;
    for (std::size_t k = 0; k < p.furthest && k < s.text.size(); k++) {
      if (s.text[k] == '\n') line++, column = 1;
      else column++;
    }
    std::string expected;
    for (std::size_t k = 0; k < p.expected.size() && k < 8; k++) expected += (k ? ", " : "") + p.expected[k];
    if (p.expected.size() > 8) expected += ", …";
    return "line " + std::to_string(line) + ", column " + std::to_string(column) + ": " +
           (p.furthest < s.text.size() ? "this is not understood from \"" + s.text.substr(p.furthest, 12) + "\"" : std::string("the statement ends too soon")) +
           (expected.empty() ? "" : "; what could come here: " + expected);
  }

  // ---- expressions --------------------------------------------------------------------------------------------------------------

  // The single name an expression is, or null.
  static const ParseNode* bare(const ParseNode& n) {
    if (n.name == "name") return &n;
    if ((n.name == "expr" || n.name == "ethen" || n.name == "etensor" || n.name == "eatom") && n.children.size() == 1) return bare(n.children[0]);
    return nullptr;
  }

  // The arrow of a finite category an expression denotes.
  static Index arrow_of(const Cat& e, const ParseNode& n) {
    const Category& C = e.C;
    if (n.name == "expr" || n.name == "eatom") return arrow_of(e, n.children.at(0));
    if (n.name == "eparen") return arrow_of(e, *n.child("expr"));
    if (n.name == "eid") return C.identity[object_of(C, name_of(*n.child("name")))];
    if (n.name == "eswap") throw Refusal("a symmetry has no meaning in a category; it belongs to a theory");
    if (n.name == "etensor") {
      if (n.children.size() != 1) throw Refusal("a tensor has no meaning in a category; it belongs to a theory");
      return arrow_of(e, n.children[0]);
    }
    if (n.name == "name") {
      const Index f = arrow_named(e, name_of(n));
      if (f == none) throw Refusal(C.name + " has no arrow named " + name_of(n) + (C.object(name_of(n)) != none ? " (it is an object; its identity is written id " + name_of(n) + ")" : ""));
      return f;
    }
    // ethen: in the order travelled; eafter: the last written is travelled first.
    std::vector<Index> parts;
    for (const ParseNode* p : n.all("etensor")) parts.push_back(arrow_of(e, *p));
    if (n.name == "eafter") std::reverse(parts.begin(), parts.end());
    Index f = parts.at(0);
    for (std::size_t k = 1; k < parts.size(); k++) {
      if (C.cod(f) != C.dom(parts[k])) throw Refusal(C.arrows[parts[k]].name + " does not follow " + C.arrows[f].name + ": one ends at " + C.objects[C.cod(f)] + ", the other begins at " + C.objects[C.dom(parts[k])]);
      f = C.compose(parts[k], f);
    }
    return f;
  }

  // The path of generators an expression denotes in a presentation.
  static presentations::Path path_of(const presentations::Presentation& P, const ParseNode& n) {
    const presentations::Quiver& Q = P.quiver;
    if (n.name == "expr" || n.name == "eatom") return path_of(P, n.children.at(0));
    if (n.name == "eparen") return path_of(P, *n.child("expr"));
    if (n.name == "eid") {
      const std::string a = name_of(*n.child("name"));
      for (Index k = 0; k < Q.objects.size(); k++)
        if (Q.objects[k] == a) return {k, {}};
      throw Refusal(P.name + " has no object named " + a);
    }
    if (n.name == "eswap") throw Refusal("a symmetry has no meaning in a category; it belongs to a theory");
    if (n.name == "etensor") {
      if (n.children.size() != 1) throw Refusal("a tensor has no meaning in a category; it belongs to a theory");
      return path_of(P, n.children[0]);
    }
    if (n.name == "name") {
      for (Index k = 0; k < Q.edges.size(); k++)
        if (Q.edges[k].name == name_of(n)) return {Q.edges[k].dom, {k}};
      throw Refusal(P.name + " has no generator named " + name_of(n));
    }
    std::vector<presentations::Path> parts;
    for (const ParseNode* p : n.all("etensor")) parts.push_back(path_of(P, *p));
    if (n.name == "eafter") std::reverse(parts.begin(), parts.end());
    presentations::Path path = parts.at(0);
    for (std::size_t k = 1; k < parts.size(); k++) {
      if (presentations::target(Q, path) != parts[k].source)
        throw Refusal(presentations::words(Q, parts[k]) + " does not follow " + presentations::words(Q, path) + ": one ends at " + Q.objects[presentations::target(Q, path)] + ", the other begins at " + Q.objects[parts[k].source]);
      path.edges.insert(path.edges.end(), parts[k].edges.begin(), parts[k].edges.end());
    }
    return path;
  }

  // The term of a theory an expression denotes.
  monoidal::Term term_of(const std::string& theory, const ParseNode& n) const {
    const monoidal::Signature& S = named(theories_, theory, "theory").signature;
    auto type = [&](const std::string& w) {
      const Index a = S.type(w);
      if (a == none) throw Refusal(theory + " has no type named " + w);
      return a;
    };
    if (n.name == "expr" || n.name == "eatom") return term_of(theory, n.children.at(0));
    if (n.name == "eparen") return term_of(theory, *n.child("expr"));
    if (n.name == "eid") return name_of(*n.child("name")) == "I" ? monoidal::id() : monoidal::id({type(name_of(*n.child("name")))});
    if (n.name == "eswap") {
      const auto both = n.all("name");
      return monoidal::swap(type(name_of(*both.at(0))), type(name_of(*both.at(1))));
    }
    if (n.name == "name") {
      const std::string w = name_of(n);
      if (S.generator(w) != none) return monoidal::gen(S.generator(w));
      if (S.type(w) != none) return monoidal::id({S.type(w)});
      if (w == "I") return monoidal::id();
      const auto it = diagrams_.find(w);
      if (it != diagrams_.end() && it->second.theory == theory) return it->second.term;
      throw Refusal(theory + " has no generator, type or diagram named " + w);
    }
    std::vector<monoidal::Term> parts;
    for (const ParseNode* p : n.all(n.name == "etensor" ? "eatom" : "etensor")) parts.push_back(term_of(theory, *p));
    if (parts.size() == 1) return parts[0];
    if (n.name == "etensor") return monoidal::par(std::move(parts));
    if (n.name == "eafter") std::reverse(parts.begin(), parts.end());
    return monoidal::seq(std::move(parts));
  }

  // ---- views --------------------------------------------------------------------------------------------------------------------

  static Value verdict_into(Value o, const Verdict& v) {
    o.set("status", std::string(kernel::word(v.status))).set("claim", v.claim).set("reason", v.reason).set("examined", v.examined);
    Value evidence = Value::list();
    for (auto& e : v.evidence) evidence.push(Value::map().set("role", e.role).set("value", e.value));
    return o.set("evidence", std::move(evidence));
  }
  static Value outcome(const std::string& kind, const std::string& name, const Verdict& v, Value view = Value()) {
    Value o = Value::map();
    o.set("kind", kind).set("name", name);
    o = verdict_into(std::move(o), v);
    if (view.kind() != Value::Kind::null) o.set("view", std::move(view));
    return o;
  }

  static Value view_of(const Cat& e) {
    const Category& C = e.C;
    Value v = Value::map();
    v.set("type", "category").set("name", e.finite ? C.name : e.P->name).set("finite", e.finite);
    Value facts = Value::list();
    if (!e.finite) {
      const presentations::Quiver& Q = e.P->quiver;
      v.set("objects", Value::of(Q.objects));
      Value arrows = Value::list();
      for (auto& g : Q.edges) arrows.push(Value::map().set("name", g.name).set("dom", g.dom).set("cod", g.cod).set("kind", "generator"));
      v.set("arrows", std::move(arrows));
      facts.push("not built whole: only its generators are drawn");
    } else {
      v.set("objects", Value::of(C.objects));
      const auto gens = finite::generators(C);
      std::vector<char> is_gen(C.size(), 0);
      for (Index g : gens) is_gen[g] = 1;
      Value arrows = Value::list();
      for (Index f = 0; f < C.size(); f++)
        arrows.push(Value::map().set("name", C.arrows[f].name).set("dom", C.dom(f)).set("cod", C.cod(f)).set("kind", C.is_identity(f) ? "identity" : is_gen[f] ? "generator" : "composite"));
      v.set("arrows", std::move(arrows)).set("generators", Value::of(gens));
      if (C.size() <= 48) {
        Value table = Value::list();
        for (Index g = 0; g < C.size(); g++) {
          Value row = Value::list();
          for (Index f = 0; f < C.size(); f++) row.push(C.compose(g, f) == none ? Value(-1) : Value(C.compose(g, f)));
          table.push(std::move(row));
        }
        v.set("table", std::move(table));
      }
      facts.push(kernel::count(C.objects.size(), "object") + ", " + kernel::count(C.size(), "arrow") + ", generated by " + std::to_string(gens.size()) + " of them");
      if (finite::is_discrete(C)) facts.push("discrete: identities only");
      else if (finite::is_thin(C)) facts.push("thin: at most one arrow between two objects, a preorder");
      if (C.size() <= 400 && !finite::is_discrete(C) && finite::is_groupoid(C)) facts.push(C.objects.size() == 1 ? "one object and every arrow invertible: a group" : "every arrow invertible: a groupoid");
      else if (C.objects.size() == 1) facts.push("one object: a monoid");
      const auto initial = finite::initial_objects(C), terminal = finite::terminal_objects(C);
      if (!initial.empty()) facts.push("initial object " + C.objects[initial[0]]);
      if (!terminal.empty()) facts.push("terminal object " + C.objects[terminal[0]]);
      const auto parts = finite::components(C);
      const std::size_t count = parts.empty() ? 0 : *std::max_element(parts.begin(), parts.end()) + 1;
      if (count > 1) facts.push(std::to_string(count) + " connected components");
    }
    if (e.P) {
      Value equations = Value::list();
      for (auto& [l, r] : e.P->equations) equations.push(presentations::words(e.P->quiver, l) + " = " + presentations::words(e.P->quiver, r));
      v.set("equations", std::move(equations));
      facts.push("presented by " + kernel::count(e.P->quiver.edges.size(), "generator") + " and " + kernel::count(e.P->equations.size(), "equation") + "; " +
                 (e.K.complete ? "completed into " + kernel::count(e.K.rules.size(), "rule") : e.K.reason));
    }
    return v.set("facts", std::move(facts));
  }
  Value view_of(const Fun& f) const {
    return Value::map().set("type", "functor").set("name", f.F.name).set("source", view_of(named(cats_, f.source, "category"))).set("target", view_of(named(cats_, f.target, "category")))
        .set("objects", Value::of(f.F.objects)).set("arrows", Value::of(f.F.arrows));
  }
  Value view_of(const Set& x) const {
    const Cat& e = cat(x.on);
    Value v = Value::map();
    v.set("type", "sets").set("name", x.X.name).set("category", view_of(e));
    Value elements = Value::list(), actions = Value::list();
    for (auto& names : x.X.elements) elements.push(Value::of(names));
    for (Index g : finite::generators(e.C)) actions.push(Value::map().set("arrow", g).set("map", Value::of(x.X.action[g])));
    return v.set("elements", std::move(elements)).set("actions", std::move(actions));
  }
  static Value view_of(const monoidal::Signature& S, const monoidal::Term& t) {
    const monoidal::Diagram D = monoidal::diagram(S, t);
    const auto depth = monoidal::depths(D);
    Value v = Value::map(), wires = Value::list(), boxes = Value::list();
    for (Index w : D.wires) wires.push(S.types[w]);
    for (Index b = 0; b < D.boxes.size(); b++)
      boxes.push(Value::map().set("name", S.generators[D.boxes[b].generator].name).set("in", Value::of(D.boxes[b].in)).set("out", Value::of(D.boxes[b].out)).set("depth", depth[b]));
    return v.set("words", monoidal::words(S, t)).set("wires", std::move(wires)).set("boxes", std::move(boxes)).set("inputs", Value::of(D.inputs)).set("outputs", Value::of(D.outputs));
  }
  static Value strings(const monoidal::Signature& S, const monoidal::Term& left, const monoidal::Term* right = nullptr) {
    Value v = Value::map();
    v.set("type", "string");
    if (monoidal::type(S, left).verdict.holds()) v.set("left", view_of(S, left));
    if (right && monoidal::type(S, *right).verdict.holds()) v.set("right", view_of(S, *right));
    return v;
  }
  Value cone_view(const Cat& e, const functors::Functor& D, const limits::Cone& K, bool colimit) const {
    return Value::map().set("type", "cone").set("category", view_of(e)).set("colimit", colimit).set("shape", Value::map().set("objects", Value::of(D.objects)).set("arrows", Value::of(D.arrows)))
        .set("apex", K.apex).set("legs", Value::of(K.legs));
  }
  static Value table(std::vector<std::string> columns, Value rows) { return Value::map().set("type", "table").set("columns", Value::of(columns)).set("rows", std::move(rows)); }

  // ---- statements ---------------------------------------------------------------------------------------------------------------

  Value carry_out(const ParseNode& n) {
    if (n.name == "category") return category(n);
    if (n.name == "functor") return functor(n);
    if (n.name == "transformation") return transformation(n);
    if (n.name == "sets") return sets_of(n);
    if (n.name == "theory") return theory(n);
    if (n.name == "model") return model(n);
    if (n.name == "diagram") return diagram(n);
    if (n.name == "check") return check(n.children.at(0));
    return find(n.children.at(0));
  }

  // Refuses a category of more arrows than a statement may build, before it is built: its table has the square of them.
  void too_many(const std::string& name, std::size_t arrows) const {
    if (arrows > most_arrows) throw Refusal(name + " would have " + std::to_string(arrows) + " arrows, more than the " + std::to_string(most_arrows) + " a statement may build");
  }

  Value keep(const std::string& name, Cat e, Verdict v) {
    if (e.finite) too_many(name, e.C.size());
    if (e.finite) e.C.name = name;
    Value view = view_of(e);
    if (v.holds() || v.status == kernel::Status::undecided) forget(name), cats_[name] = std::move(e);
    return outcome("category", name, v, std::move(view));
  }

  static Category group_of(const morphe::algebra::PermutationGroup& G, std::size_t degree) {
    std::vector<std::string> names;
    for (const auto& p : G.elements) {  // in cycle notation
      std::string w;
      std::vector<char> seen(degree, 0);
      for (std::size_t i = 0; i < degree; i++) {
        if (seen[i] || p[i] == i) continue;
        w += "(";
        for (std::size_t j = i; !seen[j]; j = p[j]) seen[j] = 1, w += (j == i ? "" : " ") + std::to_string(j);
        w += ")";
      }
      names.push_back(w.empty() ? "e" : w);
    }
    return finite::group(G.group.order(), G.group.table, G.group.name, names);
  }

  Value category(const ParseNode& n) {
    const std::string name = name_of(*n.child("name"));
    Cat e;
    if (const ParseNode* block = n.child("cblock")) {
      presentations::Presentation P;
      P.name = name;
      auto object = [&](const std::string& w) {
        for (Index k = 0; k < P.quiver.objects.size(); k++)
          if (P.quiver.objects[k] == w) return k;
        P.quiver.objects.push_back(w);
        return static_cast<Index>(P.quiver.objects.size() - 1);
      };
      for (const ParseNode* item : block->all("citem")) {
        const ParseNode& it = item->children.at(0);
        if (it.name == "objects")
          for (const ParseNode* o : it.all("name")) object(name_of(*o));
        if (it.name == "edge") {
          const auto ends = it.all("name");
          const Index dom = object(name_of(*ends.at(0))), cod = object(name_of(*ends.at(1)));
          for (const ParseNode* g : it.child("names")->all("name")) {
            for (auto& old : P.quiver.edges)
              if (old.name == name_of(*g)) throw Refusal("the generator " + old.name + " is declared twice");
            P.quiver.edges.push_back({name_of(*g), dom, cod});
          }
        }
      }
      for (const ParseNode* item : block->all("citem")) {
        const ParseNode& it = item->children.at(0);
        if (it.name != "equation") continue;
        const auto sides = it.all("expr");
        P.equations.push_back({path_of(P, *sides.at(0)), path_of(P, *sides.at(1))});
      }
      if (Verdict v = presentations::well_formed(P); !v.holds()) return outcome("category", name, v);
      e.K = presentations::complete(P);
      e.built = presentations::category(P, e.K, most_arrows);
      e.P = P;
      if (!e.built) {
        e.finite = false;
        const Verdict open = e.K.complete ? Verdict::unknown(name + " is a finite category", (e.K.rules.empty() ? std::string("it needs no rule") : "its " + kernel::count(e.K.rules.size(), "rule") + (e.K.rules.size() == 1 ? " is" : " are") + " complete") +
                                                                                                 ", and its arrows are more than " + std::to_string(most_arrows) + ": it is not built whole, and equalities of paths in it are still decided")
                                          : Verdict::unknown(name + " is a finite category", e.K.reason + "; paths whose normal forms coincide are still proved equal");
        return keep(name, std::move(e), open);
      }
      e.C = e.built->category;
      Verdict v = finite::validate(e.C);
      v.claim = name + " is a category";
      v.reason = "from " + kernel::count(P.quiver.edges.size(), "generator") + " and " + kernel::count(P.equations.size(), "equation") + ", completed into " + kernel::count(e.K.rules.size(), "rule") + ": " + v.reason;
      return keep(name, std::move(e), v);
    }
    const ParseNode& x = n.child("cexpr")->children.at(0);
    if (x.name == "cfamily") {
      const std::string family = x.child("cfam")->text;
      const std::size_t k = std::strtoull(x.child("number")->text.c_str(), nullptr, 10);
      auto within = [&](std::size_t most) {
        if (k > most) throw Refusal(family + " " + std::to_string(k) + " is too large here: at most " + std::to_string(most));
      };
      if (family == "chain") within(12), e.C = finite::chain(k);
      if (family == "discrete") within(24), e.C = finite::discrete(k);
      if (family == "subsets") within(4), e.C = finite::subsets(k);
      if (family == "divisors") {
        within(100000);
        if (k == 0) throw Refusal("divisors of 0 are not finitely many");
        e.C = finite::divisors(k);
      }
      if (family == "finset") within(3), e.C = finite::finset(k);
      if (family == "simplex") within(3), e.C = finite::simplex(k);
      if (family == "mult") {
        within(24);
        if (k == 0) throw Refusal("the integers modulo 0 are not finite");
        e.C = finite::multiplicative(k);
      }
      if (family == "cyclic") {
        within(60);
        if (k == 0) throw Refusal("a cyclic group has at least one element");
        const auto G = morphe::algebra::cyclic(k);
        e.C = finite::group(k, G.table, "ℤ/" + std::to_string(k), finite::detail::numbered(k));
      }
      if (family == "symmetric" || family == "dihedral") {
        within(family == "symmetric" ? 5 : 30);
        if (k < (family == "symmetric" ? 2u : 3u)) throw Refusal(family == "symmetric" ? "the symmetric group on at least 2 points" : "the dihedral group of a polygon of at least 3 sides");
        morphe::algebra::Permutation turn(k), flip(k);
        for (std::size_t i = 0; i < k; i++) turn[i] = static_cast<std::uint32_t>((i + 1) % k), flip[i] = static_cast<std::uint32_t>(family == "symmetric" ? (i < 2 ? 1 - i : i) : (k - i) % k);
        e.C = group_of(morphe::algebra::permutation_group({turn, flip}, k, family == "symmetric" ? "S" + std::to_string(k) : "D" + std::to_string(k)), k);
      }
    } else if (x.name == "cplain") {
      if (x.text == "arrow") e.C = finite::chain(2);
      if (x.text == "point") e.C = finite::discrete(1);
      if (x.text == "iso") e.C = finite::preorder({"0", "1"}, {{1, 1}, {1, 1}});
      if (x.text == "pair") e.C = finite::assemble("pair", {"0", "1"}, {{"id_0", 0, 0}, {"id_1", 1, 1}, {"u", 0, 1}, {"v", 0, 1}}, {0, 1}, [](Index g, Index f) { return f < 2 ? g : f; }), e.C.basis = {2, 3};
      if (x.text == "quaternion") {
        const auto G = morphe::algebra::quaternion();
        e.C = finite::group(G.order(), G.table, "Q8");
      }
    } else if (x.name == "cunary") {
      const std::string op = x.child("cuop")->text, of = name_of(*x.child("name"));
      if (op == "op") e.C = finite::opposite(cat(of).C);
      if (op == "skeleton") {
        auto S = finite::skeleton(cat(of).C);
        functors::Functor in{"the inclusion", S.objects, S.arrows};
        e.C = std::move(S.category), e.projection.emplace(in, of);
      }
      if (op == "arrows") {
        const Category& C = cat(of).C;
        auto A = functors::functor_category(finite::chain(2), C, most_arrows);
        for (Index k = 0; k < A.functors.size(); k++) A.category.objects[k] = C.arrows[A.functors[k].arrows[2]].name;
        for (Index k = 0; k < A.category.size(); k++) {
          const auto& [from, to] = A.between[k];
          A.category.arrows[k].name = A.category.is_identity(k) ? "id_" + A.category.objects[from]
                                                                : "(" + C.arrows[A.transformations[k].components[0]].name + "," + C.arrows[A.transformations[k].components[1]].name + "):" + A.category.objects[from] + "→" + A.category.objects[to];
        }
        e.C = std::move(A.category);
      }
      if (op == "elements") {
        const Set& X = set(of);
        auto E = sets::elements(cat(X.on).C, X.X);
        e.C = std::move(E.category), e.projection.emplace(E.projection, X.on);
      }
      if (op == "subobjects") {
        const Set& X = set(of);
        e.C = sets::subobjects(cat(X.on).C, X.X);
      }
      if (op == "algebras" || op == "kleisli") {
        const Fun& L = fun(of);
        const Category &C = cat(L.source).C, &D = cat(L.target).C;
        const auto found = functors::right_adjoint(C, D, L.F);
        if (!found.adjunction) throw Refusal(of + " has no right adjoint, and so gives no monad: " + found.verdict.reason);
        functors::Monad M = functors::monad_of(*found.adjunction);
        M.T.name = "T";
        if (op == "algebras") {
          auto A = functors::eilenberg_moore(C, M);
          e.C = std::move(A.category), e.projection.emplace(A.forgetful, L.source);
        } else {
          e.C = functors::kleisli(C, M).category;
        }
      }
    } else {
      const std::string op = x.child("cbop")->text;
      const auto two = x.all("name");
      const std::string a = name_of(*two.at(0)), b = name_of(*two.at(1));
      if (op == "product") too_many(name, cat(a).C.size() * cat(b).C.size()), e.C = finite::product(cat(a).C, cat(b).C), e.factors = {a, b};
      if (op == "sum") e.C = finite::coproduct(cat(a).C, cat(b).C);
      if (op == "slice" || op == "coslice") {
        const Category& C = cat(a).C;
        auto S = op == "slice" ? finite::slice(C, object_of(C, b)) : finite::coslice(C, object_of(C, b));
        functors::Functor to{op == "slice" ? "the source" : "the target", {}, S.arrows};
        for (Index f : S.objects) to.objects.push_back(op == "slice" ? C.dom(f) : C.cod(f));
        e.C = std::move(S.category), e.projection.emplace(to, a);
      }
      if (op == "functors") e.C = functors::functor_category(cat(a).C, cat(b).C, most_arrows).category;
      if (op == "comma") {
        const Fun &F = fun(a), &G = fun(b);
        if (F.target != G.target) throw Refusal(a + " and " + b + " do not end in one category");
        auto K = functors::comma(cat(F.source).C, cat(G.source).C, cat(F.target).C, F.F, G.F);
        e.C = std::move(K.category), e.projection.emplace(K.first, F.source);
      }
    }
    Verdict v = finite::validate(e.C);
    v.claim = name + " is a category";
    return keep(name, std::move(e), v);
  }

  // ---- functors -----------------------------------------------------------------------------------------------------------------

  Value keep(const std::string& name, functors::Functor F, const std::string& source, const std::string& target, Verdict v, Value view = Value()) {
    F.name = name;
    if (v.claim.find("⊣") == std::string::npos) v.claim = name + " is a functor " + source + " → " + target;
    Fun f{std::move(F), source, target};
    if (view.kind() == Value::Kind::null) view = view_of(f);
    if (v.holds()) forget(name), funs_[name] = std::move(f);
    return outcome("functor", name, v, std::move(view));
  }
  Value adjunction_view(const std::string& c, const std::string& d, const functors::Adjunction& A) const {
    return Value::map().set("type", "adjunction").set("source", view_of(cat(c))).set("target", view_of(cat(d)))
        .set("left", Value::map().set("name", A.left.name).set("objects", Value::of(A.left.objects)).set("arrows", Value::of(A.left.arrows)))
        .set("right", Value::map().set("name", A.right.name).set("objects", Value::of(A.right.objects)).set("arrows", Value::of(A.right.arrows)))
        .set("unit", Value::of(A.unit.components)).set("counit", Value::of(A.counit.components));
  }

  Value functor(const ParseNode& n) {
    const auto names = n.all("name");
    const std::string name = name_of(*names.at(0));
    if (const ParseNode* block = n.child("ablock")) {
      const std::string source = name_of(*names.at(1)), target = name_of(*names.at(2));
      const Cat &c = cat(source), &d = cat(target);
      const Category &C = c.C, &D = d.C;
      functors::Options fixed;
      fixed.limit = 2;
      fixed.objects.assign(C.objects.size(), none), fixed.arrows.assign(C.size(), none);
      for (const ParseNode* a : block->all("assign")) {
        const std::string left = name_of(*a->child("name"));
        const ParseNode& right = *a->child("expr");
        const Index f = arrow_named(c, left);
        if (f == none && C.object(left) != none) {
          const ParseNode* to = bare(right);
          if (!to) throw Refusal("the object " + left + " is to be sent to an object of " + target);
          fixed.objects[C.object(left)] = object_of(D, name_of(*to));
        } else if (f != none) {
          fixed.arrows[f] = arrow_of(d, right);
        } else {
          throw Refusal(source + " has no object or arrow named " + left);
        }
      }
      const std::string claim = name + " is a functor " + source + " → " + target;
      for (Index f = 0; f < C.size(); f++) {  // the ends of each arrow sent
        if (fixed.arrows[f] == none) continue;
        for (int end = 0; end < 2; end++) {
          const Index a = end ? C.cod(f) : C.dom(f), image = end ? D.cod(fixed.arrows[f]) : D.dom(fixed.arrows[f]);
          if (fixed.objects[a] != none && fixed.objects[a] != image)
            return outcome("functor", name, Verdict::no(claim, C.typed(f) + " is sent to " + D.typed(fixed.arrows[f]) + ", while " + C.objects[a] + " is sent to " + D.objects[fixed.objects[a]]).with("at", C.arrows[f].name));
          fixed.objects[a] = image;
        }
      }
      if (c.P) {  // the equations, where every generator in them is sent
        auto image = [&](const presentations::Path& p) {
          Index at = fixed.objects[p.source] == none ? none : D.identity[fixed.objects[p.source]];
          for (Index g : p.edges) {
            const Index to = fixed.arrows[c.built->generator[g]];
            if (to == none || at == none || D.cod(at) != D.dom(to)) return none;
            at = D.compose(to, at);
          }
          return at;
        };
        for (auto& [l, r] : c.P->equations) {
          const Index a = image(l), b = image(r);
          if (a != none && b != none && a != b)
            return outcome("functor", name, Verdict::no(claim, "it does not respect the equation " + presentations::words(c.P->quiver, l) + " = " + presentations::words(c.P->quiver, r) + ": the sides are sent to " + D.arrows[a].name +
                                                                   " and " + D.arrows[b].name).with("at", presentations::words(c.P->quiver, l) + " = " + presentations::words(c.P->quiver, r)).with("left", D.arrows[a].name).with("right", D.arrows[b].name));
        }
      }
      std::vector<functors::Functor> found;
      functors::for_each_functor(C, D, [&](const functors::Functor& F) { return found.push_back(F), true; }, fixed);
      if (found.empty()) return outcome("functor", name, Verdict::no(claim, "no functor sends these objects and arrows as asked: what is given contradicts a composite"));
      if (found.size() > 1) {
        std::string free;
        for (Index a = 0; a < C.objects.size(); a++)
          if (found[0].objects[a] != found[1].objects[a]) free += (free.empty() ? "" : ", ") + C.objects[a];
        for (Index g : finite::generators(C))
          if (found[0].arrows[g] != found[1].arrows[g]) free += (free.empty() ? "" : ", ") + C.arrows[g].name;
        return outcome("functor", name, Verdict::unknown(claim, "what is given leaves it open: more than one functor sends these as asked; say also where " + free + " go"));
      }
      found[0].name = name;
      return keep(name, found[0], source, target, functors::verify(C, D, found[0]));
    }
    const ParseNode& x = n.child("fexpr")->children.at(0);
    if (x.name == "ftwo") {
      const auto two = x.all("name");
      const Fun &G = fun(name_of(*two.at(0))), &F = fun(name_of(*two.at(1)));
      if (F.target != G.source) throw Refusal(name_of(*two.at(1)) + " ends in " + F.target + ", and " + name_of(*two.at(0)) + " begins in " + G.source);
      const auto H = functors::compose(G.F, F.F);
      return keep(name, H, F.source, G.target, functors::verify(cat(F.source).C, cat(G.target).C, H));
    }
    if (x.name == "fthree") {
      const auto three = x.all("name");
      const std::string source = name_of(*three.at(0)), target = name_of(*three.at(1));
      const auto F = functors::constant(cat(source).C, cat(target).C, object_of(cat(target).C, name_of(*three.at(2))));
      return keep(name, F, source, target, functors::verify(cat(source).C, cat(target).C, F));
    }
    const std::string op = x.child("fop")->text, of = name_of(*x.child("name"));
    if (op == "identity") return keep(name, functors::identity(cat(of).C), of, of, functors::verify(cat(of).C, cat(of).C, functors::identity(cat(of).C)));
    if (op == "left adjoint" || op == "right adjoint") {
      const Fun& G = fun(of);
      const bool left = op == "left adjoint";
      // A left adjoint of G : D → C runs C → D, with G on the right; a right adjoint of G : C → D runs D → C.
      const auto found = left ? functors::left_adjoint(cat(G.target).C, cat(G.source).C, G.F) : functors::right_adjoint(cat(G.source).C, cat(G.target).C, G.F);
      if (!found.adjunction) return outcome("functor", name, found.verdict);
      functors::Adjunction A = *found.adjunction;
      (left ? A.left : A.right).name = name, (left ? A.right : A.left).name = of;
      Verdict v = found.verdict;
      v.claim = left ? name + " ⊣ " + of : of + " ⊣ " + name;
      return keep(name, left ? A.left : A.right, G.target, G.source, v, left ? adjunction_view(G.target, G.source, A) : adjunction_view(G.source, G.target, A));
    }
    if (op == "diagonal") {
      const Category& C = cat(of).C;
      std::string square;
      for (auto& [k, e] : cats_)
        if (e.factors == std::vector<std::string>{of, of}) square = k;
      if (square.empty()) {
        square = of + "×" + of;
        too_many(square, C.size() * C.size());
        Cat e;
        e.C = finite::product(C, C), e.C.name = square, e.factors = {of, of};
        cats_[square] = std::move(e);
      }
      functors::Functor F{name, {}, {}};
      for (Index a = 0; a < C.objects.size(); a++) F.objects.push_back(a * static_cast<Index>(C.objects.size()) + a);
      for (Index f = 0; f < C.size(); f++) F.arrows.push_back(f * static_cast<Index>(C.size()) + f);
      return keep(name, F, of, square, functors::verify(C, cat(square).C, F));
    }
    if (op == "first" || op == "second") {
      const Cat& p = cat(of);
      if (p.factors.size() != 2) throw Refusal(of + " was not made as a product");
      const Category &A = cat(p.factors[0]).C, &B = cat(p.factors[1]).C;
      functors::Functor F{name, {}, {}};
      for (Index o = 0; o < p.C.objects.size(); o++) F.objects.push_back(op == "first" ? o / static_cast<Index>(B.objects.size()) : o % static_cast<Index>(B.objects.size()));
      for (Index f = 0; f < p.C.size(); f++) F.arrows.push_back(op == "first" ? f / static_cast<Index>(B.size()) : f % static_cast<Index>(B.size()));
      const std::string target = p.factors[op == "first" ? 0 : 1];
      return keep(name, F, of, target, functors::verify(p.C, op == "first" ? A : B, F));
    }
    const Cat& e = cat(of);  // projection
    if (!e.projection) throw Refusal(of + " has no functor to the category it was made from (a slice, a comma category, elements, algebras and a skeleton have)");
    return keep(name, e.projection->first, of, e.projection->second, functors::verify(e.C, cat(e.projection->second).C, e.projection->first));
  }

  Value transformation(const ParseNode& n) {
    const auto names = n.all("name");
    const std::string name = name_of(*names.at(0)), from = name_of(*names.at(1)), to = name_of(*names.at(2));
    const Fun &F = fun(from), &G = fun(to);
    if (F.source != G.source || F.target != G.target) throw Refusal(from + " and " + to + " are not functors between the same two categories");
    const Cat &c = cat(F.source), &d = cat(F.target);
    functors::Transformation t{name, std::vector<Index>(c.C.objects.size(), none)};
    for (const ParseNode* a : n.child("ablock")->all("assign")) t.components[object_of(c.C, name_of(*a->child("name")))] = arrow_of(d, *a->child("expr"));
    for (Index a = 0; a < c.C.objects.size(); a++)
      if (t.components[a] == none) throw Refusal("the component at " + c.C.objects[a] + " is not given");
    const Verdict v = functors::natural(c.C, d.C, F.F, G.F, t);
    Value view = Value::map();
    view.set("type", "transformation").set("source", view_of(c)).set("target", view_of(d))
        .set("from", Value::map().set("name", from).set("objects", Value::of(F.F.objects)).set("arrows", Value::of(F.F.arrows)))
        .set("to", Value::map().set("name", to).set("objects", Value::of(G.F.objects)).set("arrows", Value::of(G.F.arrows))).set("components", Value::of(t.components));
    if (v.holds()) forget(name), nats_[name] = {t, from, to};
    return outcome("transformation", name, v, std::move(view));
  }

  // ---- set-valued functors ------------------------------------------------------------------------------------------------------

  Value keep(const std::string& name, sets::Copresheaf X, const std::string& on, Verdict v) {
    X.name = name;
    if (v.claim.find("Kan extension") == std::string::npos) v.claim = name + " is a functor " + on + " → FinSet";
    Set x{std::move(X), on};
    Value view = view_of(x);
    if (v.holds()) forget(name), sets_[name] = std::move(x);
    return outcome("sets", name, v, std::move(view));
  }

  Value sets_of(const ParseNode& n) {
    const auto names = n.all("name");
    const std::string name = name_of(*names.at(0));
    if (const ParseNode* block = n.child("sblock")) {
      const std::string on = name_of(*names.at(1));
      const Cat& c = cat(on);
      const Category& C = c.C;
      sets::Copresheaf X{name, std::vector<std::vector<std::string>>(C.objects.size()), std::vector<sets::Function>(C.size())};
      std::vector<char> known(C.size(), 0);
      for (const ParseNode* item : block->all("sitem")) {
        const ParseNode& it = item->children.at(0);
        if (it.name != "carrier") continue;
        const auto all = it.all("name");
        auto& here = X.elements[object_of(C, name_of(*all.at(0)))];
        for (std::size_t k = 1; k < all.size(); k++) here.push_back(name_of(*all[k]));
      }
      auto element = [&](Index a, const std::string& w) {
        for (Index k = 0; k < X.elements[a].size(); k++)
          if (X.elements[a][k] == w) return k;
        throw Refusal(w + " is no element of " + name + "(" + C.objects[a] + ")");
      };
      for (Index a = 0; a < C.objects.size(); a++) X.action[C.identity[a]] = finite::detail::iota(X.size(a)), known[C.identity[a]] = 1;
      for (const ParseNode* item : block->all("sitem")) {
        const ParseNode& it = item->children.at(0);
        if (it.name != "action") continue;
        const std::string arrow = name_of(*it.child("name"));
        const Index f = arrow_named(c, arrow);
        if (f == none) throw Refusal(on + " has no arrow named " + arrow);
        sets::Function act(X.size(C.dom(f)), none);
        for (const ParseNode* p : it.all("pair")) {
          const auto ends = p->all("name");
          act[element(C.dom(f), name_of(*ends.at(0)))] = element(C.cod(f), name_of(*ends.at(1)));
        }
        for (Index k = 0; k < act.size(); k++)
          if (act[k] == none) throw Refusal(arrow + " is not said where to send " + X.elements[C.dom(f)][k]);
        X.action[f] = act, known[f] = 1;
      }
      // What is given fixes every composite: carry it through, and stop where two ways disagree.
      const std::string claim = name + " is a functor " + on + " → FinSet";
      for (bool changed = true; changed;) {
        changed = false;
        for (Index g = 0; g < C.size(); g++)
          for (Index f = 0; f < C.size(); f++) {
            if (!known[g] || !known[f] || C.cod(f) != C.dom(g)) continue;
            const Index h = C.compose(g, f);
            sets::Function act;
            for (Index x : X.action[f]) act.push_back(X.action[g][x]);
            if (!known[h]) {
              X.action[h] = act, known[h] = 1, changed = true;
            } else if (X.action[h] != act) {
              return outcome("sets", name, Verdict::no(claim, "it does not keep the composite " + C.arrows[g].name + " ∘ " + C.arrows[f].name + " = " + C.arrows[h].name + ": the two ways act differently").with("at", C.arrows[g].name + ", " + C.arrows[f].name));
            }
          }
      }
      std::string missing;
      for (Index g : finite::generators(C))
        if (!known[g]) missing += (missing.empty() ? "" : ", ") + C.arrows[g].name;
      for (Index f = 0; f < C.size() && missing.empty(); f++)
        if (!known[f]) missing = C.arrows[f].name;
      if (!missing.empty()) throw Refusal("the action of " + missing + " is not given, and does not follow from what is");
      return keep(name, X, on, sets::verify(C, X));
    }
    const ParseNode& x = n.child("sexpr")->children.at(0);
    if (x.name == "somega") {
      const std::string on = name_of(*x.child("name"));
      const auto K = sets::classifier(cat(on).C);
      Verdict v = sets::verify(cat(on).C, K.omega);
      return keep(name, K.omega, on, v);
    }
    const std::string op = x.child("sop")->text;
    const auto two = x.all("name");
    const std::string a = name_of(*two.at(0)), b = name_of(*two.at(1));
    if (op == "hom") return keep(name, sets::representable(cat(a).C, object_of(cat(a).C, b)), a, sets::verify(cat(a).C, sets::representable(cat(a).C, object_of(cat(a).C, b))));
    if (op == "constant") return keep(name, sets::constant(cat(a).C, std::strtoull(b.c_str(), nullptr, 10)), a, sets::verify(cat(a).C, sets::constant(cat(a).C, std::strtoull(b.c_str(), nullptr, 10))));
    const Set& X = set(a);
    const Fun& K = fun(b);
    if (op == "pullback") {
      if (X.on != K.target) throw Refusal(a + " is on " + X.on + ", and " + b + " ends in " + K.target);
      const auto Y = sets::pullback(K.F, X.X);
      return keep(name, Y, K.source, sets::verify(cat(K.source).C, Y));
    }
    if (X.on != K.source) throw Refusal(a + " is on " + X.on + ", and " + b + " begins in " + K.source);
    const Category &C = cat(K.source).C, &D = cat(K.target).C;
    const sets::Kan kan = op == "lan" ? sets::left_kan(C, D, K.F, X.X) : sets::right_kan(C, D, K.F, X.X);
    Verdict v = sets::verify(D, kan.extension);
    if (v.holds()) {  // universal against every representable and the constant 2
      std::size_t against = 0;
      for (Index d = 0; d <= D.objects.size() && v.holds(); d++) {
        const sets::Copresheaf Y = d < D.objects.size() ? sets::representable(D, d) : sets::constant(D, 2);
        const Verdict u = op == "lan" ? sets::left_kan_universal(C, D, K.F, X.X, kan, Y) : sets::right_kan_universal(C, D, K.F, X.X, kan, Y);
        if (!u.holds()) v = u;
        against++;
      }
      if (v.holds())
        v = Verdict::yes(name + " is the " + (op == "lan" ? "left" : "right") + " Kan extension of " + a + " along " + b,
                         "computed pointwise, it is a functor, and it is universal against each of " + std::to_string(against) + " functors tried (the representables and the constant 2)", v.examined);
    }
    return keep(name, kan.extension, K.target, v);
  }

  // ---- theories, models, diagrams -----------------------------------------------------------------------------------------------

  Value theory_view(const monoidal::Theory& T) const {
    const monoidal::Signature& S = T.signature;
    Value v = Value::map(), gens = Value::list(), laws = Value::list();
    for (auto& g : S.generators) gens.push(Value::map().set("name", g.name).set("in", monoidal::words(S, g.inputs)).set("out", monoidal::words(S, g.outputs)).set("diagram", view_of(S, monoidal::gen(S.generator(g.name)))));
    for (auto& law : T.laws) {
      Value l = strings(S, law.left, &law.right);
      laws.push(l.set("name", law.name));
    }
    return v.set("type", "theory").set("name", S.name).set("types", Value::of(S.types)).set("generators", std::move(gens)).set("laws", std::move(laws));
  }

  Value theory(const ParseNode& n) {
    const std::string name = name_of(*n.child("name"));
    monoidal::Theory T;
    T.signature.name = name;
    monoidal::Signature& S = T.signature;
    const auto items = n.child("tblock")->all("titem");
    for (const ParseNode* item : items) {
      const ParseNode& it = item->children.at(0);
      if (it.name == "types")
        for (const ParseNode* t : it.all("name")) S.types.push_back(name_of(*t));
    }
    for (const ParseNode* item : items) {
      const ParseNode& it = item->children.at(0);
      if (it.name != "box") continue;
      const auto sides = it.all("wires");
      auto wires = [&](const ParseNode& w) {
        std::vector<Index> out;
        for (const ParseNode* t : w.all("name")) {
          if (name_of(*t) == "I") continue;
          if (S.type(name_of(*t)) == none) throw Refusal(name + " has no type named " + name_of(*t));
          out.push_back(S.type(name_of(*t)));
        }
        return out;
      };
      for (const ParseNode* g : it.child("names")->all("name")) {
        if (S.generator(name_of(*g)) != none || S.type(name_of(*g)) != none) throw Refusal(name_of(*g) + " is declared twice");
        S.generators.push_back({name_of(*g), wires(*sides.at(0)), wires(*sides.at(1))});
      }
    }
    forget(name), theories_[name] = T;  // the laws are read against the signature
    std::size_t unnamed = 0;
    try {
      for (const ParseNode* item : items) {
        const ParseNode& it = item->children.at(0);
        if (it.name != "law") continue;
        const auto sides = it.all("expr");
        const ParseNode* label = it.child("name");
        T.laws.push_back({label ? name_of(*label) : "law " + std::to_string(++unnamed), term_of(name, *sides.at(0)), term_of(name, *sides.at(1))});
      }
    } catch (...) {
      theories_.erase(name);
      throw;
    }
    const Verdict v = monoidal::well_formed(T);
    if (v.holds()) theories_[name] = T;
    else theories_.erase(name);
    Value o = outcome("theory", name, v);
    if (v.holds()) o.set("view", theory_view(T));
    return o;
  }

  Value laws_view(const monoidal::Theory& T, const monoidal::Model& M) const {
    Value laws = Value::list();
    const auto verdicts = monoidal::laws_in(T, M);
    for (std::size_t k = 0; k < T.laws.size(); k++) {
      Value l = strings(T.signature, T.laws[k].left, &T.laws[k].right);
      laws.push(verdict_into(l.set("name", T.laws[k].name), verdicts[k]));
    }
    return Value::map().set("type", "laws").set("name", M.name).set("theory", T.signature.name).set("laws", std::move(laws));
  }

  Value model(const ParseNode& n) {
    const auto names = n.all("name");
    const std::string name = name_of(*names.at(0)), theory = name_of(*names.at(1));
    const monoidal::Theory& T = named(theories_, theory, "theory");
    const monoidal::Signature& S = T.signature;
    monoidal::Model M;
    M.name = name;
    const ParseNode& world = *n.child("world");
    const std::string kind = world.child("wkind")->text;
    M.kronecker = kind != "sums";
    M.semiring = kind == "relations" ? monoidal::Semiring::boolean : monoidal::Semiring::integer;
    if (const ParseNode* ring = world.child("ring")) {
      if (ring->text == "boolean") M.semiring = monoidal::Semiring::boolean;
      else M.semiring = monoidal::Semiring::modular, M.modulus = std::strtoll(ring->child("number")->text.c_str(), nullptr, 10);
    }
    M.dimension.assign(S.types.size(), 0), M.generators.assign(S.generators.size(), {});
    std::vector<char> typed(S.types.size(), 0), given(S.generators.size(), 0);
    const auto items = n.child("mblock")->all("mitem");
    for (const ParseNode* item : items) {  // the dimensions first
      const std::string w = name_of(*item->child("name"));
      if (S.type(w) == none) continue;
      const ParseNode* values = item->child("values");
      if (!values || values->all("integer").size() != 1) throw Refusal("the type " + w + " is given a dimension, one number");
      M.dimension[S.type(w)] = std::strtoull(values->text.c_str(), nullptr, 10), typed[S.type(w)] = 1;
    }
    for (Index t = 0; t < S.types.size(); t++)
      if (!typed[t]) throw Refusal("the type " + S.types[t] + " is given no dimension");
    for (const ParseNode* item : items) {
      const std::string w = name_of(*item->child("name"));
      if (S.type(w) != none) continue;
      const Index g = S.generator(w);
      if (g == none) throw Refusal(theory + " has no type or generator named " + w);
      const std::size_t rows = M.dimension_of(S.generators[g].outputs), cols = M.dimension_of(S.generators[g].inputs);
      std::vector<std::vector<long long>> lines;
      if (const ParseNode* values = item->child("values")) {
        lines.emplace_back();
        for (const ParseNode* i : values->all("integer")) lines.back().push_back(std::strtoll(i->text.c_str(), nullptr, 10));
      } else {
        for (const ParseNode* row : item->child("matrix")->all("row")) {
          lines.emplace_back();
          for (const ParseNode* i : row->all("integer")) lines.back().push_back(std::strtoll(i->text.c_str(), nullptr, 10));
        }
      }
      if (kind == "sets" && item->child("values")) {  // a function, by the value at each input in order
        if (lines[0].size() != cols) throw Refusal(w + " is a function on " + std::to_string(cols) + " inputs, and " + std::to_string(lines[0].size()) + " values are given");
        std::vector<Index> f;
        for (long long y : lines[0]) {
          if (y < 0 || static_cast<std::size_t>(y) >= rows) throw Refusal(w + " takes the value " + std::to_string(y) + ", outside its " + std::to_string(rows) + " outputs");
          f.push_back(static_cast<Index>(y));
        }
        M.generators[g] = monoidal::function(f, rows);
      } else {
        monoidal::Matrix A{lines.size(), lines.empty() ? 0 : lines[0].size(), {}};
        for (auto& line : lines) {
          if (line.size() != A.cols) throw Refusal("the rows of " + w + " are not of one length");
          A.v.insert(A.v.end(), line.begin(), line.end());
        }
        if (lines.empty()) A.rows = rows, A.cols = cols, A.v.assign(rows * cols, 0);  // [] where a side has dimension 0
        M.generators[g] = std::move(A);
      }
      given[g] = 1;
    }
    for (Index g = 0; g < S.generators.size(); g++)
      if (!given[g]) throw Refusal("the generator " + S.generators[g].name + " is given no value");
    const Verdict v = monoidal::satisfies(T, M);
    Value view = monoidal::well_formed(S, M).holds() ? laws_view(T, M) : Value();
    if (monoidal::well_formed(S, M).holds()) forget(name), models_[name] = {M, theory};
    return outcome("model", name, v, std::move(view));
  }

  Value diagram(const ParseNode& n) {
    const auto names = n.all("name");
    const std::string name = name_of(*names.at(0)), theory = name_of(*names.at(1));
    const monoidal::Term t = term_of(theory, *n.child("expr"));
    const monoidal::Signature& S = named(theories_, theory, "theory").signature;
    const monoidal::Typed typed = monoidal::type(S, t);
    Verdict v = typed.verdict;
    if (v.holds()) {
      v.reason = monoidal::words(S, typed.in) + " → " + monoidal::words(S, typed.out);
      forget(name), diagrams_[name] = {t, theory};
    }
    return outcome("diagram", name, v, strings(S, t));
  }

  // ---- claims -------------------------------------------------------------------------------------------------------------------

  Value derivation_view(const presentations::Presentation& P, const presentations::Path& from, const presentations::Derivation& d) const {
    Value steps = Value::list();
    const auto paths = presentations::trace(P, from, d);
    for (std::size_t k = 0; k < paths.size(); k++) {
      Value edges = Value::list();
      for (Index g : paths[k].edges) edges.push(P.quiver.edges[g].name);
      Value s = Value::map();
      s.set("edges", std::move(edges)).set("at_object", P.quiver.objects[paths[k].source]).set("words", presentations::words(P.quiver, paths[k]));
      if (k < d.size()) {
        const auto& eq = P.equations[d[k].equation];
        s.set("at", d[k].at).set("span", (d[k].forward ? eq.left : eq.right).edges.size()).set("forward", d[k].forward).set("equation", d[k].equation)
            .set("by", presentations::words(P.quiver, eq.left) + " = " + presentations::words(P.quiver, eq.right));
      }
      steps.push(std::move(s));
    }
    return Value::map().set("type", "derivation").set("name", P.name).set("steps", std::move(steps));
  }

  Value check(const ParseNode& n) {
    if (n.name == "cequal") {
      const auto sides = n.all("expr");
      const std::string in = name_of(*n.child("name"));
      if (theories_.count(in)) {
        const monoidal::Signature& S = theories_.at(in).signature;
        const monoidal::Term l = term_of(in, *sides.at(0)), r = term_of(in, *sides.at(1));
        return outcome("check", in, monoidal::same(S, l, r), strings(S, l, &r));
      }
      if (models_.count(in)) {
        const Mod& m = models_.at(in);
        const monoidal::Signature& S = theories_.at(m.theory).signature;
        const monoidal::Term l = term_of(m.theory, *sides.at(0)), r = term_of(m.theory, *sides.at(1));
        return outcome("check", in, monoidal::holds_in(S, m.M, l, r), strings(S, l, &r));
      }
      const Cat& c = named(cats_, in, "category, theory or model");
      if (c.P) {
        const presentations::Path l = path_of(*c.P, *sides.at(0)), r = path_of(*c.P, *sides.at(1));
        const presentations::Proof proof = presentations::prove(*c.P, c.K, l, r);
        return outcome("check", in, proof.verdict, proof.verdict.holds() ? derivation_view(*c.P, l, proof.derivation) : Value());
      }
      const Index l = arrow_of(c, *sides.at(0)), r = arrow_of(c, *sides.at(1));
      const std::string claim = c.C.arrows[l].name + " = " + c.C.arrows[r].name + " in " + in;
      if (c.C.dom(l) != c.C.dom(r) || c.C.cod(l) != c.C.cod(r)) return outcome("check", in, Verdict::no(claim, "the two are not parallel: " + c.C.typed(l) + " and " + c.C.typed(r)));
      return outcome("check", in, l == r ? Verdict::yes(claim, "both sides are the arrow " + c.C.arrows[l].name + ", by the table of composition", 1)
                                        : Verdict::no(claim, "the sides are different arrows", 1).with("left", c.C.arrows[l].name).with("right", c.C.arrows[r].name));
    }
    if (n.name == "cadjoint") {
      const auto two = n.all("name");
      const std::string left = name_of(*two.at(0)), right = name_of(*two.at(1));
      const Fun &L = fun(left), &R = fun(right);
      if (L.source != R.target || L.target != R.source) throw Refusal(left + " runs " + L.source + " → " + L.target + " and " + right + " runs " + R.source + " → " + R.target + ": they are not opposite ways between two categories");
      const Category &C = cat(L.source).C, &D = cat(L.target).C;
      functors::Adjunction A{L.F, R.F, {}, {}};
      const auto units = functors::all_transformations(C, C, functors::identity(C), functors::compose(R.F, L.F));
      const auto counits = functors::all_transformations(D, D, functors::compose(L.F, R.F), functors::identity(D));
      for (auto& eta : units)
        for (auto& eps : counits) {
          A.unit = eta, A.unit.name = "η", A.counit = eps, A.counit.name = "ε";
          const Verdict v = functors::verify_adjunction(C, D, A);
          if (v.holds()) return outcome("check", left, v, adjunction_view(L.source, L.target, A));
        }
      return outcome("check", left, Verdict::no(left + " ⊣ " + right, "none of the " + std::to_string(units.size()) + " natural transformations 1 ⇒ " + right + " ∘ " + left + " with any of the " + std::to_string(counits.size()) + " natural transformations " +
                                                                           left + " ∘ " + right + " ⇒ 1 satisfies the triangle identities", units.size() * counits.size()));
    }
    if (n.name == "crel") {
      const auto two = n.all("name");
      const std::string a = name_of(*two.at(0)), b = name_of(*two.at(1));
      const bool iso = n.child("rel")->text == "isomorphic";
      if (cats_.count(a)) {
        if (!iso) return outcome("check", a, functors::equivalent(cat(a).C, cat(b).C));
        const auto found = functors::isomorphism(cat(a).C, cat(b).C);
        if (!found) return outcome("check", a, Verdict::no(a + " ≅ " + b, "no functor between them is a bijection on arrows: every one that could be was tried"));
        std::string pairs;
        for (Index o = 0; o < cat(a).C.objects.size(); o++) pairs += (o ? ", " : "") + cat(a).C.objects[o] + " ↦ " + cat(b).C.objects[found->objects[o]];
        Fun f{*found, a, b};
        f.F.name = "an isomorphism";
        return outcome("check", a, Verdict::yes(a + " ≅ " + b, "a functor that is a bijection on objects and on arrows was found", cat(a).C.size()).with("witness", pairs), view_of(f));
      }
      if (funs_.count(a)) {
        const Fun &F = fun(a), &G = fun(b);
        if (F.source != G.source || F.target != G.target) throw Refusal(a + " and " + b + " are not functors between the same two categories");
        const auto found = functors::natural_isomorphism(cat(F.source).C, cat(F.target).C, F.F, G.F);
        if (!found) return outcome("check", a, Verdict::no(a + " ≅ " + b, "no natural transformation between them has every component invertible"));
        std::string parts;
        for (Index o = 0; o < found->components.size(); o++) parts += (o ? ", " : "") + cat(F.target).C.arrows[found->components[o]].name;
        return outcome("check", a, Verdict::yes(a + " ≅ " + b, "a natural isomorphism was found").with("witness", parts));
      }
      const Set &X = set(a), &Y = set(b);
      if (X.on != Y.on) throw Refusal(a + " and " + b + " are not on one category");
      const auto found = sets::isomorphism(cat(X.on).C, X.X, Y.X);
      return outcome("check", a, found ? Verdict::yes(a + " ≅ " + b, "a natural bijection was found") : Verdict::no(a + " ≅ " + b, "no natural transformation between them is a bijection at every object"));
    }
    if (n.name == "cyoneda") {
      const auto two = n.all("name");
      const Set& X = set(name_of(*two.at(0)));
      return outcome("check", name_of(*two.at(0)), sets::yoneda(cat(X.on).C, X.X, object_of(cat(X.on).C, name_of(*two.at(1)))));
    }
    if (n.name == "cclass") {
      const Set& X = set(name_of(*n.child("name")));
      return outcome("check", name_of(*n.child("name")), sets::classifies(cat(X.on).C, X.X, sets::classifier(cat(X.on).C)));
    }
    if (n.name == "cprop") {
      const auto words = n.all("name");
      const std::string subject = name_of(*words.at(0));
      std::string property, in;
      for (std::size_t k = 1; k < words.size(); k++) {
        const std::string w = name_of(*words[k]);
        if (w == "in" && k + 1 < words.size()) {
          in = name_of(*words[k + 1]);
          break;
        }
        if (w == "a" || w == "an") continue;
        property += (property.empty() ? "" : " ") + w;
      }
      if (!in.empty()) {
        const Cat& c = cat(in);
        const Index f = arrow_named(c, subject);
        if (f == none) throw Refusal(in + " has no arrow named " + subject);
        if (property == "mono" || property == "monic") return outcome("check", subject, finite::monic(c.C, f));
        if (property == "epi" || property == "epic") return outcome("check", subject, finite::epic(c.C, f));
        if (property == "iso" || property == "invertible" || property == "isomorphism") {
          const Index g = finite::inverse(c.C, f);
          return outcome("check", subject, g == none ? Verdict::no(subject + " is invertible in " + in, "no arrow " + c.C.objects[c.C.cod(f)] + " → " + c.C.objects[c.C.dom(f)] + " composes with it to both identities")
                                                     : Verdict::yes(subject + " is invertible in " + in, "its inverse is " + c.C.arrows[g].name).with("witness", c.C.arrows[g].name));
        }
        throw Refusal("of an arrow one may ask: mono, epi, iso");
      }
      if (cats_.count(subject)) {
        const Category& C = cat(subject).C;
        auto plain = [&](bool is, const std::string& what, const std::string& yes, const std::string& no) { return outcome("check", subject, is ? Verdict::yes(subject + " is " + what, yes, C.size()) : Verdict::no(subject + " is " + what, no, C.size())); };
        if (property == "complete") return outcome("check", subject, limits::finitely_complete(C));
        if (property == "cocomplete") return outcome("check", subject, limits::finitely_cocomplete(C));
        if (property == "cartesian closed") return outcome("check", subject, limits::cartesian_closed(C));
        if (property == "thin" || property == "preorder") return plain(finite::is_thin(C), "thin", "no two arrows are parallel", "two arrows are parallel");
        if (property == "groupoid") return plain(finite::is_groupoid(C), "a groupoid", "every arrow has an inverse", "some arrow has no inverse");
        if (property == "discrete") return plain(finite::is_discrete(C), "discrete", "it has identities only", "it has an arrow that is no identity");
        if (property == "connected") return plain(finite::components(C).empty() || *std::max_element(finite::components(C).begin(), finite::components(C).end()) == 0, "connected", "every two objects are joined by a zigzag of arrows", "some two objects are joined by no zigzag of arrows");
        if (property == "skeletal") {
          const auto cls = finite::isomorphism_classes(C);
          return plain(cls.empty() || *std::max_element(cls.begin(), cls.end()) + 1 == C.objects.size(), "skeletal", "no two objects are isomorphic", "two objects are isomorphic");
        }
        throw Refusal("of a category one may ask: complete, cocomplete, cartesian closed, thin, groupoid, discrete, connected, skeletal");
      }
      if (funs_.count(subject)) {
        const Fun& F = fun(subject);
        const Category &C = cat(F.source).C, &D = cat(F.target).C;
        if (property == "faithful") return outcome("check", subject, functors::faithful(C, D, F.F));
        if (property == "full") return outcome("check", subject, functors::full(C, D, F.F));
        if (property == "essentially surjective") return outcome("check", subject, functors::essentially_surjective(C, D, F.F));
        if (property == "equivalence") return outcome("check", subject, functors::equivalence(C, D, F.F).verdict);
        throw Refusal("of a functor one may ask: faithful, full, essentially surjective, equivalence");
      }
      throw Refusal(subject + " names no category or functor; of an arrow, say in which category: " + subject + " is mono in C");
    }
    // A bare name: whatever it names is asked to be what it was declared as.
    const std::string name = name_of(*n.child("name"));
    if (cats_.count(name)) {
      const Cat& c = named(cats_, name, "category");
      if (!c.finite) return outcome("check", name, presentations::certify(*c.P, c.K), view_of(c));
      Verdict v = finite::validate(c.C);
      if (c.P && v.holds()) {
        const Verdict rules = presentations::certify(*c.P, c.K);
        if (!rules.holds()) v = rules;
        else v.reason += "; its " + std::to_string(c.K.rules.size()) + " rules decrease, follow from the equations and are confluent", v.examined += rules.examined;
      }
      return outcome("check", name, v, view_of(c));
    }
    if (funs_.count(name)) return outcome("check", name, functors::verify(cat(fun(name).source).C, cat(fun(name).target).C, fun(name).F), view_of(fun(name)));
    if (nats_.count(name)) {
      const Nat& t = nats_.at(name);
      const Fun &F = fun(t.from), &G = fun(t.to);
      return outcome("check", name, functors::natural(cat(F.source).C, cat(F.target).C, F.F, G.F, t.t));
    }
    if (sets_.count(name)) return outcome("check", name, sets::verify(cat(set(name).on).C, set(name).X), view_of(set(name)));
    if (theories_.count(name)) return outcome("check", name, monoidal::well_formed(theories_.at(name)), theory_view(theories_.at(name)));
    if (models_.count(name)) {
      const Mod& m = models_.at(name);
      return outcome("check", name, monoidal::satisfies(theories_.at(m.theory), m.M), laws_view(theories_.at(m.theory), m.M));
    }
    if (diagrams_.count(name)) {
      const Dia& d = diagrams_.at(name);
      return outcome("check", name, monoidal::type(theories_.at(d.theory).signature, d.term).verdict, strings(theories_.at(d.theory).signature, d.term));
    }
    throw Refusal("nothing is named " + name);
  }

  // ---- questions ----------------------------------------------------------------------------------------------------------------

  Value find(const ParseNode& n) {
    if (n.name == "qlimit") {
      const bool co = n.child("qkind")->text == "colimit";
      const std::string name = name_of(*n.child("name"));
      const Fun& D = fun(name);
      const Cat& c = cat(D.target);
      const limits::Limit L = co ? limits::colimit(c.C, cat(D.source).C, D.F) : limits::limit(c.C, cat(D.source).C, D.F);
      return outcome("find", name, L.verdict, L.cone ? cone_view(c, D.F, *L.cone, co) : view_of(c));
    }
    if (n.name == "qshape") {
      const std::string shape = n.child("shape")->text;
      auto names = n.all("name");
      const std::string in = name_of(*names.back());
      names.pop_back();
      const Cat& c = cat(in);
      const Category& C = c.C;
      auto need = [&](std::size_t k) {
        if (names.size() != k) throw Refusal(shape + " takes " + std::to_string(k) + (k == 1 ? " name" : " names") + " before \"in\"");
      };
      const bool co = shape == "coproduct" || shape == "coequalizer" || shape == "pushout" || shape == "initial";
      limits::Diagram G;
      if (shape == "terminal" || shape == "initial") {
        need(0), G = limits::empty_diagram();
      } else if (shape == "exponential") {
        need(2);
        const Index a = object_of(C, name_of(*names[0])), b = object_of(C, name_of(*names[1]));
        const limits::Exponential E = limits::exponential(C, a, b);
        Value view = view_of(c);
        if (E.verdict.holds()) view.set("marks", Value::map().set("objects", Value::list().push(E.object)).set("arrows", Value::list().push(E.evaluation)));
        return outcome("find", in, E.verdict, std::move(view));
      } else if (shape == "product" || shape == "coproduct") {
        if (names.size() < 2) throw Refusal(shape + " takes two or more objects before \"in\"");
        std::vector<Index> objects;
        for (const ParseNode* o : names) objects.push_back(object_of(C, name_of(*o)));
        G = limits::discrete_diagram(C, objects);
      } else {
        need(2);
        const Index f = arrow_named(c, name_of(*names[0])), g = arrow_named(c, name_of(*names[1]));
        if (f == none || g == none) throw Refusal(in + " has no arrow named " + name_of(*names[f == none ? 0 : 1]));
        try {
          G = shape == "equalizer" || shape == "coequalizer" ? limits::parallel_diagram(C, f, g) : shape == "pullback" ? limits::cospan_diagram(C, f, g) : limits::span_diagram(C, f, g);
        } catch (const std::invalid_argument& e) {
          const std::string what = e.what();
          throw Refusal(what.substr(what.find(": ") == std::string::npos ? 0 : what.find(": ") + 2));
        }
      }
      limits::Limit L = co ? limits::colimit(C, G.shape, G.functor) : limits::limit(C, G.shape, G.functor);
      if (shape == "terminal" || shape == "initial") {
        L.verdict.claim = L.cone ? C.objects[L.cone->apex] + " is " + (co ? "an initial" : "a terminal") + " object of " + in : in + " has " + (co ? "an initial" : "a terminal") + " object";
        L.verdict.reason = L.cone ? std::string("it has exactly one arrow ") + (co ? "to" : "from") + " every object" : std::string("no object has exactly one arrow ") + (co ? "to" : "from") + " every object";
      }
      return outcome("find", in, L.verdict, L.cone ? cone_view(c, G.functor, *L.cone, co) : view_of(c));
    }
    if (n.name == "qfun") {
      const auto two = n.all("name");
      const std::string a = name_of(*two.at(0)), b = name_of(*two.at(1));
      const Category &C = cat(a).C, &D = cat(b).C;
      functors::Options o;
      o.limit = 100000;
      Value rows = Value::list();
      const auto gens = finite::generators(C);
      const std::uint64_t count = functors::for_each_functor(C, D, [&](const functors::Functor& F) {
        if (rows.size() < 60) {
          Value row = Value::list();
          for (Index x : F.objects) row.push(D.objects[x]);
          for (Index g : gens) row.push(D.arrows[F.arrows[g]].name);
          rows.push(std::move(row));
        }
        return true;
      }, o);
      std::vector<std::string> columns = C.objects;
      for (Index g : gens) columns.push_back(C.arrows[g].name);
      return outcome("find", a, Verdict::yes("the functors " + a + " → " + b, (count >= o.limit ? "at least " : "") + std::to_string(count) + (count == 1 ? " functor" : " functors") + (count > 60 ? "; the first 60 are listed" : ""), count), table(columns, std::move(rows)));
    }
    if (n.name == "qnat") {
      const auto two = n.all("name");
      const std::string a = name_of(*two.at(0)), b = name_of(*two.at(1));
      const Fun &F = fun(a), &G = fun(b);
      if (F.source != G.source || F.target != G.target) throw Refusal(a + " and " + b + " are not functors between the same two categories");
      const Category &C = cat(F.source).C, &D = cat(F.target).C;
      const auto all = functors::all_transformations(C, D, F.F, G.F);
      Value rows = Value::list();
      for (std::size_t k = 0; k < all.size() && k < 60; k++) {
        Value row = Value::list();
        for (Index x : all[k].components) row.push(D.arrows[x].name);
        rows.push(std::move(row));
      }
      return outcome("find", a, Verdict::yes("the natural transformations " + a + " ⇒ " + b, std::to_string(all.size()) + (all.size() == 1 ? " natural transformation" : " natural transformations") + (all.size() > 60 ? "; the first 60 are listed" : ""), all.size()), table(C.objects, std::move(rows)));
    }
    const std::string what = n.child("qwhat")->text, name = name_of(*n.child("name"));
    if (what == "generators" || what == "table") {
      const Cat& c = cat(name);
      Value rows = Value::list();
      for (Index g : finite::generators(c.C)) rows.push(Value::list().push(c.C.arrows[g].name).push(c.C.objects[c.C.dom(g)]).push(c.C.objects[c.C.cod(g)]));
      if (what == "generators") return outcome("find", name, Verdict::yes("arrows that generate " + name, std::to_string(rows.size()) + " arrows, of which every arrow is a composite" + (c.C.basis.empty() ? "; the choice is one that generates, not the only one" : ""), c.C.size()), table({"arrow", "from", "to"}, std::move(rows)));
      if (c.C.size() > 48) throw Refusal(name + " has " + std::to_string(c.C.size()) + " arrows; its table is shown up to 48");
      Value view = view_of(c);
      return outcome("find", name, Verdict::yes("the table of composition of " + name, "row g, column f: g ∘ f", c.C.size() * c.C.size()), view.set("type", "composition"));
    }
    if (what == "rules") {
      const Cat& c = named(cats_, name, "category");
      if (!c.P) throw Refusal(name + " was not given by generators and equations");
      Value rows = Value::list();
      for (auto& r : c.K.rules) rows.push(Value::list().push(presentations::words(c.P->quiver, r.left)).push(presentations::words(c.P->quiver, r.right)).push(r.why.size()));
      return outcome("find", name, presentations::certify(*c.P, c.K), table({"a path", "is rewritten to", "steps of its derivation"}, std::move(rows)));
    }
    const Set& X = set(name);
    const Category& C = cat(X.on).C;
    if (what == "sections") {
      const auto all = sets::sections(C, X.X);
      Value rows = Value::list();
      for (std::size_t k = 0; k < all.size() && k < 60; k++) {
        Value row = Value::list();
        for (Index a = 0; a < C.objects.size(); a++) row.push(X.X.elements[a][all[k][a]]);
        rows.push(std::move(row));
      }
      return outcome("find", name, Verdict::yes("the limit of " + name, std::to_string(all.size()) + (all.size() == 1 ? " section" : " sections") + ": choices of an element at each object that every arrow carries to one another", all.size()), table(C.objects, std::move(rows)));
    }
    if (what == "classes") {
      const auto K = sets::classes(C, X.X);
      std::vector<std::string> members(K.count);
      for (Index a = 0; a < C.objects.size(); a++)
        for (Index x = 0; x < X.X.size(a); x++) members[K.of[a][x]] += (members[K.of[a][x]].empty() ? "" : ", ") + X.X.elements[a][x];
      Value rows = Value::list();
      for (auto& m : members) rows.push(Value::list().push(m));
      return outcome("find", name, Verdict::yes("the colimit of " + name, std::to_string(K.count) + (K.count == 1 ? " class" : " classes") + " of elements joined by the arrows", X.X.total()), table({"a class"}, std::move(rows)));
    }
    const auto subs = sets::subfunctors(C, X.X);
    Value rows = Value::list();
    for (std::size_t k = 0; k < subs.size() && k < 80; k++) {
      Value row = Value::list();
      for (Index a = 0; a < C.objects.size(); a++) {
        std::string w;
        for (Index x = 0; x < X.X.size(a); x++)
          if (subs[k][a][x]) w += (w.empty() ? "" : ", ") + X.X.elements[a][x];
        row.push(w.empty() ? "∅" : w);
      }
      rows.push(std::move(row));
    }
    return outcome("find", name, Verdict::yes("the subfunctors of " + name, std::to_string(subs.size()) + " subfunctors" + (subs.size() > 80 ? "; the first 80 are listed" : ""), subs.size()), table(C.objects, std::move(rows)));
  }
};

}  // namespace kategoria::script
