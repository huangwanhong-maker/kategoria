// Checks of kategoria/script: the language, statement by statement, against answers known beforehand.
//
// Each case is a script and the status its statements must be answered with ("holds", "fails", "undecided", or
// "error" for a statement that cannot be carried out), with a word that must stand in the reason where one is known.
// The answers are those of the library's own checks (the commutative square, S₃, Galois connections, the divisors of
// 12, Kan extensions along an inclusion of ordinals, the Boolean monoid), now asked through the language.

#include <kategoria/script/session.hpp>

#include <calx/verification/check.hpp>

#include <string>
#include <vector>

using namespace kategoria::script;

struct Expected {
  std::string status;
  std::string word;  // must stand in the claim, the reason or the evidence; "" for any
};

int main() {
  calx::verification::Suite s;
  auto text_of = [](const Value& o, const char* key) { return o.get(key) ? o.get(key)->text() : std::string(); };
  auto whole = [&](const Value& o) {
    std::string w = text_of(o, "claim") + " | " + text_of(o, "reason");
    if (const Value* evidence = o.get("evidence"))
      for (const Value& e : evidence->items()) w += " | " + e.get("value")->text();
    return w;
  };
  auto run = [&](const std::string& what, const std::string& script, const std::vector<Expected>& expected) {
    Session session;
    const Value out = session.run(script);
    std::string wrong;
    if (out.items().size() != expected.size()) wrong = std::to_string(out.items().size()) + " statements where " + std::to_string(expected.size()) + " were expected";
    for (std::size_t k = 0; k < out.items().size() && k < expected.size() && wrong.empty(); k++) {
      const Value& o = out.items()[k];
      if (text_of(o, "status") != expected[k].status || whole(o).find(expected[k].word) == std::string::npos)
        wrong = "statement " + std::to_string(k + 1) + " (line " + std::to_string(static_cast<int>(o.get("line")->number())) + "): " + text_of(o, "status") + ": " + whole(o);
    }
    s.require(what, wrong.empty(), wrong);
    return out;
  };

  const Value square = run("a commutative square: a category of 9 arrows, and its equation proved in one step",
                           "# a square\n"
                           "category Sq {\n  objects A B C D\n  f : A -> B; g : B -> D\n  h : A -> C\n  k : C -> D\n  g . f = k . h\n}\n"
                           "check g . f = k . h in Sq\ncheck f >> g = h >> k in Sq\ncheck f = h in Sq\ncheck Sq\n",
                           {{"holds", "9 arrows"}, {"holds", "1 step"}, {"holds", ""}, {"fails", "not parallel"}, {"holds", "confluent"}});
  const Value& sq = square.items()[0];
  s.require("its view: 4 objects, 9 arrows of which 4 are generators and 4 identities, a table, its equation, and where it stands",
            sq.get("view")->get("objects")->size() == 4 && sq.get("view")->get("arrows")->size() == 9 && sq.get("view")->get("generators")->size() == 4 && sq.get("view")->get("table")->size() == 9 &&
                sq.get("view")->get("equations")->items()[0].text() == "g ∘ f = k ∘ h" && sq.get("line")->number() == 2 && sq.get("kind")->text() == "category");
  const Value& proof = square.items()[1];
  s.require("a derivation's view: two paths, the first with the place and the equation of its step", proof.get("view")->get("type")->text() == "derivation" && proof.get("view")->get("steps")->size() == 2 &&
                                                                                                    proof.get("view")->get("steps")->items()[0].get("by")->text() == "g ∘ f = k ∘ h");

  run("S₃ by generators and equations: (st)³ = 1 proved, s ≠ t refuted, isomorphic to the symmetric group on 3 points",
      "category G { s, t : o -> o\n s . s = id o; t . t = id o; s . t . s = t . s . t }\n"
      "check s >> t >> s >> t >> s >> t = id o in G\ncheck s = t in G\ncategory S = symmetric 3\ncheck G isomorphic S\ncheck G is groupoid\ncheck \"(0 1)\" is iso in S\nfind rules G\n",
      {{"holds", "6 arrows"}, {"holds", "steps"}, {"fails", "normal forms differ"}, {"holds", "6 arrows"}, {"holds", "bijection"}, {"holds", ""}, {"holds", "inverse"}, {"holds", "critical pair"}});

  run("functors: one that is (faithful, and not full), one that breaks an equation, one that is left open, and a composite",
      "category Sq { f : A -> B; g : B -> D; h : A -> C; k : C -> D; g . f = k . h }\ncategory I = arrow\n"
      "functor F : Sq -> I { A -> 0; B -> 0; C -> 1; D -> 1; g -> \"0≤1\"; h -> \"0≤1\" }\n"
      "category E { x : o -> o; x . x = x }\ncategory Z = cyclic 4\nfunctor W : E -> Z { x -> 1 }\nfunctor V : E -> Z { x -> 0 }\n"
      "functor U : Sq -> Sq { }\nfunctor J = identity I\nfunctor FJ = compose J F\ncheck F is full\ncheck F is faithful\nfind functors I -> Sq\n",
      {{"holds", ""}, {"holds", ""}, {"holds", "keeps"}, {"holds", "2 arrows"}, {"holds", ""}, {"fails", "does not respect the equation x ∘ x = x"}, {"holds", ""}, {"undecided", "leaves it open"}, {"holds", ""}, {"holds", ""},
       {"fails", "image of no arrow"}, {"holds", "tells apart"}, {"holds", "9 functors"}});

  run("adjoints between ordinals: the inclusion of {0, 2} in 4 has a right adjoint and no left one",
      "category C2 = chain 2\ncategory C4 = chain 4\nfunctor i : C2 -> C4 { 0 -> 0; 1 -> 2 }\nfunctor r = right adjoint i\nfunctor l = left adjoint i\ncheck i -| r\ncheck r -| i\n"
      "category T = algebras i\ncheck T isomorphic C2\nfind functors C2 -> C4\n",
      {{"holds", ""}, {"holds", ""}, {"holds", ""}, {"holds", "i ⊣ r"}, {"fails", "3 has no universal arrow"}, {"holds", "triangle"}, {"fails", "triangle"}, {"holds", ""}, {"holds", ""}, {"holds", "10 functors"}});

  run("limits: greatest common divisors and least common multiples; what FinSet up to 2 lacks",
      "category D = divisors 12\nfind product 4 6 in D\nfind coproduct 4 6 in D\nfind terminal in D\nfind exponential 4 6 in D\ncheck D is cartesian closed\ncheck D is complete\n"
      "category F = finset 2\nfind product 2 2 in F\ncheck F is complete\nfind equalizer \"[1→2|0]\" \"[1→2|1]\" in F\nfind pullback \"4≤12\" \"6≤12\" in D\n",
      {{"holds", ""}, {"holds", "2 with"}, {"holds", "12 with"}, {"holds", "12"}, {"holds", "6 with"}, {"holds", ""}, {"holds", ""}, {"holds", "11 arrows"}, {"fails", "universal"}, {"fails", "2 and 2 have no product"}, {"holds", "0 with"},
       {"holds", "2 with"}});

  run("a set-valued functor with an empty set: the arrows out of it need not be written, and one into it from a set with an element cannot be",
      "category C2 = chain 2\nsets E : C2 {\n  0 = {}\n  1 = {r}\n}\nsets F : C2 {\n  0 = {p}\n  1 = {}\n}\n",
      {{"holds", ""}, {"holds", "keeps"}, {"error", "is not given"}});

  const Value kan = run("set-valued functors: an instance, its classes and sections, its Kan extensions along an inclusion, Yoneda, the classifier",
                        "category C2 = chain 2\ncategory C4 = chain 4\nfunctor i : C2 -> C4 { 0 -> 0; 1 -> 2 }\n"
                        "sets X : C2 {\n  0 = {p, q}\n  1 = {r, s}\n  \"0≤1\" : p -> r, q -> r\n}\n"
                        "find classes X\nfind sections X\nsets L = lan X i\nsets R = ran X i\nsets B = pullback L i\ncheck B isomorphic X\ncheck yoneda X 0\nsets O = omega C2\ncheck classifier X\nfind subfunctors X\n"
                        "category E = elements X\nfunctor pr = projection E\nsets H = hom C4 1\ncheck L isomorphic H\n",
                        {{"holds", ""}, {"holds", ""}, {"holds", ""}, {"holds", "keeps"}, {"holds", "2 classes"}, {"holds", "2 sections"}, {"holds", "universal"}, {"holds", "universal"}, {"holds", ""}, {"holds", "bijection"}, {"holds", ""},
                         {"holds", ""}, {"holds", "matched one to one"}, {"holds", "subfunctors"}, {"holds", "4 objects"}, {"holds", ""}, {"holds", ""}, {"fails", ""}});
  s.require("a Kan extension's view: its sets at the four objects of the ordinal 4, of 2, 2, 2 and 1 elements on the right",
            kan.items()[7].get("view")->get("elements")->size() == 4 && kan.items()[7].get("view")->get("elements")->items()[3].size() == 1 && kan.items()[6].get("view")->get("elements")->items()[3].size() == 2);

  run("a set-valued functor that does not keep a composite is refused; one with an action missing cannot be carried out",
      "category Sq { f : A -> B; g : B -> D; h : A -> C; k : C -> D; g . f = k . h }\n"
      "sets X : Sq { A = {a}; B = {b}; C = {c}; D = {d1, d2}; f : a -> b; g : b -> d1; h : a -> c; k : c -> d2 }\n"
      "sets Y : Sq { A = {a}; B = {b}; C = {c}; D = {d1, d2}; f : a -> b; g : b -> d1; h : a -> c }\n",
      {{"holds", ""}, {"fails", "does not keep the composite"}, {"error", "the action of k is not given"}});

  const Value mon = run("a theory of monoids: the Boolean monoid is a model, another unit is not; associativity holds in the model and not by the axioms alone",
                        "theory Mon {\n  type x\n  m : x x -> x\n  e : I -> x\n  law associativity : (m * x) >> m = (x * m) >> m\n  law \"left unit\" : (e * x) >> m = x\n  law \"right unit\" : (x * e) >> m = x\n}\n"
                        "model And : Mon in sets { x = 2; m = 0 0 0 1; e = 1 }\nmodel Bad : Mon in sets { x = 2; m = 0 0 0 1; e = 0 }\ndiagram d = (m * x) >> m in Mon\n"
                        "check (m * x) >> m = (x * m) >> m in Mon\ncheck (m * x) >> m = (x * m) >> m in And\ncheck swap(x, x) >> swap(x, x) = x * x in Mon\ncheck m . (m * x) = d in Mon\ncheck And\n",
                        {{"holds", "3 laws"}, {"holds", ""}, {"fails", "left unit"}, {"holds", "x ⊗ x ⊗ x → x"}, {"fails", "diagrams differ"}, {"holds", "one matrix"}, {"holds", "one diagram"}, {"holds", ""}, {"holds", ""}});
  s.require("a diagram's view: 2 boxes and 5 wires, 3 in and 1 out; a model's view: each law with its verdict and both sides drawn",
            mon.items()[3].get("view")->get("left")->get("boxes")->size() == 2 && mon.items()[3].get("view")->get("left")->get("wires")->size() == 5 && mon.items()[3].get("view")->get("left")->get("inputs")->size() == 3 &&
                mon.items()[2].get("view")->get("laws")->size() == 3 && mon.items()[2].get("view")->get("laws")->items()[1].get("status")->text() == "fails" && mon.items()[2].get("view")->get("laws")->items()[0].get("left")->get("boxes")->size() == 2);

  run("bialgebras among matrices with the direct sum: over ℤ with the antipode −1 a Hopf algebra; over the Booleans not",
      "theory Hopf { type x; m : x x -> x; e : I -> x; d : x -> x x; c : x -> I; a : x -> x\n law bialgebra : m >> d = (d * d) >> (x * swap(x, x) * x) >> (m * m)\n law antipode : d >> (x * a) >> m = c >> e }\n"
      "model Z : Hopf in sums { x = 1; m = [1 1]; e = []; d = [1 | 1]; c = []; a = [-1] }\nmodel B : Hopf in sums boolean { x = 1; m = [1 1]; e = []; d = [1 | 1]; c = []; a = [1] }\n"
      "model F2 : Hopf in sums mod 2 { x = 1; m = [1 1]; e = []; d = [1 | 1]; c = []; a = [1] }\n",
      {{"holds", ""}, {"holds", "2 laws"}, {"fails", "antipode"}, {"holds", ""}});

  run("equivalence and isomorphism: the square of the ordinal 2 is the subsets of 2; the walking isomorphism is equivalent to a point and not isomorphic to it",
      "category C2 = chain 2\ncategory P = product C2 C2\ncategory S = subsets 2\ncheck P isomorphic S\ncategory W = iso\ncategory pt = point\ncheck W equivalent pt\ncheck W isomorphic pt\ncheck W is skeletal\n"
      "functor p1 = first P\nfunctor dg = diagonal C2\nfunctor back = compose p1 dg\nfunctor one = identity C2\ncheck back isomorphic one\ncategory A = arrows C2\ncategory O = op S\ncheck O isomorphic S\n",
      {{"holds", ""}, {"holds", ""}, {"holds", ""}, {"holds", "bijection"}, {"holds", ""}, {"holds", ""}, {"holds", "skeletons"}, {"fails", ""}, {"fails", "isomorphic"}, {"holds", ""}, {"holds", ""}, {"holds", ""}, {"holds", ""},
       {"holds", ""}, {"holds", "3 objects"}, {"holds", ""}, {"holds", ""}});

  run("a category that is not finite is said to be; equalities in it are still decided",
      "category N { a : o -> o }\ncheck a >> a = a . a in N\ncheck a = a >> a in N\nfind product o o in N\ncategory Br { a, b : o -> o; a . b . a = b . a . b }\ncheck a = b in Br\n",
      {{"undecided", "not built whole"}, {"holds", ""}, {"fails", "normal forms differ"}, {"error", "not built whole"}, {"undecided", ""}, {"undecided", "so far"}});

  const Value errors = run("what cannot be read or carried out is answered with its place and reason, and the script goes on",
                           "category C = chain 3\ncategory = chain 3\nfind product 0 7 in C\ncheck nothing\nfunctor F : C -> D { 0 -> 0 }\ncategory B = chain 99\ncheck \"0≤1\" >> \"0≤1\" = \"0≤2\" in C\n\n\nfind product 0 2 in C\n"
                           "category S = symmetric 5\ncategory SS = product S S\n",
                           {{"holds", ""}, {"error", ""}, {"error", "has no object named 7"}, {"error", "nothing is named nothing"}, {"error", "there is no category named D"}, {"error", "too large"}, {"error", "does not follow"}, {"holds", "0 with"},
                            {"holds", "120 arrows"}, {"error", "14400 arrows"}});
  s.require("a statement that is not understood is answered with its line and column and what could come there", errors.items()[1].get("reason")->text().find("line 2, column 10") == 0 && errors.items()[1].get("reason")->text().find("what could come here") != std::string::npos,
            errors.items()[1].get("reason")->text());
  s.require("the last statement stands on line 10, after two blank lines", errors.items()[7].get("line")->number() == 10);

  // The document.
  Value v = Value::map();
  v.set("text", "a \"quoted\" line\nand a tab\t").set("list", Value::list().push(1).push(2.5).push(true).push(Value())).set("text", "replaced \\ once");
  s.require("a document writes itself as JSON, escaping what must be", v.json() == "{\"text\":\"replaced \\\\ once\",\"list\":[1,2.5,true,null]}" && Value("a\"b\n").json() == "\"a\\\"b\\n\"", v.json());
  const std::string json = square.json();
  long depth = 0, least = 0;
  bool quoted = false;
  for (std::size_t k = 0; k < json.size(); k++) {
    if (json[k] == '"' && (k == 0 || json[k - 1] != '\\')) quoted = !quoted;
    if (!quoted && (json[k] == '[' || json[k] == '{')) depth++;
    if (!quoted && (json[k] == ']' || json[k] == '}')) depth--, least = std::min(least, depth);
  }
  s.require("the answer of a script is one balanced JSON list", json.front() == '[' && json.back() == ']' && depth == 0 && least == 0 && !quoted, std::to_string(json.size()) + " bytes");
  return s.done();
}
