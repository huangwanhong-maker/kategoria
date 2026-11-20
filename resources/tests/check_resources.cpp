// Checks of kategoria/resources: resource types, their laws and verdicts, allocations as morphisms, the order-dependence of
// finite grant systems, and the equivariance of operators.
//
// - A mixed type (money divisible, nurses in units, two clinics as distinct items, a permit as a quality): well formed;
//   amounts outside the carrier refused; combination by hand; a distinct item held twice invalid; halving a sum allowed and
//   halving a nurse refused; its report lawful, with the monoid laws, the order's compatibility and quantity-likeness held on
//   its finite model of 32 bundles (each kind up to 1).
// - A capacity on a signed balance: validity not closed under parts, refuted with the pair.
// - Finite algebras declared whole: ℤ/3 with the natural order a monoid but its order incompatible with combination (1 ≽ 0
//   while 1 + 2 = 0 ⋡ 2 = 0 + 2); saturating addition on {0, 1, 2} lawful and not cancellative; |a − b| not associative,
//   kategoria naming the failure; ℕ truncated with partial addition lawful; a partial addition whose undefinedness breaks
//   associativity refuted; max on {0, 1} quality-like and not quantity-like.
// - Laws on the generating processes: cash plus vouchers conserved by buying; not conserved once vouchers may be thrown away,
//   though still a monotone; a conversion that doubles refuted at its name.
// - Convertibility as a Petri net (2 H₂ + O₂ → 2 H₂O): reached with its witness, replayed; refuted by the hydrogen it would
//   need; refuted exhaustively without any law; undecided when the reachable bundles never end; a forged witness rejected.
// - Splittability: a cow converts into beef and leather jointly, but no split of one cow gives one recipient beef and the
//   other leather; ℕ² with disposal splittable on its model.
// - Allocations: a lawful one; one exceeding the pool; a distinct clinic given twice; a nurse left over where nurses may not
//   be disposed of.
// - Grant systems: two recipients drawing on one stock commute (and their transition monoid, validated by kategoria, has the
//   size brute force gives); a price that rises after each sale makes order matter, with the two outcomes named; of three
//   grants on two pools, exactly the pair that competes for one pool fails to commute.
// - Operators: the swap mutation on the arrangements of three items treats renamed items and renamed positions alike; moving
//   one named item to the front does not; uniform crossover on two bits is natural for flipping a bit, a crossover that
//   prefers one parent is not.

#include <kategoria/resources/algebra.hpp>
#include <kategoria/resources/finite.hpp>
#include <kategoria/resources/systems.hpp>
#include <kategoria/resources/verify.hpp>

#include <calx/verification/check.hpp>

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace kategoria::resources;
using R = Rational;

static Bundle b(std::initializer_list<long long> xs) {
  Bundle out;
  for (long long x : xs) out.push_back(R(x));
  return out;
}

static Type city(bool nurses_disposable = true) {
  Type T;
  T.name = "a city's means";
  T.components = {{"money", Quantity::nonnegative, 1, {{"pounds"}}},
                  {"staff", Quantity::natural, 1, {{"nurses", nurses_disposable}}},
                  {"sites", Quantity::natural, 1, {{"north", true, std::nullopt, true}, {"south", true, std::nullopt, true}}},
                  {"licence", Quantity::boolean, 1, {{"permit"}}}};
  T.declared = {"quantity-like"};
  return T;
}

static FiniteAlgebra table_algebra(std::string name, std::size_t n, std::function<Index(Index, Index)> op, std::function<bool(Index, Index)> conv) {
  FiniteAlgebra A;
  A.name = std::move(name);
  for (std::size_t i = 0; i < n; i++) A.elements.push_back(std::to_string(i));
  A.combine.assign(n, std::vector<Index>(n, none));
  A.converts.assign(n, std::vector<char>(n, 0));
  for (Index a = 0; a < n; a++)
    for (Index c = 0; c < n; c++) A.combine[a][c] = op(a, c), A.converts[a][c] = conv(a, c);
  A.unit = 0;
  return A;
}

int main() {
  calx::verification::Suite s;

  // ---- a mixed type ----
  {
    const Type T = city();
    s.require("a mixed type is well formed: 4 components, 5 kinds", well_formed(T).holds() && T.size() == 5);
    s.require("amounts outside the carrier are refused: 1.5 nurses, a permit of 2", !member(T, {R(0), R(3, 2), R(0), R(0), R(0)}) && !member(T, b({0, 0, 0, 0, 2})));
    s.require("combination by hand: pounds and nurses add, the permit joins", combine(T, b({10, 1, 1, 0, 0}), b({5, 2, 0, 0, 1})) == b({15, 3, 1, 0, 1}) &&
                                                                                combine(T, b({0, 0, 0, 0, 1}), b({0, 0, 0, 0, 1})) == b({0, 0, 0, 0, 1}));
    const auto why = invalid(T, b({0, 0, 2, 0, 0}));
    s.require("a distinct clinic held twice is invalid, and said so", why && why->find("distinct") != std::string::npos);
    bool halved = scale(T, b({10, 2, 0, 0, 0}), R(1, 2)) == b({5, 1, 0, 0, 0}), refused = false;
    try {
      scale(T, b({0, 1, 0, 0, 0}), R(1, 2));
    } catch (const std::invalid_argument&) {
      refused = true;
    }
    s.require("a sum of money halves; one nurse does not", halved && refused);
    Grid unit;
    unit.greatest = R(1);
    const Report rep = verify(T, {unit});
    bool construction = false, model = false, quantity = false;
    for (const auto& e : rep.entries) {
      if (e.method == Method::construction && e.law.find("commutative") != std::string::npos) construction = e.verdict.holds();
      if (e.method == Method::finite_model && e.law.find("compatibility") != std::string::npos) model = e.verdict.holds() && e.scope.find("32 bundles") != std::string::npos;
      if (e.law == "declared: quantity-like") quantity = e.verdict.holds();
    }
    s.require("its report is lawful: the laws by construction, the order compatible on its model of 32 bundles, quantity-like", rep.lawful() && construction && model && quantity);
    bool monoid = false;
    for (const auto& e : rep.entries)
      if (e.law == "the monoid laws on the finite model") monoid = e.verdict.holds() && e.verdict.reason.find("validates") != std::string::npos;
    s.require("the monoid laws on the model are decided by kategoria's validation of the totalisation", monoid);
  }

  // ---- a capacity on a signed balance ----
  {
    Type L;
    L.name = "a ledger";
    L.components = {{"balance", Quantity::integer, 1, {{"account", true, R(3)}}}};
    const Report rep = verify(L, {std::nullopt});
    bool refuted = false;
    for (const auto& e : rep.entries)
      if (e.law.find("validity") != std::string::npos) refuted = e.verdict.fails() && e.verdict.piece("left") == "4 balance.account";
    s.require("a capacity on a signed balance: validity is not closed under parts, refuted with the pair", refuted && !rep.lawful());
  }

  // ---- finite algebras declared whole ----
  {
    const auto z3 = table_algebra("ℤ/3 with the natural order", 3, [](Index a, Index c) { return (a + c) % 3; }, [](Index a, Index c) { return a >= c; });
    const Verdict m = monotone(z3);
    s.require("ℤ/3 is a commutative monoid", monoid_laws(z3).holds() && commutative(z3).holds());
    s.require("but its natural order is incompatible with combination, a counterexample named", m.fails() && !m.piece("left").empty());
    const auto sat = table_algebra("saturating addition on {0, 1, 2}", 3, [](Index a, Index c) { return std::min<Index>(a + c, 2); }, [](Index a, Index c) { return a >= c; });
    s.require("saturating addition is lawful and compatible, but not cancellative", monoid_laws(sat).holds() && monotone(sat).holds() && cancellative(sat).fails());
    const auto absd = table_algebra("|a − b| on {0, 1, 2}", 3, [](Index a, Index c) { return a > c ? a - c : c - a; }, [](Index a, Index c) { return a == c; });
    const Verdict am = monoid_laws(absd);
    s.require("|a − b| is not associative, refuted by kategoria's validation", am.fails() && am.reason.find("not a monoid") != std::string::npos);
    const auto trunc = table_algebra("ℕ up to 2 with partial addition", 3, [](Index a, Index c) { return a + c <= 2 ? a + c : none; }, [](Index a, Index c) { return a >= c; });
    s.require("ℕ truncated with partial addition is lawful in the strong sense, and compatible", monoid_laws(trunc).holds() && monotone(trunc).holds() && cancellative(trunc).holds());
    // 1 + 1 = 2, 2 + 2 = 3, 1 + 2 undefined: (1 + 1) + 2 = 3 but 1 + (1 + 2) is undefined.
    auto bad = table_algebra("a partial addition broken by its undefinedness", 4, [](Index a, Index c) -> Index {
      if (a == 0) return c;
      if (c == 0) return a;
      if (a == 1 && c == 1) return 2;
      if (a == 2 && c == 2) return 3;
      return none;
    }, [](Index a, Index c) { return a == c; });
    s.require("a partial addition whose undefinedness breaks associativity is refuted", monoid_laws(bad).fails());
    const auto mx = table_algebra("max on {0, 1}", 2, [](Index a, Index c) { return std::max(a, c); }, [](Index a, Index c) { return a >= c; });
    s.require("max on {0, 1} is quality-like and not quantity-like", quality_like(mx).holds() && quantity_like(mx).fails());
  }

  // ---- laws on the generating processes ----
  {
    Type E;
    E.name = "an exchange";
    E.components = {{"money", Quantity::natural, 1, {{"cash", false}, {"voucher", false}}}};
    E.conversions = {{"buy", b({1, 0}), b({0, 1})}};
    const Law value{"value", {R(1), R(1)}, true}, cash{"cash", {R(1), R(0)}, false};
    s.require("cash plus vouchers is conserved by buying, checked on the generators", verify_law(E, value).holds() && verify_law(E, value).reason.find("every free process") != std::string::npos);
    s.require("cash alone never increases (a monotone) but is not conserved", verify_law(E, cash).holds() && !verify_law(E, Law{"cash", {R(1), R(0)}, true}).holds());
    E.components[0].kinds[1].disposable = true;
    s.require("once vouchers may be thrown away, value is no longer conserved, though it is a monotone", verify_law(E, value).fails() && verify_law(E, Law{"value", {R(1), R(1)}, false}).holds());
    E.conversions.push_back({"inflate", b({1, 0}), b({0, 2})});
    const Verdict v = verify_law(E, Law{"value", {R(1), R(1)}, false});
    s.require("a conversion that doubles is refuted at its name", v.fails() && v.piece("at") == "inflate");
  }

  // ---- convertibility as a Petri net ----
  {
    Type M;
    M.name = "molecules";
    M.components = {{"matter", Quantity::natural, 1, {{"H2", false}, {"O2", false}, {"H2O", false}}}};
    M.conversions = {{"burn", b({2, 1, 0}), b({0, 0, 2})}};
    Type bare = M;
    M.laws = {{"hydrogen atoms", {R(2), R(0), R(2)}, true}, {"oxygen atoms", {R(0), R(2), R(1)}, true}};
    const auto yes = convertible(M, b({2, 1, 0}), b({0, 0, 2}));
    s.require("two H₂ and an O₂ become two H₂O, the witness replayed", yes.verdict.holds() && yes.witness.size() == 1 && yes.witness[0].what == "burn" && check_witness(M, b({2, 1, 0}), yes.witness, b({0, 0, 2})).holds());
    const auto no = convertible(M, b({1, 1, 0}), b({0, 0, 2}));
    s.require("one H₂ cannot: refuted by the hydrogen atoms it would need (2 against 4)", no.verdict.fails() && no.verdict.piece("monotone") == "hydrogen atoms");
    s.require("four H₂ and two O₂ become two H₂O with H₂ and O₂ left", convertible(M, b({4, 2, 0}), b({2, 1, 2})).verdict.holds());
    const auto exhaust = convertible(bare, b({2, 1, 0}), b({0, 0, 1}));
    s.require("without any law, refuted by examining every reachable bundle", exhaust.verdict.fails() && exhaust.verdict.reason.find("every bundle reachable") != std::string::npos);
    Type G;
    G.name = "a seed that multiplies";
    G.components = {{"plants", Quantity::natural, 1, {{"A", false}, {"B", false}}}};
    G.conversions = {{"grow", b({1, 0}), b({2, 0})}};
    s.require("undecided when the reachable bundles never end", convertible(G, b({1, 0}), b({0, 1}), 100).verdict.status == kategoria::kernel::Status::undecided);
    std::vector<Step> forged = {{"burn", b({0, 0, 3})}};
    s.require("a forged witness is rejected by the replay", check_witness(M, b({2, 1, 0}), forged, b({0, 0, 3})).fails());
  }

  // ---- splittability ----
  {
    Type C;
    C.name = "a cow and its products";
    C.components = {{"goods", Quantity::natural, 1, {{"cow"}, {"beef"}, {"leather"}}}};
    C.conversions = {{"butcher", b({1, 0, 0}), b({0, 1, 1})}};
    Grid g;
    g.greatest = R(1);
    const FiniteAlgebra A = truncation(C, g);
    const Verdict sp = splittable(A);
    s.require("one cow becomes beef and leather jointly, but cannot be split between one who wants beef and one who wants leather",
              sp.fails() && sp.piece("at") == "1 goods.cow");
    Type N;
    N.name = "two kinds of unit";
    N.components = {{"units", Quantity::natural, 1, {{"a"}, {"b"}}}};
    N.declared = {"splittable", "cancellative", "catalysis-free"};
    const Report rep = verify(N);
    s.require("ℕ² with disposal is splittable, cancellative and catalysis-free on its model", rep.lawful() && rep.count(kategoria::kernel::Status::holds) == rep.entries.size());
  }

  // ---- allocations as morphisms ----
  {
    const Type T = city();
    const Bundle pool = b({100, 5, 1, 1, 1});
    s.require("a lawful allocation of money, nurses, clinics and a permit", allocation(T, pool, {b({60, 3, 1, 0, 0}), b({40, 2, 0, 1, 1})}).verdict.holds());
    s.require("parts beyond the pool are refused", allocation(T, pool, {b({70, 3, 1, 0, 0}), b({40, 2, 0, 1, 1})}).verdict.fails());
    const auto twice = allocation(T, pool, {b({10, 1, 1, 0, 0}), b({10, 1, 1, 0, 0})});
    s.require("a distinct clinic given to two recipients is refused", twice.verdict.fails() && twice.verdict.reason.find("distinct") != std::string::npos);
    s.require("where nurses may not be disposed of, a nurse left over is refused", allocation(city(false), pool, {b({60, 2, 1, 0, 0}), b({40, 2, 0, 1, 1})}).verdict.fails() &&
                                                                                    allocation(city(false), pool, {b({60, 3, 1, 0, 0}), b({40, 2, 0, 1, 1})}).verdict.holds());
  }

  // ---- grant systems ----
  {
    // Two recipients drawing on a stock of two units: states (stock, a, b).
    System D;
    D.name = "a stock of two units";
    D.states = {"(2,0,0)", "(1,1,0)", "(1,0,1)", "(0,2,0)", "(0,1,1)", "(0,0,2)"};
    D.grants = {"A", "B"};
    D.action = {{1, 3, 4, none, none, none}, {2, 4, 5, none, none, none}};
    const auto I = independence(D);
    const auto M = transition_monoid(D);
    // Brute force: the distinct maps of all words up to length 4.
    std::set<std::vector<Index>> maps;
    for (int len = 0; len <= 4; len++)
      for (int w = 0; w < (1 << len); w++) {
        std::vector<Index> m(7);
        for (Index x = 0; x < 7; x++) {
          Index y = x;
          for (int i = 0; i < len; i++) y = y == 6 ? 6 : (D.action[(w >> i) & 1][y] == none ? 6 : D.action[(w >> i) & 1][y]);
          m[x] = y;
        }
        maps.insert(m);
      }
    s.require("two recipients drawing on one stock: the order of grants does not matter", I.verdict.holds() && I.commute[0][1]);
    s.require("their transition monoid is validated by kategoria, with the size brute force gives", M.verdict.holds() && M.maps.size() == maps.size());
    // A price that rises after each sale: A then B against B then A.
    System P;
    P.name = "a rising price";
    P.states = {"none sold", "A paid 1", "B paid 1", "A paid 1, B paid 2", "B paid 1, A paid 2"};
    P.grants = {"A buys", "B buys"};
    P.action = {{1, none, 4, none, none}, {2, 3, none, none, none}};
    const auto IP = independence(P);
    s.require("a price that rises after each sale makes order matter, the two outcomes named",
              IP.verdict.fails() && IP.verdict.piece("left") == "A paid 1, B paid 2" && IP.verdict.piece("right") == "B paid 1, A paid 2");
    // Three grants on two pools: 1 takes X, 2 takes Y, 3 takes X if it is there, else Y.
    System T3;
    T3.name = "two pools";
    const char* hx[] = {"-", "1", "3"};
    const char* hy[] = {"-", "2", "3"};
    for (int x = 0; x < 3; x++)
      for (int y = 0; y < 3; y++) T3.states.push_back(std::string("X:") + hx[x] + " Y:" + hy[y]);
    T3.grants = {"1 takes X", "2 takes Y", "3 takes X or else Y"};
    T3.action.assign(3, std::vector<Index>(9, none));
    for (int x = 0; x < 3; x++)
      for (int y = 0; y < 3; y++) {
        const Index at = x * 3 + y;
        if (x == 0) T3.action[0][at] = 1 * 3 + y;
        if (y == 0) T3.action[1][at] = x * 3 + 1;
        if (x == 0) T3.action[2][at] = 2 * 3 + y;
        else if (y == 0) T3.action[2][at] = x * 3 + 2;
      }
    const auto I3 = independence(T3);
    // Eight of the nine states are reachable: Y is never taken by 3 while X is free, since 3 takes X first.
    s.require("of three grants on two pools, exactly the pair competing for X fails to commute (eight states reachable)",
              I3.verdict.fails() && I3.commute[0][1] && I3.commute[1][2] && !I3.commute[0][2] && I3.reachable.size() == 8);
  }

  // ---- operators as kernels ----
  {
    // The arrangements of three items, each a vector; the swap mutation picks one of the three pairs of positions.
    std::vector<std::vector<int>> perms;
    std::vector<int> p = {0, 1, 2};
    do perms.push_back(p);
    while (std::next_permutation(p.begin(), p.end()));
    auto index = [&](const std::vector<int>& q) { return static_cast<Index>(std::find(perms.begin(), perms.end(), q) - perms.begin()); };
    Kernel swap{"the swap mutation", {}, std::vector<std::vector<R>>(6, std::vector<R>(6, R(0)))};
    Kernel front{"moving item 0 to the front", {}, std::vector<std::vector<R>>(6, std::vector<R>(6, R(0)))};
    for (std::size_t x = 0; x < 6; x++) {
      std::string name;
      for (int v : perms[x]) name += std::to_string(v);
      swap.points.push_back(name), front.points.push_back(name);
      for (auto [i, j] : std::vector<std::pair<int, int>>{{0, 1}, {0, 2}, {1, 2}}) {
        auto q = perms[x];
        std::swap(q[i], q[j]);
        swap.p[x][index(q)] += R(1, 3);
      }
      auto q = perms[x];
      q.erase(std::find(q.begin(), q.end(), 0));
      q.insert(q.begin(), 0);
      front.p[x][index(q)] = R(1);
    }
    // Renaming items: swap the values 0 ↔ 1, and 1 ↔ 2. Renaming positions: swap positions 0 ↔ 1.
    auto rename_items = [&](int a, int c) {
      std::vector<Index> s(6);
      for (std::size_t x = 0; x < 6; x++) {
        auto q = perms[x];
        for (int& v : q) v = v == a ? c : v == c ? a : v;
        s[x] = index(q);
      }
      return s;
    };
    std::vector<Index> positions(6);
    for (std::size_t x = 0; x < 6; x++) {
      auto q = perms[x];
      std::swap(q[0], q[1]);
      positions[x] = index(q);
    }
    s.require("the swap mutation treats renamed items and renamed positions alike", equivariant(swap, {rename_items(0, 1), rename_items(1, 2), positions}).holds());
    s.require("moving one named item to the front does not treat renamed items alike", equivariant(front, {rename_items(0, 1)}).fails());
    // Two bits; uniform crossover; flipping the second bit acts on both parents and the child.
    Kernel2 uniform{"uniform crossover", {"00", "01", "10", "11"}, {}}, first{"a crossover preferring the first parent's first bit and the smaller second", {"00", "01", "10", "11"}, {}};
    uniform.p.assign(4, std::vector<std::vector<R>>(4, std::vector<R>(4, R(0))));
    first.p = uniform.p;
    for (int x = 0; x < 4; x++)
      for (int y = 0; y < 4; y++) {
        for (int m = 0; m < 4; m++) {
          const int child = ((m & 2) ? (y & 2) : (x & 2)) | ((m & 1) ? (y & 1) : (x & 1));
          uniform.p[x][y][child] += R(1, 4);
        }
        first.p[x][y][(x & 2) | std::min(x & 1, y & 1)] = R(1);
      }
    const std::vector<Index> flip = {1, 0, 3, 2};
    s.require("uniform crossover is natural for flipping a bit", equivariant(uniform, {flip}).holds());
    s.require("a crossover that prefers the smaller second bit is not", equivariant(first, {flip}).fails());
  }

  return s.done();
}
