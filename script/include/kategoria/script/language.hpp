// The language of scripts: declarations of categories, functors, transformations, set-valued functors, theories and
// their models, and claims about them.
//
// A script is a sequence of statements, one to a line; a statement with a block in braces runs to the brace that closes
// it. A '#' begins a comment. Inside a block, items are separated by new lines or by ';'. The grammar of one statement
// is written below in BNF and read by morphe's reader (morphe/formal/bnf.hpp), which parses it by Earley's algorithm
// and, where a statement is wrong, says how far it is right and what could have come next.
//
//   category Sq { objects A B C D;  f : A -> B;  g : B -> D;  h : A -> C;  k : C -> D;  g . f = k . h }
//   category P = product C D          chain 4 · discrete 3 · subsets 3 · divisors 12 · finset 2 · simplex 2 · mult 6 ·
//                                     cyclic 4 · symmetric 3 · dihedral 4 · quaternion · arrow · iso · pair · point ·
//                                     op C · skeleton C · arrows C · elements X · subobjects X · algebras L · kleisli L ·
//                                     product C D · sum C D · slice C A · coslice C A · functors C D · comma F G
//   functor F : C -> D { A -> X;  f -> v . u }
//   functor G = left adjoint F        identity C · compose G F · constant C D X · right adjoint F · diagonal C ·
//                                     first P · second P · projection E
//   transformation t : F => G { A -> u }
//   sets X : C { A = {a, b};  B = {c};  f : a -> c, b -> c }
//   sets Y = lan X K                  hom C A · constant C 2 · pullback Y K · ran X K · omega C
//   theory M { type x;  m : x x -> x;  e : I -> x;  law unit : (e * x) >> m = x }
//   model B : M in sets { x = 2;  m = 0 0 0 1;  e = 1 }        in sets · relations · matrices · sums, then: mod 2 · boolean
//   diagram d = (m * x) >> m in M
//   check g . f = k . h in Sq         check F · check F is faithful · check f is mono in C · check C is complete ·
//                                     check L -| R · check C equivalent D · check C isomorphic D · check yoneda X A ·
//                                     check classifier X · check d = d2 in M
//   find product A B in C             find limit F · find colimit F · find terminal in C · find equalizer f g in C ·
//                                     find exponential A B in C · find functors C -> D · find transformations F => G ·
//                                     find generators C · find rules C · find table C · find subfunctors X ·
//                                     find sections X · find classes X
//
// Composition is written g . f (g after f; also ∘) or f >> g (f then g; also ⨟); the tensor is * (also ⊗); an arrow
// is -> (also →) and a transformation => (also ⇒). A name is letters, digits, _ and ', or anything in double quotes.
// In a set-valued functor an arrow out of an object with no element need not be written: its function is the empty one.

#pragma once

#include <morphe/formal/bnf.hpp>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

namespace kategoria::script {

inline std::string_view grammar_text() {
  return R"bnf(
statement ::= _ ( category | functor | transformation | sets | theory | model | diagram | check | find ) _ ;

_    ::= [ \t\n]* ;
_s   ::= [ \t]* ;
_sp  ::= [ \t]+ ;
_sep ::= _s ( [\n;] _s )+ ;

name   ::= ident | number | quoted ;
ident  ::= [A-Za-z_] [A-Za-z0-9_']* ;
number ::= [0-9]+ ;
quoted ::= '"' [^"\n]* '"' ;
names  ::= name ( _s "," _s name )* ;
arrow  ::= "->" | "→" ;
darrow ::= "=>" | "⇒" ;

expr    ::= ethen | eafter ;
ethen   ::= etensor ( _s ( ">>" | "⨟" ) _s etensor )* ;
eafter  ::= etensor ( _s ( "." | "∘" ) _s etensor )+ ;
etensor ::= eatom ( _s ( "*" | "⊗" ) _s eatom )* ;
eatom   ::= eparen | eswap | eid | name ;
eparen  ::= "(" _s expr _s ")" ;
eswap   ::= "swap" _s "(" _s name _s "," _s name _s ")" ;
eid     ::= "id" _sp name ;

category ::= "category" _sp name _s ( cblock | "=" _s cexpr ) ;
cblock   ::= "{" _ ( citem ( _sep citem )* _ )? "}" ;
citem    ::= objects | edge | equation ;
objects  ::= ( "objects" | "object" ) ( _sp name | _s "," _s name )+ ;
edge     ::= names _s ":" _s name _s arrow _s name ;
equation ::= expr _s "=" _s expr ;
cexpr    ::= cfamily | cplain | cunary | cbinary ;
cfamily  ::= cfam _sp number ;
cfam     ::= "chain" | "discrete" | "subsets" | "divisors" | "finset" | "simplex" | "mult" | "cyclic" | "symmetric" | "dihedral" ;
cplain   ::= "arrow" | "iso" | "pair" | "point" | "quaternion" ;
cunary   ::= cuop _sp name ;
cuop     ::= "op" | "skeleton" | "elements" | "subobjects" | "arrows" | "algebras" | "kleisli" ;
cbinary  ::= cbop _sp name _sp name ;
cbop     ::= "product" | "sum" | "slice" | "coslice" | "functors" | "comma" ;

functor ::= "functor" _sp name _s ( ":" _s name _s arrow _s name _s ablock | "=" _s fexpr ) ;
ablock  ::= "{" _ ( assign ( _sep assign )* _ )? "}" ;
assign  ::= name _s arrow _s expr ;
fexpr   ::= fone | ftwo | fthree ;
fone    ::= fop _sp name ;
fop     ::= "identity" | "left adjoint" | "right adjoint" | "diagonal" | "first" | "second" | "projection" ;
ftwo    ::= "compose" _sp name _sp name ;
fthree  ::= "constant" _sp name _sp name _sp name ;

transformation ::= "transformation" _sp name _s ":" _s name _s darrow _s name _s ablock ;

sets    ::= "sets" _sp name _s ( ":" _s name _s sblock | "=" _s sexpr ) ;
sblock  ::= "{" _ ( sitem ( _sep sitem )* _ )? "}" ;
sitem   ::= carrier | action ;
carrier ::= name _s "=" _s "{" _s ( name ( _s "," _s name )* _s )? "}" ;
action  ::= name _s ":" _s pair ( _s "," _s pair )* ;
pair    ::= name _s arrow _s name ;
sexpr   ::= sbinary | somega ;
sbinary ::= sop _sp name _sp name ;
sop     ::= "hom" | "constant" | "pullback" | "lan" | "ran" ;
somega  ::= "omega" _sp name ;

theory ::= "theory" _sp name _s tblock ;
tblock ::= "{" _ ( titem ( _sep titem )* _ )? "}" ;
titem  ::= types | box | law ;
types  ::= ( "types" | "type" ) ( _sp name | _s "," _s name )+ ;
box    ::= names _s ":" _s wires _s arrow _s wires ;
wires  ::= name ( ( _s ( "*" | "⊗" ) _s | _sp ) name )* ;
law    ::= "law" _sp ( name _s ":" _s )? expr _s "=" _s expr ;

model   ::= "model" _sp name _s ":" _s name _sp "in" _sp world _s mblock ;
world   ::= wkind ( _sp ring )? ;
wkind   ::= "sets" | "relations" | "matrices" | "sums" ;
ring    ::= "mod" _sp number | "boolean" ;
mblock  ::= "{" _ ( mitem ( _sep mitem )* _ )? "}" ;
mitem   ::= name _s "=" _s ( matrix | values ) ;
values  ::= integer ( _sp integer )* ;
matrix  ::= "[" _s ( row ( _s "|" _s row )* _s )? "]" ;
row     ::= integer ( _sp integer )* ;
integer ::= "-"? [0-9]+ ;

diagram ::= "diagram" _sp name _s "=" _s expr _sp "in" _sp name ;

check    ::= "check" _sp ( cequal | cadjoint | cprop | crel | cyoneda | cclass | cname ) ;
cequal   ::= expr _s "=" _s expr _sp "in" _sp name ;
cadjoint ::= name _s ( "-|" | "⊣" ) _s name ;
cprop    ::= name _sp "is" ( _sp name )+ ;
crel     ::= name _sp rel _sp name ;
rel      ::= "equivalent" | "isomorphic" ;
cyoneda  ::= "yoneda" _sp name _sp name ;
cclass   ::= "classifier" _sp name ;
cname    ::= name ;

find    ::= "find" _sp ( qlimit | qshape | qfun | qnat | qlist ) ;
qlimit  ::= qkind _sp name ;
qkind   ::= "limit" | "colimit" ;
qshape  ::= shape ( _sp name )* _sp "in" _sp name ;
shape   ::= "product" | "coproduct" | "equalizer" | "coequalizer" | "pullback" | "pushout" | "terminal" | "initial" | "exponential" ;
qfun    ::= "functors" _sp name _s arrow _s name ;
qnat    ::= "transformations" _sp name _s darrow _s name ;
qlist   ::= qwhat _sp name ;
qwhat   ::= "generators" | "subfunctors" | "sections" | "classes" | "rules" | "table" ;
)bnf";
}

// The compiled grammar, made once.
inline const morphe::formal::Bnf& grammar() {
  static const morphe::formal::Bnf bnf = morphe::formal::compile_bnf(grammar_text());
  return bnf;
}

// A statement cut from a script: its text (comments blanked, so that places in it are places in the script) and the
// line it begins on, from 1.
struct Statement {
  std::string text;
  std::size_t line = 1;
};

// The statements of a script. A statement begins on a line that is not blank and runs to the end of that line, or, where
// braces are open, to the line on which the last of them closes.
inline std::vector<Statement> statements(std::string_view script) {
  std::string clean;
  bool quoted = false, comment = false;
  for (const char c : script) {
    if (c == '\r') continue;
    if (c == '\n') quoted = false, comment = false;
    else if (!comment && c == '"') quoted = !quoted;
    else if (!quoted && c == '#') comment = true;
    clean += comment && c != '\n' ? ' ' : c;
  }
  std::vector<Statement> out;
  Statement now;
  std::size_t line = 1, depth = 0;
  bool open = false;
  quoted = false;
  auto close = [&] {
    std::size_t end = now.text.find_last_not_of(" \t\n");
    if (end != std::string::npos) now.text.resize(end + 1), out.push_back(now);
    now = {}, open = false, depth = 0;
  };
  for (const char c : clean) {
    if (c == '\n') {
      line++, quoted = false;
      if (open && depth == 0) close();
      else if (open) now.text += c;
      continue;
    }
    if (!open) {
      if (c == ' ' || c == '\t') continue;
      open = true, now.line = line;
    }
    if (c == '"') quoted = !quoted;
    if (!quoted && c == '{') depth++;
    if (!quoted && c == '}' && depth > 0) depth--;
    now.text += c;
  }
  if (open) close();
  return out;
}

// The text of a name: what is between the quotes of a quoted one.
inline std::string name_of(const morphe::formal::ParseNode& node) {
  const std::string& t = node.text;
  return t.size() >= 2 && t.front() == '"' ? t.substr(1, t.size() - 2) : t;
}

}  // namespace kategoria::script
