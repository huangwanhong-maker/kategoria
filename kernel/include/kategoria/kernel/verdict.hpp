// Verdicts: what a claim is answered with.
//
// A claim about categories is answered in one of three ways, and never with a bare yes or no:
//
//   holds      with the evidence that makes it so (a witness for a claim that something exists, the count of instances
//              examined for a claim about all of them);
//   fails      with a counterexample: the instance at which it fails, named, with both sides;
//   undecided  with the reason no answer was reached (a bound on a search, a completion that did not end).
//
// Evidence is a list of named pieces in words, so that a reader, a page or another program can show it. What stands
// behind a verdict is stated by the function that returns it: a claim about every instance of a finite structure is
// decided by examining every instance; a claim that something exists is decided by a search, and the witness found is
// then checked by a function that does not share the search's code (the library's rule, docs/theory.md §2).

#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace kategoria::kernel {

enum class Status { holds, fails, undecided };

// A number with its noun: "1 arrow", "4 arrows".
inline std::string count(std::size_t n, const std::string& one, const std::string& many = {}) { return std::to_string(n) + " " + (n == 1 ? one : many.empty() ? one + "s" : many); }

inline std::string_view word(Status s) { return s == Status::holds ? "holds" : s == Status::fails ? "fails" : "undecided"; }

struct Evidence {
  std::string role;   // what this piece is: "at", "left", "right", "witness", …
  std::string value;  // in words
};

struct Verdict {
  Status status = Status::undecided;
  std::string claim;               // what was asked
  std::string reason;              // why it holds, where it fails, or why it is not decided
  std::vector<Evidence> evidence;  // the witness or the counterexample, piece by piece
  std::size_t examined = 0;        // how many instances were examined

  bool holds() const { return status == Status::holds; }
  bool fails() const { return status == Status::fails; }
  explicit operator bool() const { return holds(); }

  Verdict& with(std::string role, std::string value) {
    evidence.push_back({std::move(role), std::move(value)});
    return *this;
  }
  // The value of the first piece of evidence in this role, or "".
  std::string_view piece(std::string_view role) const {
    for (const auto& e : evidence)
      if (e.role == role) return e.value;
    return {};
  }

  static Verdict yes(std::string claim, std::string reason = {}, std::size_t examined = 0) {
    return {Status::holds, std::move(claim), std::move(reason), {}, examined};
  }
  static Verdict no(std::string claim, std::string reason, std::size_t examined = 0) {
    return {Status::fails, std::move(claim), std::move(reason), {}, examined};
  }
  static Verdict unknown(std::string claim, std::string reason, std::size_t examined = 0) {
    return {Status::undecided, std::move(claim), std::move(reason), {}, examined};
  }
};

// Both hold: the first that does not is returned, else the first with the examined instances of both.
inline Verdict both(Verdict a, const Verdict& b) {
  if (!a.holds()) return a;
  if (!b.holds()) return b;
  a.examined += b.examined;
  return a;
}

}  // namespace kategoria::kernel
