// A document: the tree in which the answers of a script are handed on.
//
// What a statement answers (a verdict with its evidence, and what there is to draw: a category, a functor, a cone, a
// derivation, a string diagram) is data for whoever shows it: a page, a notebook, another program. It is held as a
// small tree of maps, lists, texts and numbers, which writes itself as JSON (ECMA-404). Nothing here reads JSON.

#pragma once

#include <cmath>
#include <cstddef>
#include <cstdio>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace kategoria::script {

class Value {
 public:
  enum class Kind { null, boolean, number, text, list, map };

  Value() = default;
  Value(bool b) : kind_(Kind::boolean), boolean_(b) {}
  Value(double n) : kind_(Kind::number), number_(n) {}
  Value(int n) : kind_(Kind::number), number_(n) {}
  Value(std::size_t n) : kind_(Kind::number), number_(static_cast<double>(n)) {}
  Value(unsigned n) : kind_(Kind::number), number_(n) {}
  Value(long long n) : kind_(Kind::number), number_(static_cast<double>(n)) {}
  Value(std::string s) : kind_(Kind::text), text_(std::move(s)) {}
  Value(std::string_view s) : kind_(Kind::text), text_(s) {}
  Value(const char* s) : kind_(Kind::text), text_(s) {}

  static Value list() {
    Value v;
    v.kind_ = Kind::list;
    return v;
  }
  static Value map() {
    Value v;
    v.kind_ = Kind::map;
    return v;
  }
  template <class Range>
  static Value of(const Range& range) {
    Value v = list();
    for (const auto& x : range) v.push(Value(x));
    return v;
  }

  Kind kind() const { return kind_; }
  Value& push(Value v) {
    kind_ = Kind::list;
    items_.push_back(std::move(v));
    return *this;
  }
  Value& set(std::string key, Value v) {
    kind_ = Kind::map;
    for (auto& [k, old] : fields_)
      if (k == key) {
        old = std::move(v);
        return *this;
      }
    fields_.emplace_back(std::move(key), std::move(v));
    return *this;
  }
  // The field of this name, or null.
  const Value* get(std::string_view key) const {
    for (auto& [k, v] : fields_)
      if (k == key) return &v;
    return nullptr;
  }
  const std::vector<Value>& items() const { return items_; }
  const std::vector<std::pair<std::string, Value>>& fields() const { return fields_; }
  const std::string& text() const { return text_; }
  double number() const { return number_; }
  bool boolean() const { return boolean_; }
  std::size_t size() const { return kind_ == Kind::map ? fields_.size() : items_.size(); }

  std::string json() const {
    std::string out;
    write(out);
    return out;
  }

 private:
  static void quote(std::string& out, const std::string& s) {
    out += '"';
    for (const char c : s) {
      switch (c) {
        case '"': out += "\\\""; break;
        case '\\': out += "\\\\"; break;
        case '\n': out += "\\n"; break;
        case '\r': out += "\\r"; break;
        case '\t': out += "\\t"; break;
        default:
          if (static_cast<unsigned char>(c) < 0x20) {
            char buffer[8];
            std::snprintf(buffer, sizeof buffer, "\\u%04x", static_cast<unsigned>(static_cast<unsigned char>(c)));
            out += buffer;
          } else {
            out += c;
          }
      }
    }
    out += '"';
  }
  void write(std::string& out) const {
    switch (kind_) {
      case Kind::null: out += "null"; break;
      case Kind::boolean: out += boolean_ ? "true" : "false"; break;
      case Kind::number: {
        if (!std::isfinite(number_)) {
          out += "null";
        } else if (number_ == std::floor(number_) && std::fabs(number_) < 1e15) {
          out += std::to_string(static_cast<long long>(number_));
        } else {
          char buffer[32];
          std::snprintf(buffer, sizeof buffer, "%.17g", number_);
          out += buffer;
        }
        break;
      }
      case Kind::text: quote(out, text_); break;
      case Kind::list:
        out += '[';
        for (std::size_t k = 0; k < items_.size(); k++) {
          if (k) out += ',';
          items_[k].write(out);
        }
        out += ']';
        break;
      case Kind::map:
        out += '{';
        for (std::size_t k = 0; k < fields_.size(); k++) {
          if (k) out += ',';
          quote(out, fields_[k].first);
          out += ':';
          fields_[k].second.write(out);
        }
        out += '}';
        break;
    }
  }

  Kind kind_ = Kind::null;
  bool boolean_ = false;
  double number_ = 0;
  std::string text_;
  std::vector<Value> items_;
  std::vector<std::pair<std::string, Value>> fields_;
};

}  // namespace kategoria::script
