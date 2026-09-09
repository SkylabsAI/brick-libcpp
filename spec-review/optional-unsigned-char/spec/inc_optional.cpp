// Force the concrete class instance and both in-scope value-constructor forms.
#include <optional>

template class std::optional<unsigned char>;

namespace {

inline std::optional<unsigned char> force_rvalue_ctor(unsigned char b) {
  return std::optional<unsigned char>(static_cast<unsigned char&&>(b));
}

inline std::optional<unsigned char> force_lvalue_ctor(unsigned char& b) {
  return std::optional<unsigned char>(b);
}

} // namespace
