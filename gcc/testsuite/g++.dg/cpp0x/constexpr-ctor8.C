// PR c++/46466
// { dg-options "-std=c++11 -fno-elide-constructors" }

struct S { bool b; };
constexpr S f() { return S{true}; }
static_assert(f().b,  "");
