// PR c++/49205
// { dg-options -std=c++11 }

#include <initializer_list>

struct A {
  template<typename ...T> A(T...);
  A(std::initializer_list<short>);
  A(std::initializer_list<long>);
};

A a{};
