// PR c++/59113
// { dg-do compile }
// { dg-options "-std=gnu++1y" }

void foo()
{
  void bar(auto) {} // { dg-error "function-definition|auto|not permitted" }
}

auto i = 0;
