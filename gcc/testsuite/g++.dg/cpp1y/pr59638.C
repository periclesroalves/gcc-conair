// PR c++/59638
// { dg-do compile }
// { dg-options "-std=gnu++1y" }

void (*a)(auto);         // { dg-error "template declaration" }

void (*b)(auto) = 0;     // { dg-error "template declaration" }

typedef void (*f)(auto); // { dg-error "template declaration" }

struct A
{
  int i;
};
