// { dg-do compile }
// { dg-options "--std=c++11" }
struct B
{
  virtual void f() final {}
  virtual void g() {}
  virtual void x() const {}
};

struct B2
{
  virtual void h() {}
};

struct D : B
{
  virtual void g() override final {} // { dg-error "overriding" }
};

template <class T> struct D2 : T
{
  void h() override {} // { dg-error "marked override, but does not override" }
};

template <class T> struct D3 : T
{
  void h() override {}
};

struct D4 : D
{
  void g() {} // { dg-error "virtual function" }
};

struct B3
{
  virtual void f() final final {} // { dg-error "duplicate virt-specifier" }
};

struct B4
{
  void f() final {} // { dg-error "marked final, but is not virtual" }
};

struct D5 : B
{
  void ff() override {} // { dg-error "marked override, but does not override" }
  virtual void fff() override {} // { dg-error "marked override, but does not override" }
  virtual void x() override {} // { dg-error "marked override, but does not override" }
  void g() override;
};

void D5::g() override {} // { dg-error "not allowed outside a class definition" }
void g() override {} // { dg-error "not allowed outside a class definition" }

int main()
{
  D2<B> d;
  D2<B2> d2;
  D3<B2> d3;
}
