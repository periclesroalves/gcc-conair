// PR c++/49042
// { dg-options -std=c++11 }

template <class T>
class A
{
  T p;
public:
  template <class U> auto f() -> decltype(+p) { }
};

int main()
{
  A<int>().f<int>();
}
