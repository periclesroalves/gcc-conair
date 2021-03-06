// { dg-do compile }
// { dg-options -std=c++0x }

void f (int);

int
main() {

  int a = 4;
  int b = 5;
  int (*x)[b] = new int[a][b]; // { dg-error "array size.*must be constant|usable in a constant" }

  x[2][1] = 7;

  for (int i = 0; i < a; ++i)
    for (int j = 0; j < b; ++j)
      f (x[i][j]);
  delete [] x;
}
