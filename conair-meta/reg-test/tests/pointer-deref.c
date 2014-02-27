#include<stdio.h>

int main () {
    int a = 5;
    double b = 9, c = 7;
    int *p, *r;
    double *q;

    p = &a;
    q =  &b;
    *p = 10;
    *q = 3;

    if (b == 3) {
        q = &c;
        *q = *p;
        r = NULL;
    }

    printf ("%d %f %f\n", a, b, c);

    return 0;
}
