//case3/a-three/b-five/add-lin/a_three_b_five_add_lin_rec.c
// Answer: O(n)
#include "tick.h"

void linrec(int n) {
    if (n==0) return;
    tick(1);
    linrec(n-1);
}

void recursive(int n) {
  if (n >= 5 && n <= 9) {
    tick(9);
    return;
  }
  int m = n/5;
  recursive(m);
  recursive(m);
  recursive(m);
  linrec(m);
  return;
}

void main(int n) {
  recursive(n);
}
