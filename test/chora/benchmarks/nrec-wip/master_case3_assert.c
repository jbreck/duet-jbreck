//case3/a-three/b-five/add-lin/a_three_b_five_add_lin_rec.c
// Answer: O(n)
#include "tick.h"

void linrec(int n) {
    if (n==0) return;
    __cost++;
    linrec(n-1);
}

void recursive(int n) {
  //if (n == 5 || n == 6 || n == 7 || n == 8 || n == 9) {
  if (n >= 5 && n <= 9) {
  //if (n <= 9) {
    __cost += 9;
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
  init_tick(0);
  __VERIFIER_assume(n >= 5);
  recursive(n);

  if (__VERIFIER_nondet_int()) {
    // This pattern is, in effect, an assert without an assume
    __VERIFIER_assert((__cost <= 9 || __cost <= 3 * n));
    __VERIFIER_assume(0);
  }

}
