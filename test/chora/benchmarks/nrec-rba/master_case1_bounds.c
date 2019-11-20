//case1/a-two/b-four/add-const/a_two_b_four_add_const.c
// Answer: O(sqrt(n))  i.e.  2^log_4(N)
#include "tick.h"

void recursive(int n) {
  if (n >= 4 && n <= 7) {
    tick(1);
    return;
  }
  int m = n/4;
  recursive(m);
  recursive(m);
  tick(1);
  return;
}

void main(int n) {
  init_tick(0);
  recursive(n);
}
