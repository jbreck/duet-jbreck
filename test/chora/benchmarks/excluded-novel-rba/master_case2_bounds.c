// case2/a-four/b-two/add-quad/a_four_b_two_add_quad_loop.c
// Answer: O(n^2*lg(n))
#include "tick.h"

void loop(int n) {
  int i,j;
  for(i=0; i<n; i++){
    for(j=0; j<n; j++){
      tick(1);
    }
  }
}

void recursive(int n) {
  if (n >= 2 && n <= 3) {
    tick(3);
    return;
  }
  int m = n/2;
  recursive(m);
  recursive(m);
  recursive(m);
  recursive(m);
  loop(m);
  return;
}

void main(int n) {
  init_tick(0);
  recursive(n);
}
