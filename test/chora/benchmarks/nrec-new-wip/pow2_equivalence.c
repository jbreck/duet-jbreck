#include "assert.h"

int pow2(int n) {
  if (n == 0) {
    return 1;
  } else {
    int r1 = pow2(n-1);
    int r2 = pow2(n-1);
    return r1 + r2;
  }
}

int pow2_loop(int n) {
    int r = 1;
    for(int i = 0; i != n; i++) {
        r = 2*r;
    }
    return r;
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (0 <= n && n <= 29) {
    __VERIFIER_assert(pow2(n) == pow2_loop(n));
  }
  return 0;
}

