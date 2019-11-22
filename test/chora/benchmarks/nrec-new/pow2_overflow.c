#include "assert.h"

int pow2(int n) {
  if (n == 0) {
    return 1;
  } else {
    int r1 = pow2(n-1);
    int r2 = pow2(n-1);
    __VERIFIER_assert(r1 + r2 < 1073741824);
    return r1 + r2;
  }
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (0 <= n && n <= 29) {
    pow2(n);
  }
  return 0;
}

