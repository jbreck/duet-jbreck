// Verify that the size of a tree is an upper bound on its height

#include "assert.h"

int height(int size) {
  if (size == 0) {
    return 0;
  } else {
    int left_size = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= left_size && left_size < size);
    int right_size = size - left_size - 1;
    int left_height = height(left_size);
    int right_height = height(right_size);
    return (left_height < right_height ? right_height : left_height) + 1;
  }
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (n >= 0 && n <= 29) { 
    __VERIFIER_assert(height(n) <= n);
  }
}

