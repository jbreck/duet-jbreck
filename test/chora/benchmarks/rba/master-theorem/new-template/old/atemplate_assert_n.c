int cost = 0;

void recursive(int n) {
  __VERIFIER_assume(n >= 0); // presently needed, I guess
  if (n == 2 || n == 3) {
    cost += 4;
    return;
  }
  int m = n/2;
  recursive(m);
  recursive(m);
  cost += 1;
  return;
}

void main(int n) {
  recursive(n);
  __VERIFIER_assert(cost < 3*n);
}
