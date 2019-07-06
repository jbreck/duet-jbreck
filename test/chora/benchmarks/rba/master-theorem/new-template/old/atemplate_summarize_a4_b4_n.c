int cost = 0;

void recursive(int n) {
  __VERIFIER_assume(n >= 0);
  if (n == 4 || n == 5 || n == 6 || n == 7) {
    cost += 7;
    return;
  }
  int m = n/4;
  recursive(m);
  recursive(m);
  recursive(m);
  recursive(m);
  cost += n;
  return;
}

void main(int n) {
  recursive(n);
}
