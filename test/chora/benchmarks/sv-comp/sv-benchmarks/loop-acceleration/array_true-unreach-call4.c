#define N 1024

int main(void) {
  int A[N];
  int i;

  A[N-1] = 0;

  for (i = 0; A[i] != 0; i++) {
  }

  __VERIFIER_assert(i <= N);
}
