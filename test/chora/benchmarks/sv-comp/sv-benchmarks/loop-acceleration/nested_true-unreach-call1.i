# 1 "/home/turetsky/chora/duet-jbreck/test/chora/benchmarks/sv-comp/sv-benchmarks/loop-acceleration/nested_true-unreach-call1.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/home/turetsky/chora/duet-jbreck/test/chora/benchmarks/sv-comp/sv-benchmarks/loop-acceleration/nested_true-unreach-call1.c"
int main(void) {
  unsigned int x = 0;
  unsigned int y = 0;

  while (x < 0x0fffffff) {
    y = 0;

    while (y < 10) {
      y++;
    }

    x++;
  }

  __VERIFIER_assert(x % 2);
}
