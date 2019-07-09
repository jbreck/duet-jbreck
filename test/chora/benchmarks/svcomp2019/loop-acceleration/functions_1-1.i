# 1 "/nobackup/jbreck/sv-benchmarks/c/loop-acceleration/functions_1-1.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "/nobackup/jbreck/sv-benchmarks/c/loop-acceleration/functions_1-1.c"
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

unsigned int f(unsigned int z) {
  return z + 2;
}

int main(void) {
  unsigned int x = 0;

  while (x < 0x0fffffff) {
    x = f(x);
  }

  __VERIFIER_assert(!(x % 2));
}
