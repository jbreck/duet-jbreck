# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
# 11 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"
extern int __VERIFIER_nondet_int(void);


int fibonacci(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibonacci(n-1) + fibonacci(n-2);
    }
}


int main() {
    int x = 9;
    int result = fibonacci(x);
    if (result == 34) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
