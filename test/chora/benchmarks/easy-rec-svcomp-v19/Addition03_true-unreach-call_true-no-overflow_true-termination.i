# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition03_true-unreach-call_true-no-overflow_true-termination.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition03_true-unreach-call_true-no-overflow_true-termination.c"
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
# 11 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition03_true-unreach-call_true-no-overflow_true-termination.c"
extern int __VERIFIER_nondet_int(void);

long long addition(long long m, long long n) {
    if (n == 0) {
        return m;
    }
    if (n > 0) {
        return addition(m+1, n-1);
    }
    if (n < 0) {
        return addition(m-1, n+1);
    }
}


int main() {
    int m = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    long long result = addition(m,n);
    if (m < 100 || n < 100 || result >= 200) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
