# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition01_true-unreach-call_true-no-overflow_true-termination.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition01_true-unreach-call_true-no-overflow_true-termination.c"
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
# 11 "/afs/cs.wisc.edu/u/j/b/jbreck/research/2013/chora/workspace/test/chora/benchmarks/easy-rec-svcomp-v19/Addition01_true-unreach-call_true-no-overflow_true-termination.c"
extern int __VERIFIER_nondet_int(void);

int addition(int m, int n) {
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
    if (m < 0 || m > 1073741823) {


        return 0;
    }
    int n = __VERIFIER_nondet_int();
    if (n < 0 || n > 1073741823) {


        return 0;
    }
    int result = addition(m,n);
    if (result == m + n) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}
