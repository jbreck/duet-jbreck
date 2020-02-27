// NOTE: we don't use "tick.h" in this file
//   We do use a variable having the name "__cost" for consistency with
//    the other benchmarks, but that variable is not really a cost; it is
//    simply the variable on which we want to see bounds printed

int doWork(int n) {
    int retval = 1;
    if (n <= 0) return retval;

    // A recursive call in an unbounded loop
    while(__VERIFIER_nondet_int()) {
        retval = 2 * doWork(n - 1);
    }
    return retval;
}

int __cost;

void main(int n) {
    //__VERIFIER_assume(n >= 0); // Use this if you're using the assertion
    int retval = doWork(n);
    //__VERIFIER_assert(retval <= n+1);

    // We use a variable called "__cost" here because CHORA
    //   is designed to automatically print bounds on the
    //   variable having that name.
    __cost = retval;
}
