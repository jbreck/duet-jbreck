// This program is intended to illustrate why we can't just allow bounding
//   functions b_k to decrease without being careful.
// The dual-height analysis that I proposed (-chora-dual and -chora-full)
//   does the right thing.  Those are sound analyses.
// Merely allowing decrease without being otherwise careful is unsound,
//   and this program illustrates that fact.
int x;
int y;
int __cost;
void decr(int n) {
    if (n == 0 || n == 1) { x = 0; y = 0; return; }
    decr(n-1);
    int x_first = x;
    decr(n-2);
    int y_second = y;
    y = y_second + 1;
    x = x_first + 1;
}

void main(int n) {
    if (n > 0) {
        decr(n);
        __cost = x - y;
        if (__VERIFIER_nondet_int()) {
            __VERIFIER_assert(x == y);
        }
    }
}
