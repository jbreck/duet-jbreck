int __cost;

int lg_n_helper(int n) {
    int i;
    int r = 0;
    int j;
    __VERIFIER_assume(n > 0);
    for(i = 1; i != n; i *= 2) {
        r ++;
    }
    return r;
}

void main(int n) {
    __VERIFIER_assume(n >= 2);
    __cost += lg_n_helper(n);
}

