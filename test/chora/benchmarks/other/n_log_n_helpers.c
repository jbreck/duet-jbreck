//#include "log.h"
//DECLARE_LOG(2); // this defines icra_log2

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

int n_lg_n_helper(int n) {
    int i;
    int r = 0;
    for(i = 0; i != n; i++) {
        r += lg_n_helper(n);
    }
    return r;
}

void main(int n) {
    __VERIFIER_assume(n >= 2);
    __cost += n_lg_n_helper(n);
}

