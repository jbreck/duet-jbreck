#include "tick.h"

void work(int n) {
    for(int i = 0; i < n; i++) {
        tick(1);
    }
}

int main(int argc, char ** argv) {
    init_tick(0);
    int P = (argv[1] != 0) ? atoi(argv[1]) : 0;
    work(P);
    int maxP0 = (P < 0) ? 0 : P;
    __VERIFIER_assert(__cost == maxP0);
    return 0;
}
