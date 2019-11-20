
int cost; // current (memory) usage

#define init_tick(k) {cost = (k);}
// You could add a semicolon here, and __VERIFIER_assume(hwm >= cost)


#define tick(k) { \
                 __VERIFIER_assume(cost >= 0); \
                 __VERIFIER_assume(cost + k >= 0); \
                 cost = cost + (k); \
                 }

