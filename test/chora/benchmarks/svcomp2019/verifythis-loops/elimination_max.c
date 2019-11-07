extern void *calloc(unsigned int nmemb, unsigned int size);
extern void __VERIFIER_error(void) __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
    if(!cond) __VERIFIER_error();
}

extern int __VERIFIER_nondet_int(void);

int main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 0);
    int *a = calloc(n, sizeof(int));

    int x = 0;
    int y = n - 1;

    while(x < y) {
        /* Possible formulation of the invariant:
         *
         * Claude Marche, Jean-Christophe Filliatre
         * forall i. (0 <= i || y < i < n)  ==>  (a[i] <= a[x] && a[i] <= a[y])
         *
         * Gerhard Schellhorn, Bogdan Tofan, Gidon Ernst
         * exists k. x <= k && k < y && k < n && a[k] = max(a, n)
         *      (where max a builtin logic function)
         */
        if(a[x] <= a[y]) x++;
        else y--;
    }

    int i;

    i = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= i && i < n);
    __VERIFIER_assert(a[i] <= a[x]);

    for(i=0; i<n; i++) {
        __VERIFIER_assert(a[i] <= a[x]);
    }

    return x;
}
