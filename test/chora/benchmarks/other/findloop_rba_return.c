int __cost;
int nTicks;
int find(int * A, int n) { return findAux(A,0,n,0,0); }
int findAux(int * A, int i, int n, int sum, int nAdded) {
    nTicks++;
    if (i >= n) { if (sum == 0 && nAdded > 0) {return 1;} else {return 0;} }
    int retval = 0;
    for(int tries = 0; tries < 2; tries++) {
        retval += findAux(A,i+1,n,sum,nAdded); // first try does not include A[i]
        if (retval != 0) break;
        sum += A[i]; nAdded += 1; // second try does include A[i]
    }
    return retval;
}
void main(int n) {
    int * A;
    // A = malloc(n);
    __cost = find(A,n); // NOTE: Weirdly assinging __cost to return of find!!!
}
