int __cost;
int nTicks;
int find(int * A, int n) { return findAux(A,0,n,0,0); }
int findAux(int * A, int i, int n, int sum, int nAdded) {
    nTicks++;
    if (i >= n) { if (sum == 0 && nAdded > 0) {return 1;} else {return 0;} }
    int first = findAux(A,i+1,n,sum,nAdded); // skip A[i]
    if (first > 0) return first;
    return findAux(A,i+1,n,sum + A[i],nAdded+1); // add in A[i]
}
void main(int n) {
    int * A;
    // A = malloc(n);
    __cost = find(A,n); // NOTE: Weirdly assinging __cost to return of find!!!
}
