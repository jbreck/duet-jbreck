int __cost;
int find(int * A, int n) { return findAux(A,0,n,0); }
int findAux(int * A, int i, int n, int sum) {
    __cost++;
    if (i >= n) { if (sum == 0) { return 1;} else {return 0;} }
    int first = findAux(A,i+1,n,sum);
    if (first > 0) return first;
    return findAux(A,i+1,n,sum + A[i]);
}
void main(int n) {
    int * A;
    // A = malloc(n);
    find(A,n);
}
