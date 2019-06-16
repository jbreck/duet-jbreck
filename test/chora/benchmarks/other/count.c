int nTicks;
int count(int * A, int n) { return countAux(A,0,n,0); }
int countAux(int * A, int i, int n, int sum) {
    nTicks++;
    if (i >= n) { if (sum == 0) { return 1;} else {return 0;} }
    int without = countAux(A,i+1,n,sum);
    int with = countAux(A,i+1,n,sum + A[i]);
    return with + without;
}
