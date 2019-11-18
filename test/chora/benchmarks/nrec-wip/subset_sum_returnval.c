// Copied from "chora/benchmarks/other/subsetsub_size_overview.c"
#define bool int
#define false 0
#define true 1
int __cost;
int nTicks;
bool found;
int subsetSumSize(int * A, int n) { found = false; return subsetSumSizeAux(A,0,n,0); }
int subsetSumSizeAux(int * A, int i, int n, int sum) {
    nTicks++;
    if (i >= n) {
        if (sum == 0) { found = true; }
        return 0;
    }
    int size = subsetSumSizeAux(A,i+1,n,sum + A[i]); // add A[i]
    if (found) return size + 1;
    size = subsetSumSizeAux(A,i+1,n,sum); // skip A[i]
    return size;
}
void main(int n) {
    int * A;
    //if (n >= 0) {
        __cost = subsetSumSize(A,n);
    //}
}
