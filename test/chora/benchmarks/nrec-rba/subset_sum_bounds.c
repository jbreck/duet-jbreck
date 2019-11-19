// Copied from "chora/benchmarks/other/subsetsub_size_overview.c"
#define bool int
#define false 0
#define true 1
int nTicks;
int __cost;
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
    nTicks = 0;
    int * A;
    if (n >= 0) {
        //__cost = subsetSumSize(A,n); // return value
        subsetSumSize(A,n); __cost = nTicks; // cost
    }
    
}
