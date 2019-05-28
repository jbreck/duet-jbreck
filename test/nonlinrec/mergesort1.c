int __cost;
void MergeSort(int * A, int * B, int n){
  CopyArray(A, 0, n, B);
  SplitMerge(B, 0, n, A);
}
void SplitMerge(int * B, int iBegin, int iEnd, int * A){
  __cost += 0;
  //__VERIFIER_assume(iBegin >= 0);
  __VERIFIER_assume(iEnd >= iBegin);
  // Note: this needs a fix to handle the ==2 case
  if (iEnd - iBegin >= 0 && iEnd - iBegin <= 2) return;
  int iMiddle = (iEnd + iBegin) / 2;
  SplitMerge(A, iBegin, iMiddle, B);
  SplitMerge(A, iMiddle, iEnd, B);
  Merge(B, iBegin, iMiddle, iEnd, A);
}
void Merge(int * A, int iBegin, int iMiddle, int iEnd, int * B){
  int i = iBegin, j = iMiddle;
  for(int k = iBegin; k != iEnd; k ++) {
    __cost++;
    if (i < iMiddle && (j >= iEnd || A[i] <= A[j])) {
      B[k] = A[i];
      i = i + 1;
    } else {
      B[k] = A[j];
      j = j + 1;
    }
  }
}
void CopyArray(int * A, int iBegin, int iEnd, int * B){
  for(int k = iBegin; k < iEnd; k ++) { B[k] = A[k]; }
}
void main(int n) {
  int * myarray;
  int * temparray;
  MergeSort(myarray, temparray, n);
}
