int __cost;
void MergeSort(int * A, int * B, int n){
  CopyArray(A, 0, n, B);
  SplitMerge(B, 0, n, A);
}
void SplitMerge(int * B, int iBegin, int iLength, int * A){
  int iEnd = iBegin + iLength;
  __VERIFIER_assume(iBegin >= 0);
  __VERIFIER_assume(iEnd >= 0);
  __VERIFIER_assume(iEnd >= iBegin);
  __cost += 0;
  // Note: this needs a fix to handle the ==2 case
  if (iEnd - iBegin >= 0 && iEnd - iBegin <= 2) return;
  int iMiddle = (iEnd + iBegin) / 2;
  int iLength1 = iMiddle - iBegin;
  SplitMerge(A, iBegin, iLength1, B);
  int iLength2 = iEnd - iMiddle;
  SplitMerge(A, iMiddle, iLength2, B);
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
