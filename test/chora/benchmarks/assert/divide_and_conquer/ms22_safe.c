#ifdef TRYME
#include "stdio.h"
#include "stdlib.h"
#endif

int cost = 0;

void insertion_sort(int * X, int lo, int hi);
void merge_sort(int * A, int * B, int len);
void split_merge(int * B, int lo, int hi, int * A);
void copy_array(int * A, int lo, int hi, int * B);

void insertion_sort(int * X, int lo, int hi) {
  //int lo = iBegin;
  //printf(" iBegin=%d iLength=%d\n", iBegin, iLength);
  //printf(" Insertion step: (Xb) "); for(int q = iBegin; q < iBegin+iLength; q++) { printf("%d%c",X[q],q==iBegin+iLength-1?'\n':' '); }
  for(int sorted = 1; sorted < hi-lo; sorted++) {
    for(int pos = sorted; pos > 0; pos--) {
      //cost+=2;
      cost++;
      if (X[lo+pos-1] < X[lo+pos]) { /*printf("Skip\n");*/ break; }
      //printf("Swap X[%d]=%d for X[%d]=%d\n", pos-1, X[pos-1],pos,X[pos]);
      int tmp = X[lo+pos]; X[lo+pos] = X[lo+pos-1]; X[lo+pos-1] = tmp; 
    }
  }
  //printf(" Insertion step: (Xa) "); for(int q = iBegin; q < iBegin+iLength; q++) { printf("%d%c",X[q],q==iBegin+iLength-1?'\n':' '); }
}
//void insertion_sort(int * X, int iBegin, int iLength) {
//  //printf(" iBegin=%d iLength=%d\n", iBegin, iLength);
//  //printf(" Insertion step: (Xb) "); for(int q = iBegin; q < iBegin+iLength; q++) { printf("%d%c",X[q],q==iBegin+iLength-1?'\n':' '); }
//  for(int sorted = 1+iBegin; sorted < iBegin+iLength; sorted++) {
//    for(int pos = sorted; pos > iBegin; pos--) {
//      //cost+=2;
//      cost++;
//      if (X[pos-1] < X[pos]) { /*printf("Skip\n");*/ break; }
//      //printf("Swap X[%d]=%d for X[%d]=%d\n", pos-1, X[pos-1],pos,X[pos]);
//      int tmp = X[pos]; X[pos] = X[pos-1]; X[pos-1] = tmp; 
//    }
//  }
//  //printf(" Insertion step: (Xa) "); for(int q = iBegin; q < iBegin+iLength; q++) { printf("%d%c",X[q],q==iBegin+iLength-1?'\n':' '); }
//}
void merge_sort(int * A, int * B, int len) {
  if (len <= 1) return;
  copy_array(A, 0, len, B);
  split_merge(B, 0, len, A);
}
void split_merge(int * B, int lo, int hi, int * A) {
  //int half_dist = (hi-lo) / 2;
  //int iBegin = lo;
  //int half = half_dist;
  //int iLength = (hi - lo);
  //__VERIFIER_assume(iLength >= 2); // don't need yet
  //if (iLength == 2 || iLength == 3) {
  //  cost += 3;
  //  return;
  //}
  int mid = lo + ((hi - lo) / 2);

  //if (iLength == 2 || iLength == 3) {
  if (hi-lo == 2 || hi-lo == 3) {
    //cost += 3;
    copy_array(B, lo, hi, A);
    insertion_sort(A, lo, hi);
    return;
  }
  split_merge(A, lo, mid, B);
  split_merge(A, mid, hi, B);

  // Perform the merge
  //for(int i = 0; i < iLength; i ++) {
  //    cost ++;
  //}
  //printf(" Merge step: (B) "); for(int q = 0; q < iLength; q++) { printf("%d%c",B[q],q==iLength-1?'\n':' '); }
  int i = lo;
  int j = mid;
  for(int k = lo; k < hi; k ++) {
    //cost+=2;
    cost++;
    if (i < mid && (j >= hi || B[i] <= B[j])) {
      A[k] = B[i];
      i = i + 1;
    } else {
      A[k] = B[j];
      j = j + 1;
    }
  }
  //printf(" Merge step: (A) "); for(int q = 0; q < iLength; q++) { printf("%d%c",B[q],q==iLength-1?'\n':' '); }
  //merge(B,iBegin,iLength,A,half);
  //cost += iLength;
}
//void merge(int * B, int iBegin, int iLength, int *A, int half) {
//  __VERIFIER_assume(iLength >= 0);
//  int i = iBegin;
//  int j = iBegin+half;
//  for(int k = iBegin; k < iBegin + iLength; k ++) {
//    //cost+=2;
//    cost++;
//    if (i < iBegin+half && (j >= iBegin + iLength || B[i] <= B[j])) {
//      A[k] = B[i];
//      i = i + 1;
//    } else {
//      A[k] = B[j];
//      j = j + 1;
//    }
//  }
//}
void copy_array(int * A, int lo, int hi, int * B) {
  for(int k = lo; k < hi; k++) { B[k] = A[k]; }
}

#ifdef TRYME

// The following is the entrypoint of the executable
int main(int argc, char ** argv) {
  int iLength = argc - 1;
  int * myArray = (int*)malloc(iLength*sizeof(int));
  int * tempArray = (int*)malloc(iLength*sizeof(int));
  if (iLength <= 0) { 
    printf("Usage: %s <list of integers>\n",argv[0]);
    printf("  Sort some integers.\n");
    return 0; 
  }
  if (myArray == 0 || tempArray == 0) return -1;
  for(int i = 0; i < iLength; i++) {
    myArray[i] = atoi(argv[i+1]);
  }
  merge_sort(myArray, tempArray, iLength);
  for(int i = 0; i < iLength; i++) {
    printf("%d%c",myArray[i],i==iLength-1?'\n':' ');
  }
}

#else

int lg_n_helper(int n) {
  int r = 0;
  for(int i = 1; i < n; i *= 2) {
    r ++;
  }
  return r;
}

// The following is the entrypoint of the analyzed program
void main(int iLength, int * myArray, int * tempArray) {
  __VERIFIER_assume(iLength >= 4);

  merge_sort(myArray, tempArray, iLength);

  int logLength = lg_n_helper(iLength);
  __VERIFIER_assert(cost < 3*(iLength + iLength*logLength));
  //__VERIFIER_assert(cost < 4*iLength + 4*iLength*logLength);
  //__VERIFIER_assert(cost < 4*(iLength + iLength*logLength));
  //if (__VERIFIER_nondet_int()) {
  //  __VERIFIER_assert(0);
  //} else {
  //  __VERIFIER_assert(cost <= 10);
  //}
}

#endif
