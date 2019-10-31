int __cost = 0;


void heap_pop(int *aHeap, int pN)
{
  //__VERIFIER_assume(pN > 1);
  int pi = 1;
  int pIter = pN + 1;
  while(pIter>1)
  {
    __cost++;
    int pMin = pi;
    if(2*pi<=pN && aHeap[2*pi]<aHeap[pMin])		
      pMin = 2 * pi;
    if(2*pi+1<=pN && aHeap[2*pi+1]<aHeap[pMin])
      pMin = 2 * pi + 1;
    if(pMin!=pi)
    {
      aHeap[pi] = aHeap[pi] + aHeap[pMin];
      aHeap[pMin] = aHeap[pi] - aHeap[pMin];
      aHeap[pi] = aHeap[pi] - aHeap[pMin];		
    }
    pIter = pIter / 2;
  }	
}

void heap_insert(int *aHeap, int pX, int pN)
{
  //__VERIFIER_assume(pN > 1);
  pN = pN + 1;
  aHeap[pN] = pX;
  while(pN > 1)
  {
    __cost++;
    if(aHeap[pN] < aHeap[pN/2])
    {
      aHeap[pN] = aHeap[pN] + aHeap[pN/2];
      aHeap[pN/2] = aHeap[pN] - aHeap[pN/2];
      aHeap[pN] = aHeap[pN] - aHeap[pN/2];
    }
    pN = pN / 2;
  }	
}

void heap_sort(int *aHeap, int pN)
{
  //__VERIFIER_assume(pN > 1);
  int pi = 1;
  while(pi<pN)
  {
    heap_insert(aHeap, pN, pi);
    pi = pi + 1;
  }	
  while(pN>1)
  {
    heap_pop(aHeap, pN);
    pN = pN - 1;
  }
}

void main(int N){
  int *array = (int*)malloc(N*sizeof(int));
  heap_sort(array, N);
}
