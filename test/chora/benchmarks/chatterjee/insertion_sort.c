int __cost = 0;

void insertion_sort(int *aA, int pn)
{
	__VERIFIER_assume(pn>=0);
	int pi = 1;
	while(pi<=pn)
	{
		insert(aA, pi);
		pi = pi+1;
	}
}

void insert(int *aA, int pn)
{
	__VERIFIER_assume(pn>=0);
	while(pn>=1 && aA[pn]<aA[pn-1])
	{
                __cost++;
		aA[pn] = aA[pn] + aA[pn-1];
		aA[pn-1] = aA[pn] - aA[pn-1];
		aA[pn] = aA[pn] - aA[pn-1];
		pn = pn -1;		
	}
}

void main (int N){
  int array = (int*)malloc(N*sizeof(int));
  insertion_sort(array, N);
}
