int __cost = 0;

void bubblesort(int *aA, int pn)
{
        __VERIFIER_assume(pn>=0);
	int pi = 1;
	while(pi<=pn)
	{
	bubblesort_iteration(aA, pn);		
	pi = pi+1;
	}
}

void bubblesort_iteration(int *aA, int pn)
{
        __VERIFIER_assume(pn>=0);
	int pi = 1;
	while(pi<=pn)
	{
	  bubble(aA, pi);
	  pi = pi+1;
	}
}

void bubble(int *aA, int pi)
{
	__VERIFIER_assume(pi>=0);
        __cost++;
	if(pi>1)
	{
		if(aA[pi]<aA[pi-1])
		{
			aA[pi] = aA[pi] + aA[pi-1];
			aA[pi-1] = aA[pi] - aA[pi-1];
			aA[pi] = aA[pi] - aA[pi-1];
		}
	}
}

void main(int N) {
  int *array = (int*)malloc(N*sizeof(int));
  bubblesort(array, N);
}
