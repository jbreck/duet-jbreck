int __cost = 0;

void quicksort(int *aArray, int pn)
{
	__VERIFIER_assume(pn>=1);

	int psepindex = 1;
	int pi = 2;
		while(pi<=pn)
		{
			if(aArray[pi]<=aArray[psepindex])
			{
				__cost++;
				;
				;
				;
				psepindex = psepindex + 1;
			}
			pi = pi + 1;
		}

		if(pn-psepindex>=1)
			quicksort(aArray, pn-psepindex);
		if(psepindex -1 >=1)
                	quicksort(aArray, psepindex-1);
}

void main (int N){
  int *array = (int*)malloc(N*sizeof(int));
  quicksort(array, N);
}
