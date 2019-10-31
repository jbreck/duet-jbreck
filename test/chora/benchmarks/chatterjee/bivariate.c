int __cost = 0;

void bivariate(int px, int py)
{
        __VERIFIER_assume(px>=1 && py>=1);
	while(py>=1)
	{
          __cost++;
	  px = px + 1;
	  py = py / 2;
	}
	while(px>=1)
	{
          __cost++;
          px = px - 1;
	}
}

void main(int x, int y) {
  bivariate(x, y);
}
