/* Licensed under the GPLv2 */

int main(int argc, char **argv)
{
	static char array[1024 * 100];
	char ND = __VERIFIER_nondet_char();
	unsigned int i;

	for (i = 0; i < sizeof(array); i++)
		array[i] = __VERIFIER_nondet_char();

	for (i = 0; i < sizeof(array); i++)
		if (array[i] == ND)
			return i;

ERROR: __VERIFIER_error();
	return 0;
}
