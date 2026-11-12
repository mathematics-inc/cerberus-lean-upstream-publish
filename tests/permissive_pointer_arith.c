/* Selected by the focused pointer-arithmetic differential check. */
#if CASE == 7
int y = 2, x = 1;
#endif
int main(void)
{
#if CASE == 0
	/* Linux's end cursor temporarily precedes a standalone list head. */
	struct link { void *next, *prev; } head;
	char *outside = (char *)&head - 8;
	return outside + 8 != (char *)&head;
#elif CASE == 1
	/* Concrete pointers from different allocations may be subtracted. */
	char a, b;
	long distance = &a - &b;
	return distance == 0 || distance + (&b - &a) != 0;
#elif CASE == 2
	/* Permissive subtraction still rejects null pointers. */
	int *p = 0;
	return p - p;
#elif CASE == 3
	/* Permissive arithmetic does not permit an out-of-bounds read. */
	int value = 7;
	char *outside = (char *)&value - 8;
	return *outside;
#elif CASE == 4
	/* An exposed address round trip still permits the temporary shift. */
	int value = 7;
	unsigned long address = (unsigned long)&value;
	char *p = (char *)address;
	char *outside = p - 8;
	return outside + 8 != p;
#elif CASE == 5
	/* Neither mode permits arithmetic on null pointers. */
	char *p = 0;
	return p + 1 == p;
#elif CASE == 6
	/* Element scaling and sign must survive permissive subtraction. */
	int array[3];
	return &array[2] - &array[0] != 2 || &array[0] - &array[2] != -2;
#elif CASE == 7
	/* Adjacent exposed allocations create two provenance candidates. */
	unsigned long i = (unsigned long)(&x + 1), j = (unsigned long)&y;
	if (i != j) return 2; /* Fail if the model did not create adjacency. */
	int *p = (int *)i;
	int *q = p + 1;
	/* Moving toward y must not discard the candidate for x. */
	return *(q - 2) != 1;
#else
#error unknown pointer-arithmetic case
#endif
}
