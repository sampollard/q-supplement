/* compile with
 * ccomp -dclight ub.c
 */
#include <stdio.h>
int foo(void)
{
	return printf("foo\n");
}

int bar(void)
{
	return printf("bar\n");
}

int sum(int a, int b)
{
	return a + b;
}

int main(int argc, char *argv[])
{
	return sum(foo(), bar());
}
