extern unsigned int __compcert_va_int32(void *);
extern unsigned long long __compcert_va_int64(void *);
extern double __compcert_va_float64(void *);
extern void *__compcert_va_composite(void *, unsigned long long);
extern long long __compcert_i64_dtos(double);
extern unsigned long long __compcert_i64_dtou(double);
extern double __compcert_i64_stod(long long);
extern double __compcert_i64_utod(unsigned long long);
extern float __compcert_i64_stof(long long);
extern float __compcert_i64_utof(unsigned long long);
extern long long __compcert_i64_sdiv(long long, long long);
extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);
extern long long __compcert_i64_smod(long long, long long);
extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);
extern long long __compcert_i64_shl(long long, int);
extern unsigned long long __compcert_i64_shr(unsigned long long, int);
extern long long __compcert_i64_sar(long long, int);
extern long long __compcert_i64_smulh(long long, long long);
extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);
extern void __builtin_debug(int, ...);
extern int printf(signed char *, ...);
int foo(void);
int bar(void);
int sum(int, int);
int main(int, signed char **);
signed char const __stringlit_2[5] = "bar\012";

signed char const __stringlit_1[5] = "foo\012";

int foo(void)
{
  register int $67;
  $67 = printf(__stringlit_1);
  return $67;
}

int bar(void)
{
  register int $67;
  $67 = printf(__stringlit_2);
  return $67;
}

int sum(int a, int b)
{
  return a + b;
}

int main(int argc, signed char **argv)
{
  register int $69;
  register int $68;
  register int $67;
  $67 = foo();
  $68 = bar();
  $69 = sum($67, $68);
  return $69;
  return 0;
}


