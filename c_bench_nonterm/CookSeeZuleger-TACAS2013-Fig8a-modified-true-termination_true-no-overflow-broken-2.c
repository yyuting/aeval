extern int __VERIFIER_nondet_int(void);

int main()
{
  int x = __VERIFIER_nondet_int();
  int K = __VERIFIER_nondet_int();
  int N = 2;
  
  while (x != K)
  {
    if (x > K) x = x - N; else x = x + N;
  }
}