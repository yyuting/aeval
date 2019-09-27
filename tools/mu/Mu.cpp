#include "ae/MuSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace ufo;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

char * getSmtFileName(int num, int argc, char ** argv)
{
  int num1 = 1;
  for (int i = 1; i < argc; i++)
  {
    int len = strlen(argv[i]);
    if (len >= 5 && strcmp(argv[i] + len - 5, ".smt2") == 0)
    {
      if (num1 == num) return argv[i];
      else num1++;
    }
  }
  return NULL;
}

int main (int argc, char ** argv)
{

  ExprFactory efac;
  EZ3 z3(efac);

  Expr s = z3_from_smtlib_file (z3, getSmtFileName(1, argc, argv));

  mu(s);

  return 0;
}
