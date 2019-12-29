#include "horn/EquivCheck.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc < 3){
    outs() << "Two input files with CHCs should be given\n";
    return 0;
  }

  int mode = 0;
  if (argc > 3) {
    mode = atoi(argv[3]);
  }

  string out_vars;
  if (argc > 4) {
    out_vars = string(argv[4]);
  } else out_vars = string("");

  equivCheck(string(argv[1]), string(argv[2]), mode, out_vars);

  return 0;
}
