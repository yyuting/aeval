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

  equivCheck(string(argv[1]), string(argv[2]), mode);

  return 0;
}
