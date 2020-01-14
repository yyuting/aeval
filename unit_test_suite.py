import os
import subprocess

pos_cmds = [
'./build/tools/equiv bench_horn/easy_01.smt2 bench_horn/easy_01.smt2 1',
'./build/tools/equiv bench_horn/easy_01.smt2 bench_horn/easy_01_eq.smt2 1',
'./build/tools/equiv bench_horn/robust_cond_01.smt2 bench_horn/robust_cond_01_eq.smt2 2',
'./build/tools/equiv bench_horn/robust_cond_01.smt2 bench_horn/robust_cond_01.smt2 1',
'./build/tools/equiv bench_horn/robust_cond_02.smt2 bench_horn/robust_cond_02_eq.smt2 2 1'
]

neg_cmds = [
'./build/tools/equiv bench_horn/easy_03.smt2 bench_horn/easy_03_neq.smt2 1',
'./build/tools/equiv bench_horn/robust_cond_01.smt2 bench_horn/robust_cond_01_eq.smt2 1',
'./build/tools/equiv bench_horn/robust_cond_02.smt2 bench_horn/robust_cond_02_eq.smt2 2'
]

non_det_cmds = [
'./build/tools/equiv bench_horn/easy_02.smt2 bench_horn/easy_02_eq.smt2 1',
'./build/tools/equiv bench_horn/easy_02.smt2 bench_horn/easy_02.smt2 1',
'./build/tools/equiv bench_horn/easy_03.smt2 bench_horn/easy_03.smt2 1'
]

for cmds in [pos_cmds, neg_cmds, non_det_cmds]:
    for cmd in cmds:
        out = subprocess.check_output(cmd, shell=True)
        out = out.decode('utf-8')
        ans = out.split('\n')[-2]
        if cmds == pos_cmds:
            success = ans == 'EQUIV!'
        elif cmds == neg_cmds:
            success = ans == 'NOT equiv!'
        else:
            success = ans == 'Program(s) non-deterministic, but is possible to get same output.'
        if not success:
            print(cmd)
            print(ans)
            raise
        else:
            print('succdess!')
            print(cmd)


print('success all cmd!')
