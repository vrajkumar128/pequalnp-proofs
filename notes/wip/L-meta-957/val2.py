import sys, time
sys.path.insert(0, '.')
from cegis957 import *
n = 13
tabs = line_tables()
mode = sys.argv[1]
if mode == 'mono39':
    # minterm rows suffice for monotone: units + line complements + 0
    rows = {0} | {1 << i for i in range(n)} | {((1 << n) - 1) & ~sum(1 << i for i in L) for L in LINES}
    r = cegis(n, tabs, LINES, 39, maxnot=0, time_limit=float(sys.argv[2]), init_rows=rows,
              sb_distinct=(sys.argv[3] == '1'), sb_order=(sys.argv[4] == '1'))
    print('RESULT', r[0], r[3]); 
    if r[1]: print(r[1])
