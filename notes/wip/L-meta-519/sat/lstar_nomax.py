import sys
sys.path.insert(0,'.')
from lstar import *
import lstar
tests = {
  'DS': (6, [(0,1),(0,2),(0,3),(1,4),(1,5)]),
  'C5': (5, [(i,(i+1)%5) for i in range(5)]),
  'C6': (6, [(i,(i+1)%6) for i in range(6)]),
  'DS1': (7, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6)]),
  'P5': (5, [(0,1),(1,2),(2,3),(3,4)]),
}
tests['C7'] = (7, [(i,(i+1)%7) for i in range(7)])
tests['C7L1'] = cyc_leaves(7, [0])
tests['DS2'] = (8, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7)])
tests['DS3'] = (8, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(4,7)])
tests['H'] = (10, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)])
tests['G4'] = G['G4']
tests['T344'] = G['T344']
for k in sys.argv[1:]:
    n, E = tests[k]
    test_lstar(k + '(no max)', n, E, use_max=False)
