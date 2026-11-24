"""Results table for order3/README.md from run.log and sweep/sweep.log (replaces RESULTS_TABLE)."""
import re
import sys

D = sys.argv[1]
rows = []
for line in open(D + '/run.log'):
    m = re.match(r'(\S+) (\S+) (\S+): (.*) \((\d+) s\)$', line.strip())
    if m:
        t, K, mode, msg, dt = m.groups()
        if msg.startswith('RESULT'):
            v = 'UNSAT' if '-> UNSAT' in msg else ('SAT' if '-> SAT' in msg else msg)
        elif msg.startswith('TIMEOUT'):
            v = 'no answer (cap 900 s)'
        else:
            v = 'stopped by hand (%s)' % msg
        rows.append((K, 'flag ' + mode, 'all', v, dt))
for line in open(D + '/sweep/sweep.log'):
    m = re.match(r'(\S+) (\S+) flag (\S+) notpos (\S+): (.*) rc=(-?\d+) (\d+)s$', line.strip())
    if m:
        t, K, fl, p, msg, rc, dt = m.groups()
        v = 'UNSAT' if '-> UNSAT' in msg else ('no answer (cap 300 s)' if rc == '124' else 'rc %s' % rc)
        rows.append((K, 'flag ' + fl, 'NOT at %s' % p if p != 'none' else 'no NOT', v, dt))
out = ['| K | case | NOT position | result | seconds |', '|---|---|---|---|---|']
for r in rows:
    out.append('| (%s) | %s | %s | %s | %s |' % (r[0].replace('-', ','), r[1], r[2], r[3], r[4]))
txt = open(D + '/README.md').read()
open(D + '/README.md', 'w').write(txt.replace('RESULTS_TABLE', '\n'.join(out)))
print('\n'.join(out))
