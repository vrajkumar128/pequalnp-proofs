"""Job runner for kloc5.py: each job 'K:MODE' runs under `timeout LIMIT`; parallel workers read
from DIR/NWORK before each dispatch. Logs: DIR/logs/K_MODE.log; summary lines in DIR/run.log.

usage: run_kloc.py DIR LIMIT_SECONDS JOB [JOB ...]     e.g. 0-1-2-3-7:0,0
"""
import os
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(HERE, '..', '..', 'tool-circuit-synth', 'venv', 'bin', 'python')


def job(d, limit, spec):
    K, mode = spec.split(':')
    log = os.path.join(d, 'logs', '%s_%s.log' % (K, mode.replace(',', '-')))
    t0 = time.time()
    with open(log, 'w') as f:
        rc = subprocess.run(['timeout', str(limit), PY, os.path.join(HERE, 'kloc5.py'), K, mode],
                            stdout=f, stderr=subprocess.STDOUT).returncode
    dt = time.time() - t0
    res = [l for l in open(log) if l.startswith('RESULT')]
    if rc == 124:
        with open(log, 'a') as f:
            f.write('no answer within the %d s cap (killed by timeout, exit 124)\n' % limit)
    msg = res[0].strip()[:160] if res else ('TIMEOUT after %.0f s' % dt if rc == 124 else 'rc %d' % rc)
    with open(os.path.join(d, 'run.log'), 'a') as f:
        f.write('%s %s %s: %s (%.0f s)\n' % (time.strftime('%H:%M:%S'), K, mode, msg, dt))


def main():
    d, limit, jobs = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    os.makedirs(os.path.join(d, 'logs'), exist_ok=True)
    running = []
    while jobs or running:
        running = [t for t in running if t.is_alive()]
        try:
            nw = int(open(os.path.join(d, 'NWORK')).read().strip())
        except Exception:
            nw = 1
        if jobs and len(running) < nw:
            spec = jobs.pop(0)
            with open(os.path.join(d, 'run.log'), 'a') as f:
                f.write('%s start %s (cap %d s)\n' % (time.strftime('%H:%M:%S'), spec, limit))
            t = threading.Thread(target=job, args=(d, limit, spec))
            t.start()
            running.append(t)
            continue
        time.sleep(2)


if __name__ == '__main__':
    main()
