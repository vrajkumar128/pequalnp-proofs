"""SAT backends and UNSAT certificates (DRAT proofs checked by drat-trim)."""
import hashlib
import os
import shutil
import subprocess
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def tool_path(name):
    """Solver binaries: $CIRCUIT_SYNTH_<NAME>, then third_party/bin/<name>, then PATH."""
    env = os.environ.get('CIRCUIT_SYNTH_' + name.upper().replace('-', '_'))
    if env:
        return env
    p = os.path.join(ROOT, 'third_party', 'bin', name)
    if os.path.exists(p):
        return p
    p = shutil.which(name)
    if p:
        return p
    raise FileNotFoundError('%s not found (set CIRCUIT_SYNTH_%s or run scripts/build_tools.sh)'
                            % (name, name.upper().replace('-', '_')))


def tmp_dir():
    """Scratch space for uncertified external runs: $CIRCUIT_SYNTH_TMP or build/tmp."""
    d = os.environ.get('CIRCUIT_SYNTH_TMP') or os.path.join(ROOT, 'build', 'tmp')
    os.makedirs(d, exist_ok=True)
    return d


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def have_pysat():
    try:
        import pysat.solvers  # noqa: F401
        return True
    except ImportError:
        return False


class Result:
    def __init__(self, status, model=None, seconds=0.0, info=None):
        self.status = status          # 'SAT', 'UNSAT' or 'UNKNOWN'
        self.model = model            # set of true variables
        self.seconds = seconds
        self.info = info or {}


def solve_pysat(cnf, name='cadical195'):
    from pysat.solvers import Solver
    t0 = time.time()
    with Solver(name=name, bootstrap_with=cnf.clauses) as sv:
        r = sv.solve()
        m = sv.get_model() if r else None
    return Result('SAT' if r else 'UNSAT', set(l for l in m if l > 0) if m else None,
                  time.time() - t0, {'solver': 'pysat-' + name})


def _parse(out):
    status, model = 'UNKNOWN', set()
    for line in out.splitlines():
        if line.startswith('s '):
            st = line[2:].strip()
            status = {'SATISFIABLE': 'SAT', 'UNSATISFIABLE': 'UNSAT'}.get(st, 'UNKNOWN')
        elif line.startswith('v '):
            for x in line[2:].split():
                x = int(x)
                if x > 0:
                    model.add(x)
    return status, model


def solve_external(cnf, solver='kissat', workdir=None, proof=False, timeout=None, tag='inst',
                   comments=()):
    """Write the CNF, run kissat/cadical (with a text DRAT proof if proof=True), and on UNSAT
    with a proof run drat-trim. Returns Result with info: cnf path/sha256, proof path/sha256,
    drat-trim verdict. Files are kept in workdir when given (certificate bundle)."""
    own = workdir is None
    wd = workdir or tempfile.mkdtemp(prefix='csynth_', dir=tmp_dir())
    os.makedirs(wd, exist_ok=True)
    cnf_path = os.path.join(wd, tag + '.cnf')
    with open(cnf_path, 'w') as f:
        f.write(cnf.dimacs(comments))
    proof_path = os.path.join(wd, tag + '.drat') if proof else None
    exe = tool_path(solver)
    if solver == 'kissat':
        cmd = [exe, '-q', '--no-binary', cnf_path] + ([proof_path] if proof else [])
    else:
        cmd = [exe, '-q', '--no-binary', cnf_path] + ([proof_path] if proof else [])
    if timeout:
        cmd = ['timeout', str(int(timeout))] + cmd
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    dt = time.time() - t0
    status, model = _parse(r.stdout)
    info = {'solver': solver, 'cnf': cnf_path, 'cnf_sha256': sha256_file(cnf_path),
            'vars': cnf.nv, 'clauses': len(cnf.clauses), 'solve_seconds': round(dt, 3)}
    if status == 'UNSAT' and proof:
        info['proof'] = proof_path
        info['proof_sha256'] = sha256_file(proof_path)
        info['proof_bytes'] = os.path.getsize(proof_path)
        info.update(check_drat(cnf_path, proof_path, timeout=timeout))
    if own:
        shutil.rmtree(wd, ignore_errors=True)
        info.pop('cnf', None)
        info.pop('proof', None)
    return Result(status, model if status == 'SAT' else None, dt, info)


def check_drat(cnf_path, proof_path, timeout=None):
    exe = tool_path('drat-trim')
    cmd = [exe, cnf_path, proof_path]
    if timeout:
        cmd += ['-t', str(int(timeout))]
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    dt = time.time() - t0
    verified = any(line.strip() == 's VERIFIED' for line in r.stdout.splitlines())
    return {'drat_trim': 's VERIFIED' if verified else 'NOT VERIFIED',
            'drat_seconds': round(dt, 3), 'drat_verified': verified}


def solve(cnf, backend='auto', **kw):
    if backend == 'auto':
        backend = 'pysat' if have_pysat() else 'kissat'
    if backend == 'pysat':
        return solve_pysat(cnf)
    return solve_external(cnf, solver=backend, **kw)
