"""Re-runs every claim in RERUN-RECEIPT.md on this machine and prints one PASS/FAIL line per claim, in the receipt's order.

Started by RERUN.cmd (Windows) or RERUN.sh (Mac, Linux). Needs elan (it installs the pinned Lean by itself), git, bash and
Python 3.11 or newer. Nothing is sent anywhere: the only network use is elan/lake fetching Lean and Mathlib's prebuilt
files, pip fetching pytest when it is missing, and git fetching the answer bank when it is not next to this folder.

    python scripts/rerun.py              every step
    python scripts/rerun.py --no-lean    skip the long Lean steps (about 20 minutes); they then read SKIPPED, not PASS
    python scripts/rerun.py --only stamps     re-run one claim (its id from RERUN-RECEIPT.md)
"""
from __future__ import annotations

import hashlib, os, pathlib, re, shutil, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
RECEIPT = ROOT / 'RERUN-RECEIPT.md'
STAMPS = ROOT / 'stamps'
WORK = ROOT / '.rerun'
ANSWER_BANK_URL = 'https://github.com/IniquitousAi/answer-bank.git'
CREDIT = 'Humanities Helping Hands engine, built by Daniel Steadham'
PINNED = 'leanprover/lean4:v4.35.0'
STANDARD = {'propext', 'Quot.sound', 'Classical.choice'}
ANCHOR_REASON = ('the 2026-10-22 drive manifest was lost; a search of 9,096 files on the key and the full Desktop did not find it '
                 '(the attempt is logged in witness/recovery_attempts.jsonl). Kept in on purpose: we aim to be perfect and are not yet.')

# (OpenTimestamps file format: a fixed magic, version 1, then the file's hash op and digest; attestations carry an 8-byte tag)
OTS_MAGIC = b'\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94'
OTS_SHA256 = 0x08
BITCOIN_TAG = bytes.fromhex('0588960d73d71901')


def receipt_ids(path=RECEIPT):
    ids = re.findall(r'^\| ([a-z0-9-]+) \|', path.read_text(encoding='utf-8'), re.M) if path.exists() else []
    return [i for i in ids if i != 'id' and set(i) != {'-'}]   # (not the header row or its --- line)


def run(cmd, cwd=ROOT, timeout=3600):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except FileNotFoundError: return 127, f'{cmd[0]} not found'
    except subprocess.TimeoutExpired: return 124, f'timed out after {timeout} s'


def bash():
    for b in (os.environ.get('RERUN_BASH'), r'C:\Program Files\Git\bin\bash.exe', shutil.which('bash')):
        if b and pathlib.Path(b).exists() and 'System32' not in b: return b   # (System32\bash.exe is WSL, a different machine)
    return 'bash'


# ---- the steps, one per receipt claim
def toolchain(ctx):
    pinned = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
    if pinned != PINNED: return False, f'lean-toolchain says {pinned}, the receipt says {PINNED}'
    if not shutil.which('lake'): return False, 'lake not found: install elan (https://github.com/leanprover/elan), open a new window, run RERUN again'
    code, out = run(['lake', 'env', 'lean', '--version'], timeout=1800)
    ver = PINNED.split(':v')[1]
    return code == 0 and f'version {ver}' in out, (out.strip().splitlines() or ['no output'])[-1][:160]


def check_sh(ctx):
    """check.sh runs source audit, build, VerifyAll and leanchecker in one go; the four claims read its output."""
    if 'check' not in ctx:
        if ctx['no_lean']: ctx['check'] = None
        else:
            t0 = time.time(); code, out = run([bash(), 'check.sh'], timeout=4 * 3600)
            ctx['check'] = (code, out, round(time.time() - t0))
    return ctx['check']


def _lean_step(ctx, reached, detail):
    c = check_sh(ctx)
    if c is None: return None, 'skipped (--no-lean)'
    code, out, secs = c
    return reached(out, code), detail(out, code, secs)


def source_audit(ctx):
    return _lean_step(ctx, lambda o, c: '3/5 lake build' in o, lambda o, c, s: (re.findall(r'.*\b0 matches.*', o) or ['the audit stopped check.sh: see AUDIT.log'])[0].strip()[:160])


def build(ctx):
    return _lean_step(ctx, lambda o, c: '4/5 lake env lean VerifyAll.lean' in o,
                      lambda o, c, s: (re.findall(r'Build completed[^\n]*', o) or ['lake build did not finish: see AUDIT.log'])[-1].strip()[:160])


def headline(ctx):
    def ok(o, c):
        m = re.search(r'VerifyAll: .*axioms outside propext, Quot.sound, Classical.choice: (\S+)', o)
        return bool(m) and m.group(1) == 'none' and '5/5 leanchecker' in o
    return _lean_step(ctx, ok, lambda o, c, s: (re.findall(r'VerifyAll: [^\n]*', o) or ['VerifyAll did not report: see AUDIT.log'])[-1][:200])


def root(ctx):
    def axioms(o):
        m = re.search(r"'DanielRootTheorem' depends on axioms: \[([^\]]*)\]", o)
        return None if not m else {a.strip() for a in m.group(1).split(',') if a.strip()}
    return _lean_step(ctx, lambda o, c: axioms(o) is not None and axioms(o) <= STANDARD,
                      lambda o, c, s: f"DanielRootTheorem rests on: {', '.join(sorted(axioms(o)))}" if axioms(o) is not None else 'DanielRootTheorem was not restated')


def kernel(ctx):
    def ok(o, c): return c == 0 and re.search(r'leanchecker: all \d+ LeanProofs modules \([^)]*LeanProofs\.Root', o) is not None
    return _lean_step(ctx, ok, lambda o, c, s: ((re.findall(r'leanchecker: all \d+ LeanProofs modules', o) or ['leanchecker did not finish'])[-1]
                                                 + f'; check.sh exit {c}, {s} s'))


def answer_bank(ctx):
    bank = next((p for p in (ROOT.parent / 'answer-bank', WORK / 'answer-bank') if (p / 'tests').is_dir()), None)
    if bank is None:
        WORK.mkdir(exist_ok=True)
        code, out = run(['git', 'clone', '--quiet', ANSWER_BANK_URL, str(WORK / 'answer-bank')], timeout=600)
        if code: return False, f'could not fetch the answer bank: {out.strip()[:140]}'
        bank = WORK / 'answer-bank'
    py = sys.executable
    if run([py, '-m', 'pytest', '--version'], timeout=60)[0]:   # (no pytest here: a private one in .rerun, never the machine's own Python)
        venv = WORK / 'venv'
        if not venv.exists(): run([py, '-m', 'venv', str(venv)], timeout=300)
        py = str(venv / ('Scripts/python.exe' if os.name == 'nt' else 'bin/python'))
        code, out = run([py, '-m', 'pip', 'install', '--quiet', 'pytest>=8'], timeout=600)
        if code: return False, f'could not install pytest: {out.strip()[-140:]}'
    commit = run(['git', '-C', str(bank), 'rev-parse', '--short', 'HEAD'], timeout=30)[1].strip()
    # (its own addopts already says -q; a second -q hides the "N passed" line)
    code, out = run([py, '-m', 'pytest', '-q', '-o', 'addopts=', '-p', 'no:cacheprovider'], cwd=bank, timeout=1800)
    m = re.search(r'(\d+) passed[^\n]*', out)
    return code == 0 and bool(m), f"{m.group(0).strip() if m else 'no tests ran'} (answer-bank {commit or 'unknown commit'})"


def ots_digest(data):
    """(sha256 hex digest the proof commits to, in Bitcoin yet) for a .ots file, or (None, why) when it is not one."""
    if not data.startswith(OTS_MAGIC): return None, 'not an OpenTimestamps proof'
    rest = data[len(OTS_MAGIC):]
    if rest[:1] != b'\x01': return None, f'unknown proof version {rest[:1].hex()}'
    if rest[1] != OTS_SHA256: return None, 'the proof does not use SHA-256'
    return rest[2:34].hex(), BITCOIN_TAG in rest


def stamp_rows(stamps=STAMPS, originals=ROOT.parent / '_proofs'):
    """One (name, ok, detail) per proof. The proof must name a fingerprint STAMPS.md logged for it; where the stamped copy is on
    this machine, the copy must still have that fingerprint (a copy replaced after stamping is not covered by this proof)."""
    table = (stamps / 'STAMPS.md').read_text(encoding='utf-8') if (stamps / 'STAMPS.md').exists() else ''
    logged = {}
    for what, sha, proof in re.findall(r'^\| \S+ \| (\S+) \| ([0-9a-f]{64}) \| (\S+) \|', table, re.M): logged.setdefault(proof, []).append((what, sha))
    rows = []
    for ots in sorted(p for p in stamps.rglob('*.ots')):
        rel = ots.relative_to(stamps).as_posix()
        digest, chain = ots_digest(ots.read_bytes())
        if digest is None: rows.append((rel, False, chain)); continue
        rows_for = logged.get(rel) or [r for rs in logged.values() for r in rs if r[1] == digest]   # (a replaced proof is kept as <file>.<fingerprint>.ots)
        if not rows_for: rows.append((rel, False, 'no fingerprint for it in STAMPS.md')); continue
        what, sha = next(((w, s) for w, s in rows_for if s == digest), (rows_for[-1][0], None))
        if sha is None: rows.append((rel, False, f'the proof names {digest[:12]}, which STAMPS.md never logged for it')); continue
        here = originals / rel[:-len('.ots')]   # (the frozen copy stamped beside its proof; private copies never leave his PC)
        here = here if here.is_file() else None
        if here is not None and hashlib.sha256(here.read_bytes()).hexdigest() != sha:
            newer = [s for w, s in rows_for if s == hashlib.sha256(here.read_bytes()).hexdigest()]
            rows.append((rel, False, f'the copy of {what} here was replaced after this proof ({digest[:12]})'
                                     + ('; the replacement was logged as stamped, but its proof file was never saved' if newer else ''))); continue
        older = rel != (logged.get(rel) and rel) and not here   # (kept as <file>.<fingerprint>.ots after a re-stamp)
        rows.append((rel, True, f"{sha[:12]}{', file checked' if here else ', an earlier version (its copy was replaced)' if older else ', file kept private'}; "
                                # (offline, only the attestation's presence is read; tools/stamp.py --verify checks the block itself)
                                f"{'has its Bitcoin attestation' if chain else 'waiting for its Bitcoin block (pending)'}"))
    return rows


def stamps(ctx):
    rows = stamp_rows()
    ctx['stamp_rows'] = rows
    bad = [r for r in rows if not r[1]]
    return bool(rows) and not bad, f'{len(rows) - len(bad)} of {len(rows)} proofs match' + (f'; first problem: {bad[0][0]}: {bad[0][2]}' if bad else '')


def anchor_20261022_manifest(ctx):
    return False, ANCHOR_REASON


def reminder():
    """One goal reminder in the receipt footer (ORD-1027-BJ). The lines live in vibe-lab/hhh/reminders.json on his PC; a stranger
    without it gets the first line."""
    import json, random
    try: lines = json.loads((ROOT.parent / 'vibe-lab' / 'hhh' / 'reminders.json').read_text(encoding='utf-8'))['lines']
    except (OSError, ValueError, KeyError): lines = ['Check the root first. It saves the most time.']
    return random.choice(lines)


STEPS = {'toolchain': toolchain, 'source-audit': source_audit, 'build': build, 'headline': headline, 'root': root, 'kernel': kernel,
         'answer-bank': answer_bank, 'stamps': stamps, 'anchor-20261022-manifest': anchor_20261022_manifest}
KNOWN_FAIL = {'anchor-20261022-manifest'}


def main(argv=sys.argv[1:]):
    sys.stdout.reconfigure(encoding='utf-8')
    ctx = {'no_lean': '--no-lean' in argv}
    started = time.strftime('%Y-%m-%d %H:%M:%S')
    print(CREDIT)
    print(f'Re-run started {started} on {os.environ.get("COMPUTERNAME") or os.uname().nodename}')
    print('Timestamped proof ids: ' + ', '.join(f'{p.stem} {ots_digest(p.read_bytes())[0][:12]}' for p in sorted(STAMPS.rglob('*.ots')) if ots_digest(p.read_bytes())[0]))
    results = []
    only = argv[argv.index('--only') + 1:argv.index('--only') + 2] if '--only' in argv else []   # (one claim: the paranoia button)
    if only and only[0] not in STEPS: print(f'no claim {only[0]}; the claims are: {", ".join(receipt_ids())}'); return 2
    for rid in only or receipt_ids():
        t0 = time.time()
        try: ok, why = STEPS[rid](ctx)
        except Exception as ex: ok, why = False, f'the step crashed: {type(ex).__name__}: {ex}'[:200]
        word = 'SKIPPED' if ok is None else 'PASS' if ok else 'FAIL'
        results.append((rid, word, why))
        print(f'  ... {rid}: {word} ({round(time.time() - t0)} s)', flush=True)
    w = max(len(r[0]) for r in results)
    print(f'\n{CREDIT}\n')
    print(f"{'claim'.ljust(w)}  result   why")
    for rid, word, why in results: print(f'{rid.ljust(w)}  {word.ljust(7)}  {why}')
    for name, ok, why in ctx.get('stamp_rows', []): print(f"{'':{w}}  {'  PASS' if ok else '  FAIL'}     stamp {name}: {why}")
    passed = sum(r[1] == 'PASS' for r in results)
    surprise = [r[0] for r in results if r[1] == 'FAIL' and r[0] not in KNOWN_FAIL]
    print(f'\n{passed} of {len(results)} PASS. ' + (f'Unexpected FAIL: {", ".join(surprise)}.' if surprise else
          'The only FAIL is the known one, shown on purpose.' if passed < len(results) else ''))
    print(reminder())
    return 1 if surprise or any(r[1] == 'SKIPPED' for r in results) else 0


if __name__ == '__main__':
    sys.exit(main())
