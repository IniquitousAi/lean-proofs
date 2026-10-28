"""Daniel's stamp rule (stamp/StampRule.lean, his pick 2026-10-28 01:37): Lean accepts the proofs, they rest on no axiom beyond
propext, and a forged stamp for the planted claim is refused. Run: python -m pytest -q scripts/test_stamp_rule.py"""
import pathlib, re, subprocess, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
RULE = ROOT / 'stamp' / 'StampRule.lean'


def lean(path):
    r = subprocess.run(['lean', str(path)], cwd=ROOT, capture_output=True, text=True, timeout=300)
    return r.returncode, r.stdout + r.stderr


def test_the_rule_is_proven_on_standard_axioms_only():
    code, out = lean(RULE)
    assert code == 0, out
    code_only = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', RULE.read_text(encoding='utf-8'), flags=re.S))
    assert not re.search(r'\b(sorry|admit|native_decide)\b', code_only)
    for name in ('stamp_means_proven', 'no_stamp_without_pass', 'planted_is_refused', 'honest_is_stamped'):
        line = next(l for l in out.splitlines() if f"'{name}'" in l)
        assert 'does not depend on any axioms' in line or line.endswith('[propext]'), line


def test_a_forged_stamp_for_the_planted_claim_is_refused():
    with tempfile.TemporaryDirectory() as d:
        forged = pathlib.Path(d) / 'Forged.lean'
        forged.write_text(RULE.read_text(encoding='utf-8') + '\ndef forged : Stamp := ⟨planted, by decide⟩\n', encoding='utf-8')
        code, out = lean(forged)
    assert code != 0 and 'passes planted = true' in out and 'is false' in out, out
