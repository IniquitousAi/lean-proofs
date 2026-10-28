"""RERUN on answers we know. Run: python -m pytest -q scripts/test_rerun.py

The rule (ORD-1027-BH): every claim in RERUN-RECEIPT.md has a re-run step, every step has a claim, and the table prints them in
the receipt's order. The known FAIL stays in and stays a FAIL.
"""
import hashlib, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import rerun

MAGIC = rerun.OTS_MAGIC + b'\x01\x08'


def test_every_claim_has_a_rerun_step_and_every_step_a_claim():
    ids = rerun.receipt_ids()
    assert ids, 'RERUN-RECEIPT.md lists no claims'
    assert [i for i in ids if i not in rerun.STEPS] == [], 'a receipt claim has no re-run step'
    assert [s for s in rerun.STEPS if s not in ids] == [], 'a re-run step has no receipt claim'
    assert len(ids) == len(set(ids))


def test_a_claim_with_no_step_is_caught(tmp_path):
    r = tmp_path / 'R.md'
    r.write_text((rerun.RECEIPT.read_text(encoding='utf-8')) + '| brand-new-claim | nothing re-runs this |\n', encoding='utf-8')
    assert 'brand-new-claim' in rerun.receipt_ids(r) and 'brand-new-claim' not in rerun.STEPS


def test_the_known_fail_stays_in_and_says_why():
    assert 'anchor-20261022-manifest' in rerun.receipt_ids()
    ok, why = rerun.STEPS['anchor-20261022-manifest']({})
    assert ok is False and 'lost' in why and '9,096' in why


def test_every_run_credits_daniel(capsys, monkeypatch):
    monkeypatch.setattr(rerun, 'STEPS', {i: (lambda ctx: (True, 'ok')) for i in rerun.receipt_ids()})
    rerun.main([])
    out = capsys.readouterr().out
    assert out.count('Humanities Helping Hands engine, built by Daniel Steadham') >= 2 and 'Timestamped proof ids:' in out
    lines = [l.split()[0] for l in out.split('result   why')[1].splitlines() if l.strip() and not l.startswith(' ')][:len(rerun.receipt_ids())]
    assert lines == rerun.receipt_ids(), 'the table is not in the receipt order'


def test_only_reruns_one_claim(capsys, monkeypatch):   # (the paranoia button's command)
    ran = []
    monkeypatch.setattr(rerun, 'STEPS', {i: (lambda ctx, i=i: ran.append(i) or (True, 'ok')) for i in rerun.receipt_ids()})
    rerun.main(['--only', 'stamps'])
    assert ran == ['stamps']
    assert rerun.main(['--only', 'made-up']) == 2


def make(tmp_path, body, logged):
    (tmp_path / 'd').mkdir(); (tmp_path / 'd' / 'a.txt.ots').write_bytes(MAGIC + bytes.fromhex(hashlib.sha256(body).hexdigest()))
    (tmp_path / 'STAMPS.md').write_text(f'| x | d/a.txt | {logged} | d/a.txt.ots | pending |\n', encoding='utf-8')


def test_a_stamp_that_names_its_logged_fingerprint_passes(tmp_path):
    make(tmp_path, b'hi', hashlib.sha256(b'hi').hexdigest())
    [(name, ok, why)] = rerun.stamp_rows(tmp_path, tmp_path / 'nowhere')
    assert ok and 'pending' in why and 'kept private' in why


def test_a_stamp_whose_copy_was_replaced_fails(tmp_path):
    make(tmp_path, b'hi', hashlib.sha256(b'hi').hexdigest())
    orig = tmp_path / 'orig' / 'd'; orig.mkdir(parents=True); (orig / 'a.txt').write_bytes(b'changed')
    [(name, ok, why)] = rerun.stamp_rows(tmp_path, tmp_path / 'orig')
    assert not ok and 'replaced' in why


def test_a_stamp_naming_an_unlogged_fingerprint_fails(tmp_path):
    make(tmp_path, b'hi', '0' * 64)
    assert not rerun.stamp_rows(tmp_path, tmp_path / 'nowhere')[0][1]


def test_a_file_that_is_not_a_proof_fails(tmp_path):
    (tmp_path / 'x.ots').write_bytes(b'not a proof'); (tmp_path / 'STAMPS.md').write_text('', encoding='utf-8')
    assert not rerun.stamp_rows(tmp_path, tmp_path)[0][1]
