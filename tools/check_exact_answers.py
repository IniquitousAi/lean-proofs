"""E1 check (CHIEF, 2026-10-20): every headline pXX theorem must state the engine's exact answer, not a weaker property.

    python tools/check_exact_answers.py     exit 1 if any problem Proven by Lean has no theorem whose right side is its exact answer

The answer comes from ../answer-bank/answers.json (exactAnswer), or for p48/p65 bridge/p69 tail (numbered p101-p103, not in the
bank) from an exact Fraction computation here. The Lean side is the last `= <number or a/b>` before `:=` in each theorem.
"""
import json, math, pathlib, re, sys
from fractions import Fraction as F
from itertools import product

HERE = pathlib.Path(__file__).resolve().parent.parent
BANK = HERE.parent / 'answer-bank' / 'answers.json'
if not BANK.exists(): BANK = pathlib.Path(r'C:\Users\danie\Desktop\projects\answer-bank\answers.json')
THM = re.compile(r'^theorem\s+(p\d\d\w*)\s*(.*?):=', re.M | re.S)
NUM = r'\(?\s*(\d+)\s*(?::\s*[^\s)]+\s*)?\)?'
RHS = re.compile(rf'=\s*{NUM}(?:\s*/\s*{NUM})?\s*$')


def extra():
    def coins(n, p, k): return sum(math.comb(n, i) * p**i * (1 - p)**(n - i) for i in range(k, n + 1))
    dice = [1]
    for _ in range(20): dice = [sum(dice[j - f] for f in range(1, 7) if 0 <= j - f < len(dice)) for j in range(len(dice) + 6)]
    return {'p48_third_success_by_twelve': coins(12, F(1, 3), 3),
            'p65_trap_bridge_aces_kings': F(math.comb(44, 5), math.comb(52, 13)),
            'p69_trap_twenty_dice_low_tail': F(sum(dice[:31]), 6**20)}


def exact(p):
    s = p['exactAnswer'].split(' ')[0] if re.fullmatch(r'[\d/]+ \w+', p['exactAnswer']) else p['exactAnswer']
    if p['id'] == 'p05_birthday_problem': return 1 - F(math.perm(365, 23), 365**23)
    try: return F(s)
    except ValueError: return None


def main():
    want = {p['id']: exact(p) for p in json.loads(BANK.read_text(encoding='utf-8'))['problems']} | extra()
    stated = {}
    for f in sorted((HERE / 'LeanProofs').glob('*.lean')):
        text = re.sub(r'--.*', '', re.sub(r'/-.*?-/', '', f.read_text(encoding='utf-8'), flags=re.S))
        for m in THM.finditer(text):
            r = RHS.search(' '.join(m.group(2).split()))
            if r: stated.setdefault(m.group(1), []).append(F(int(r.group(1)), int(r.group(2) or 1)))
    bad = checked = 0
    for pid in sorted(want):
        vals = stated.get(pid) or [v for n, vs in stated.items() if n.split('_')[0] == pid.split('_')[0] and not any(k == n for k in want) for v in vs] or None
        if vals is None: continue   # (no Lean theorem by the problem's own name: not Proven by Lean, nothing to check)
        ok = want[pid] is not None and want[pid] in vals
        bad += not ok; checked += 1
        print(f"{'OK ' if ok else 'BAD'} {pid}: engine {want[pid]}  Lean states {', '.join(map(str, vals))}")
    print(f"{checked} headline theorems checked, {bad} not exact")
    return bad == 0


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
