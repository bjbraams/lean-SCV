#!/usr/bin/env python3
"""Generate `Challenge.lean` from `Solution.lean` for the Palomar registry.

`Solution.lean` is the master file.  The Challenge is the same text with
* the import of the project library removed,
* everything between `-- BEGIN SOLUTION ONLY` and `-- END SOLUTION ONLY` removed,
* the proof of every `theorem` replaced by `sorry`.
A proof starts after the first line of the theorem that ends in `:=` or `:= by` and extends to the
next blank line, so proofs in `Solution.lean` must not contain blank lines. Block comments and
docstrings must start at the beginning of a line; their text is copied and never parsed.
Also writes the list of compared theorem names into `comparator.json`.
"""
import json, re

src = open('Solution.lean', encoding='utf-8').read().split('\n')
out, names, ns = [], [], []
i, skip, in_comment = 0, False, False
while i < len(src):
    l = src[i]
    if l.strip() == '-- BEGIN SOLUTION ONLY':
        skip = True
    elif l.strip() == '-- END SOLUTION ONLY':
        skip = False
        if out and out[-1] == '' and i + 1 < len(src) and src[i + 1] == '':
            i += 1
    elif skip or re.match(r'^import SeveralComplexVariables\b', l):
        pass
    elif in_comment or l.startswith('/-'):
        # block comments and docstrings are copied verbatim; their text is never parsed
        in_comment = '-/' not in l[2:] if l.startswith('/-') and not in_comment else '-/' not in l
        out.append(l)
    else:
        m = re.match(r'^namespace (\S+)', l)
        if m:
            ns.append(m.group(1))
        if re.match(r'^end \S+', l) and ns:
            ns.pop()
        m = re.match(r'^theorem (\S+)', l)
        if m:
            names.append('.'.join(ns + [m.group(1)]))
            while not re.search(r':=( by)?\s*$', src[i]):
                out.append(src[i]); i += 1
            out.append(re.sub(r':=( by)?\s*$', ':= by', src[i]))
            out.append('  sorry')
            while i + 1 < len(src) and src[i + 1].strip() != '':
                i += 1
        else:
            out.append(l)
    i += 1
text = '\n'.join(out).replace('Solution.lean', 'Challenge.lean')
open('Challenge.lean', 'w', encoding='utf-8').write(text)
cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": names,
       "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
open('comparator.json', 'w', encoding='utf-8').write(json.dumps(cfg, indent=2, ensure_ascii=False) + '\n')
n = len(out)
print(f'Challenge.lean: {n} lines, {len(text.encode())} bytes, {len(names)} theorems')
assert n <= 1000 and len(text.encode()) <= 100 * 1024, 'Palomar hard limit exceeded'
