"""Reject proof placeholders and project-defined axioms in first-party Lean files."""
from pathlib import Path
import re

files = [Path('HadwigerRamsey.lean'), Path('HadwigerRamsey4Col.lean'),
         *Path('HadwigerRamsey').rglob('*.lean'),
         *Path('HadwigerRamsey4Col').rglob('*.lean'), *Path('vendor').rglob('*.lean')]
failures = []
for path in files:
    # These words are intentionally prohibited even in comments, to make this
    # simple guard conservative. The kernel axiom report is also built by Lake.
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if re.search(r'\b(sorry|admit|axiom|unsafe)\b', line):
            failures.append(f'{path}:{number}: prohibited proof escape: {line.strip()}')
if failures:
    raise SystemExit('\n'.join(failures))
print(f'Checked {len(files)} Lean source files: no proof placeholders or custom axioms.')
