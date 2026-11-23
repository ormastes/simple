from pathlib import Path
import re

source = Path('test/01_unit/compiler/driver/worker_surface_gap_spec.spl').read_text()
blocks = re.findall(r'^    it .*?(?=^    it |\Z)', source, re.M | re.S)
selected = [block for block in blocks if block.startswith('    it "reports the actual invalid edge')
            or block.startswith('    it "bounds path text')]
assert len(selected) == 2
Path('gap-evidence/changed_spec.spl').write_text(source[:source.index('describe ')]
    + 'describe "changed diagnostic formatting":\n' + '\n'.join(selected))
