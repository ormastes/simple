"""New parser rejection criteria only; no runtime or previous green test execution."""
import importlib.util
from pathlib import Path
root=Path(__file__).parent
s=importlib.util.spec_from_file_location('qualifier',root/'qualify-pr.py')
q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
rejected=0
for suffix in ['Pending: 1','Skipped: 1','Blocked: 1','UNVERIFIED','process-error']:
    try:q.counts('Results: 16 total, 16 passed, 0 failed\n'+suffix,16)
    except AssertionError:rejected+=1
assert rejected==5
print('PASS: five new incomplete-verdict rejection criteria; no product executed')
