#!/usr/bin/env python3
"""Exercise the POSIX bootstrap allowlist through the actual Windows Job owner."""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--cc', required=True)
parser.add_argument('--output-root', type=Path, required=True)
parser.add_argument('--source-root', type=Path, default=Path(__file__).resolve().parents[3])
args = parser.parse_args()
if os.name != 'nt':
    raise SystemExit('UNSUPPORTED: actual Windows Job execution required')
source = args.source_root.resolve()
out = args.output_root.resolve()
out.mkdir(parents=True, exist_ok=False)
for name in ['repo/build', 'external', 'outside']:
    (out / name).mkdir(parents=True)
capture = out / 'native-capture.py'
capture.write_text(
    'import json, os, sys\nfrom pathlib import Path\n'
    'Path(sys.argv[1]).write_text(json.dumps({"argv":sys.argv[2:], '
    '"kept":os.environ["BOOTSTRAP_TEST_KEEP"], '
    '"converted":os.environ["BOOTSTRAP_TEST_CONVERT"], '
    '"exclusions":os.environ["MSYS2_ENV_CONV_EXCL"]}))\n', encoding='utf-8')
q = shlex.quote
check = out / 'check.shs'
check.write_text(
    '#!/usr/bin/env bash\nset -eu\n'
    + '. ' + q((source / 'scripts/check/lib/bootstrap-stage3/authority.shs').as_posix()) + '\n'
    + 'base=$(cygpath -u ' + q(out.as_posix()) + ')\n'
    + 'printf "inherited_external=%s\\n" "$SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT"\n'
    + '[ "$SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT" = "$base/external" ]\n'
    + 'bootstrap_stage3_resume_output_path "$base/external" "$base/repo" "$SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT"\n'
    + '[ "$BOOTSTRAP_STAGE3_RESUME_OUTPUT" = "$base/external" ]\n'
    + 'if bootstrap_stage3_resume_output_path "$base/outside" "$base/repo" "$SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT"; then\n'
    + '  echo "FAIL: outside root accepted"; exit 1\nfi\n'
    + 'export BOOTSTRAP_TEST_CONVERT="$base/external"\n'
    + shlex.join([Path(sys.executable).as_posix(), capture.as_posix(),
                  (out / 'native.json').as_posix()]) + ' "$base/external"\n'
    + 'echo "PASS: exact root accepted; outside root refused"\n', encoding='utf-8')
launch = out / 'launch.shs'
command = ['perl', 'scripts/resource/process-tree-rss-watchdog.pl',
           '--max-rss-kib=262144', '--timeout-seconds=30', '--interval-ms=100',
           '--receipt=' + (out / 'owner.env').as_posix(), '--', 'bash', check.as_posix()]
launch.write_text(
    '#!/usr/bin/env bash\nset -eu\nexport PATH="/usr/bin:$PATH"\ncd ' + q(source.as_posix()) + '\n'
    + 'base=$(cygpath -u ' + q(out.as_posix()) + ')\n'
    + 'export SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT="$base/external"\n'
    + 'export SIMPLE_BOOTSTRAP_SESSION_HELPER_CACHE="$base/helper-cache"\n'
    + 'export BOOTSTRAP_TEST_KEEP="$base/external"\n'
    + 'export MSYS2_ENV_CONV_EXCL="BOOTSTRAP_TEST_KEEP="\n'
    + 'exec ' + shlex.join(command) + '\n', encoding='utf-8')
env = os.environ.copy()
env['CC'] = args.cc
run = subprocess.run(['C:/msys64/usr/bin/bash.exe', launch.as_posix()],
                     env=env, capture_output=True, timeout=90)
(out / 'stdout.log').write_bytes(run.stdout)
(out / 'stderr.log').write_bytes(run.stderr)
if run.returncode:
    raise SystemExit(f'FAIL: owner exit {run.returncode}; inspect {out}')
receipt = dict(line.split('=', 1) for line in (out / 'owner.env').read_text().splitlines())
assert receipt['status'] == 'complete' and receipt['exit_status'] == '0'
assert receipt['quiescent'] == '1' and receipt['rss_cap_enforced'] == '1'
assert int(receipt['rss_limit_kib']) == 262144
actual = json.loads((out / 'native.json').read_text())
expected = (out / 'external').as_posix()
assert actual['argv'] == [expected], actual
assert actual['converted'] == expected, actual
assert actual['kept'].startswith('/') and actual['kept'].endswith('/external'), actual
exclusions = actual['exclusions'].split(';')
for name in ['BOOTSTRAP_TEST_KEEP=', 'SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT=',
             'SIMPLE_BOOTSTRAP_SESSION_HELPER_CACHE=']:
    assert exclusions.count(name) == 1, actual
assert '*' not in exclusions, actual
print('PASS: real Windows Job preserves POSIX root, refuses outside root, and retains native conversion')
