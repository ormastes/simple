#!/usr/bin/env python3
"""Resume ownership/dispatch unit fixtures; not native product qualification.

The product verifier boundary is a receipt replay fixture. Its actual strict
raw-ledger contracts are covered by compiler-subsystem-product-verifier-test.shs.
"""
from pathlib import Path
import hashlib
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
EVIDENCE = ('build.exit build.stdout.log build.stderr.log build.env enumeration.exit '
            'enumeration.tsv enumeration.stdout.log enumeration.stderr.log enumeration-watchdog.env '
            'execution.exit execution.tsv execution.stdout.log execution.stderr.log execution-watchdog.env').split()
with tempfile.TemporaryDirectory(prefix='subsystem-resume-unit.') as td:
    top = Path(td)
    output = top / 'output'
    output.mkdir()
    source = top / 'source'
    source.mkdir()
    lock = output / '.product-owner.lock'
    lock.mkdir()
    inventory = output / 'source-specs.tsv'
    inventory.write_text('fixture inventory\n')
    inventory_program = top / 'inventory.sh'
    inventory_program.write_text('#!/bin/sh\nprintf "fixture inventory\\n"\n')
    fields = dict(format='SIMPLE-SUBSYSTEM-TEST-MATRIX-1', status='FAIL', source_root=str(source),
                  execution_cwd=str(source), runtime_mode='native', threads='20', rss_cap_kib='6835937',
                  build_timeout_seconds='1800', test_timeout_seconds='7200', inventory_sha256=sha(inventory))
    rows = []
    for backend in ('llvm', 'cranelift'):
        producer = top / backend
        producer.mkdir()
        compiler = producer / 'simple'
        compiler.write_text('compiler ' + backend)
        receipt = producer / 'admission.env'
        receipt.write_text('schema=simple-bootstrap-stage2-admission-v2\nstatus=admitted\n'
                           f'candidate_path={compiler}\ncandidate_sha256={sha(compiler)}\n')
        fields[f'compiler_{backend}_sha256'] = sha(compiler) if backend == 'cranelift' else 'MISSING'
        fields[f'producer_receipt_{backend}_path'] = str(receipt) if backend == 'cranelift' else ''
        fields[f'producer_receipt_{backend}_sha256'] = sha(receipt) if backend == 'cranelift' else 'MISSING'
        for suite in ('compiler', 'interpreter', 'loader'):
            for stage in ('build', 'enumerate', 'run'):
                rows.append(f'phase4_{backend}_product_{suite}_{stage}\t' +
                            ('SUCCEEDED\t0\n' if backend == 'cranelift' else 'BLOCKED\t1\n'))
            if backend == 'llvm':
                continue
            job = output / backend / suite
            job.mkdir(parents=True)
            (job / 'result.env').write_text('status=PASS\nunit_fixture=receipt-replay-boundary\n')
            fields[f'{backend}_{suite}_receipt_sha256'] = sha(job / 'result.env')
            for name in EVIDENCE:
                path = job / name
                path.write_text('0\n' if name.endswith('.exit') else f'fixture {name}\n')
                key = name.replace('.', '_').replace('-', '_')
                fields[f'{backend}_{suite}_{key}_sha256'] = sha(path)
            for stage in ('build', 'enumeration', 'execution'):
                fields[f'{backend}_{suite}_{stage}_exit'] = '0'
    statuses = output / 'product-status.tsv'
    statuses.write_text(''.join(rows))
    fields['schedule_sha256'] = sha(statuses)
    matrix = output / 'matrix.env'
    matrix.write_text(''.join(f'{k}={v}\n' for k, v in fields.items()) + ''.join(rows))
    original_matrix = matrix.read_bytes()
    original_status = statuses.read_bytes()
    # Paths originate from tempfile (no quotes/newlines).
    script = f'''set -eu
source_root='{source}'
output_root='{output}'
owner_lock='{lock}'
inventory='{inventory}'
inventory_program='{inventory_program}'
statuses='{statuses}'
matrix='{matrix}'
threads=20 rss_cap_kib=6835937 build_timeout=1800 test_timeout=7200
regular() {{ [ -f "$1" ] && [ ! -L "$1" ]; }}
hash_file() {{ regular "$1" || exit 2; sha256sum "$1" | cut -d ' ' -f 1; }}
die() {{ echo "$*" >&2; exit 2; }}
compiler_for() {{ printf '{top}/%s/simple\\n' "$1"; }}
receipt_for() {{ printf '{top}/%s/admission.env\\n' "$1"; }}
job_for() {{ printf '%s/%s/%s\\n' "$output_root" "$1" "$2"; }}
verify_base() {{
  [ "$3" = complete ] || exit 2
  backend=$1 suite=$2
  case "${{REJECT_REPLAY:-0}}" in 1) return 1 ;; esac
  for arg do case "$arg" in --output=*) target=${{arg#*=}} ;; esac; done
  cp "$(job_for "$backend" "$suite")/result.env" "$target"
}}
. '{ROOT}/lib/subsystem-product-resume.shs'
resume_validate
[ "$resume_reused" = cranelift ] && [ "$resume_missing" = llvm ]
product_reuse_ready() {{ [ "$1" = "$resume_reused" ]; }}
managed_attempt_product() {{ printf '%s/%s\\n' "$1" "$2" >>'{top}/dispatch'; }}
. '{ROOT}/lib/managed-task-schedule.shs'
# Restore fixture operation after importing the real dispatcher.
managed_attempt_product() {{ printf '%s/%s\\n' "$1" "$2" >>'{top}/dispatch'; }}
managed_dispatch_products
'''
    def run(ok, prefix=''):
        result = subprocess.run(['sh', '-c', prefix + script], capture_output=True, text=True)
        assert (result.returncode == 0) == ok, result.stderr
        assert statuses.read_bytes() == original_status
    run(True)
    assert (top / 'dispatch').read_text().splitlines() == ['llvm/compiler', 'llvm/interpreter', 'llvm/loader']
    assert matrix.read_bytes() == original_matrix
    run(False, 'REJECT_REPLAY=1\n')
    matrix.write_bytes(original_matrix + b'threads=20\n')
    run(False)
    matrix.write_bytes(original_matrix)
    p = output / 'cranelift/compiler/execution.tsv'
    saved = p.read_bytes()
    p.write_text('tampered raw execution\n')
    run(False)
    p.write_bytes(saved)
    (output / 'llvm').mkdir()
    run(False)
    (output / 'llvm').rmdir()
    matrix.write_bytes(original_matrix.replace(b'test_timeout_seconds=7200', b'test_timeout_seconds=1'))
    run(False)
    matrix.write_bytes(original_matrix)
    source_receipt = top / 'cranelift/admission.env'
    saved = source_receipt.read_bytes()
    source_receipt.write_bytes(saved + b'status=admitted\n')
    run(False)
    source_receipt.write_bytes(saved)
    # Reject partial/failed journals even if their outer hash is updated.
    changed = original_status.replace(b'BLOCKED\t1', b'FAILED\t1', 1)
    statuses.write_bytes(changed)
    matrix.write_bytes(original_matrix.replace(original_status, changed).replace(
        fields['schedule_sha256'].encode(), sha(statuses).encode()))
    result = subprocess.run(['sh', '-c', script], capture_output=True)
    assert result.returncode != 0
print('PASS: resume dispatches only absent backend; rejects replay failure, duplicate fields, raw tamper, partial artifacts, policy drift and failed tasks')
