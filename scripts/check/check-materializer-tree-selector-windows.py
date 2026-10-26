#!/usr/bin/env python3
"""Check the real Windows materializer's bound-tree selection and failures.

Run from any directory: python scripts/check/check-materializer-tree-selector-windows.py
Requires Windows PowerShell and Git. Exits 77 on unsupported hosts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--producer', type=Path, default=Path(__file__).resolve().parent.parent / 'setup/materialize-symlinks-windows.shs')
    parser.add_argument('--case', action='append', help='Run only the named regression; repeat for multiple cases.')
    args = parser.parse_args()
    powershell = shutil.which('powershell.exe')
    if os.name != 'nt' or not powershell or not shutil.which('git'):
        print('BLOCKED: Windows PowerShell and Git are required')
        return 77
    source = args.producer.read_text(encoding='utf-8')
    helper = re.search(r"<<'POWERSHELL'\n(.*?)\nPOWERSHELL", source, re.S)
    if helper is None:
        raise RuntimeError('actual materializer helper not found')
    oid, other = '1' * 40, '2' * 40

    def pairs(*entries):
        return b''.join(f'{path}\0{object_id}\0'.encode('utf-8') for path, object_id in entries)

    mixed = [
        ('100644', oid, 'a-regular'), ('040000', oid, 'b-directory'),
        ('160000', oid, 'c-gitlink'), ('120000', oid, 'd file link'),
        ('120000', other, "e-ü'[]$;& link"), ('120000', oid, 'sub/target/skip'),
        ('120000', oid, 'target/skip'), ('120000', oid, 'target'),
        ('120000', oid, 'targetish/keep'), ('120000', other, 'z-last'),
    ]
    cases = [
        ('mixed', b''.join(f'{mode} {obj} {path}\0'.encode('utf-8') for mode, obj, path in mixed),
         pairs(('d file link', oid), ("e-ü'[]$;& link", other), ('target', oid), ('targetish/keep', oid), ('z-last', other)), None),
        ('empty', b'', b'', None),
        ('large-sparse', b''.join(f'100644 {oid} regular/{i:06d}\0'.encode() for i in range(10000)) + f'120000 {other} z-link\0'.encode(), pairs(('z-link', other)), None),
        ('missing-fields', b'invalid\0', None, 'tree.fields'),
        ('invalid-utf8', b'100644 ' + oid.encode() + b' bad\xff\0', None, 'DecoderFallbackException'),
        ('policy-digest', f'120000 {oid} link\0'.encode(), None, 'receipt.policy-digest-mismatch'),
        ('list-destination', f'120000 {oid} link\0'.encode(), None, 'UnauthorizedAccessException'),
        ('unterminated-only', f'120000 {oid} dropped'.encode(), b'', None),
        ('unterminated-after-complete', f'120000 {oid} kept\0'.encode() + f'120000 {other} dropped'.encode(), pairs(('kept', oid)), None),
    ]
    if args.case:
        unknown = set(args.case) - {case[0] for case in cases}
        if unknown:
            parser.error('unknown case: ' + ', '.join(sorted(unknown)))
        cases = [case for case in cases if case[0] in args.case]
    failures = []
    # Each unique fixture is below the OS-selected temporary directory and
    # contains only test-authored regular files; no fixture creates links.
    with tempfile.TemporaryDirectory(prefix='simple-materializer-selector-') as temporary:
        root = Path(temporary).resolve()
        if root.parent != Path(tempfile.gettempdir()).resolve():
            raise RuntimeError('unexpected temporary fixture parent')
        api = root / 'api.ps1'
        api.write_text(helper.group(1), encoding='utf-8')
        for name, inventory, expected, error in cases:
            fixture = root / name
            fixture.mkdir()
            tree, links, policy = fixture / 'tree', fixture / 'list', fixture / 'policy'
            tree.write_bytes(inventory)
            links.write_bytes(b'')
            policy.write_bytes(b'')
            env = os.environ.copy()
            env.update(MATERIALIZER_ROOT=str(fixture), MATERIALIZER_TREE=str(tree),
                       MATERIALIZER_LIST=str(fixture if name == 'list-destination' else links),
                       MATERIALIZER_POLICY=str(policy), MATERIALIZER_BLOB=str(fixture / 'blob'),
                       MATERIALIZER_POLICY_SHA256='0' * 64 if name == 'policy-digest' else hashlib.sha256(b'').hexdigest(),
                       TEMP=str(fixture), TMP=str(fixture))
            requests = ''
            responses = ['READY']
            if name == 'mixed':
                requests = ''.join(f'tracked\t{path}\t\n' for path in ['a-regular', 'b-directory', 'c-gitlink', 'sub/target/skip', 'absent'])
                responses += ['OK|tracked'] * 4 + ['OK|untracked']
            if name.startswith('unterminated'):
                requests = 'tracked\tdropped\t\n'
                responses += ['OK|tracked']
            child = subprocess.run([powershell, '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', str(api)],
                                   input=requests, text=True, encoding='utf-8', capture_output=True,
                                   env=env, cwd=fixture, timeout=45)
            if error:
                passed = child.returncode != 0 and 'READY' not in child.stdout and error in child.stderr
            else:
                passed = child.returncode == 0 and child.stdout.splitlines() == responses and links.read_bytes() == expected
            print(json.dumps({'case': name, 'passed': passed, 'returncode': child.returncode}))
            if not passed:
                failures.append(name)
                print(child.stderr[:2000])
    if failures:
        print('FAIL: ' + ', '.join(failures))
        return 1
    print(f'PASS: {len(cases)} actual materializer helper criteria')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
