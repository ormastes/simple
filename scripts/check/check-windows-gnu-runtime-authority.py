#!/usr/bin/env python3
"""Validate a CI Windows bootstrap archive before a Linux cross build."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

REQUIRED = {'rt_native_build', 'rt_set_args', 'rt_alloc', 'rt_free',
            'rt_string_new', 'rt_string_free', 'rt_array_new', 'rt_string_new_literal'}


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def validate_formats(headers):
    formats = re.findall(r'^Format: (.+)$', headers, re.MULTILINE)
    allowed = {'COFF-x86-64', 'COFF-import-file-x86-64'}
    if not formats or 'COFF-x86-64' not in formats or set(formats) - allowed:
        raise ValueError(f'expected only x86_64 COFF members, found {sorted(set(formats))}')
    return {name: formats.count(name) for name in sorted(set(formats))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--source-revision', required=True)
    parser.add_argument('--llvm-bin', required=True, type=Path)
    parser.add_argument('--producer', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    identity = dict(line.split('=', 1) for line in
                    (args.root / 'authority.env').read_text(encoding='utf-8-sig').splitlines())
    if identity['source_revision'] != args.source_revision:
        raise ValueError('archive source revision does not match this cross build')
    if identity['target'] != 'x86_64-pc-windows-gnullvm':
        raise ValueError('archive must come from the pinned Windows GNU LLVM target')
    archive = args.root / 'libsimple_native_all.a'
    expected = identity['native_all_sha256']
    if sha256(archive) != expected:
        raise ValueError('archive SHA-256 mismatch')
    suffix = '.exe' if os.name == 'nt' else ''
    headers = subprocess.check_output([str(args.llvm_bin / ('llvm-readobj' + suffix)),
                                      '--file-headers', str(archive)], text=True, timeout=60)
    formats = validate_formats(headers)
    symbols_text = subprocess.check_output([str(args.llvm_bin / ('llvm-nm' + suffix)),
        '--defined-only', '--extern-only', str(archive)], text=True, timeout=60)
    symbols = {line.split()[-1].lstrip('_') for line in symbols_text.splitlines() if line.split()}
    missing = REQUIRED - symbols
    if missing:
        raise ValueError(f'missing bootstrap runtime owners: {sorted(missing)}')
    if sha256(archive) != expected:
        raise ValueError('archive changed during validation')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(schema='windows-cross-runtime-evidence-v1',
        status='PASS', identity=identity, archive=str(archive.resolve()), formats=formats,
        producer_sha256=sha256(args.producer), required_symbols=sorted(REQUIRED),
        qualification='target archive and runtime ownership only; not compiler execution'),
        indent=2) + '\n', encoding='utf-8')
    print(f'PASS: Windows GNU archive identity, COFF members and runtime owners; {args.output}')


if __name__ == '__main__':
    main()
