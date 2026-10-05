#!/usr/bin/env python3
"""Verify an independently pinned bootstrap orchestration tree, never source authority."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath


def sha(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('tool input must be a regular file: ' + str(path))
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def validate(root, manifest, expected, entry=None):
    root, manifest = Path(root), Path(manifest)
    if root.is_symlink() or not root.is_dir() or sha(manifest) != expected:
        raise ValueError('tool root or manifest identity differs')
    root = root.resolve()
    if manifest.stat().st_size > 8 * 1024 * 1024:
        raise ValueError('tool manifest exceeds bounded size')
    value = json.loads(manifest.read_text(encoding='utf-8'))
    if value.get('schema') != 'simple-bootstrap-tool-code-v1':
        raise ValueError('unsupported tool authority schema')
    head = value.get('tool_head', '')
    if not re.fullmatch('[0-9a-f]{40}', head):
        raise ValueError('tool commit identity required')
    actual = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                                     text=True).strip()
    if actual != head:
        raise ValueError('tool commit differs')
    files = value.get('files')
    if not isinstance(files, dict) or not files:
        raise ValueError('nonempty tool closure required')
    # Pin complete script directories, including transitive shell/Perl imports.
    prefixes = ('scripts/bootstrap/', 'scripts/check/lib/')
    catalog = subprocess.check_output(['git', '-C', str(root), 'ls-tree', '-rz',
        '--full-tree', head, '--', *prefixes])
    committed = {}
    for row in catalog.split(b'\0'):
        if not row:
            continue
        metadata, name = row.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split()
        if mode not in ('100644', '100755') or kind != 'blob':
            raise ValueError('nonregular committed tool member')
        committed[name.decode('utf-8')] = oid
    if set(files) != set(committed):
        raise ValueError('tool manifest differs from committed closure')
    physical = set()
    for prefix in prefixes:
        directory = root / prefix
        if not directory.is_dir() or directory.is_symlink():
            raise ValueError('tool closure directory unavailable')
        for path in directory.rglob('*'):
            if path.is_symlink():
                raise ValueError('linked tool closure member')
            if path.is_file() and '__pycache__' not in path.parts:
                physical.add(path.relative_to(root).as_posix())
    if set(files) != physical:
        raise ValueError('tool manifest does not cover the complete physical closure')
    for name, expected_sha in files.items():
        relative = PurePosixPath(name)
        if (relative.is_absolute() or '..' in relative.parts or '\\' in name
                or not name.startswith(prefixes)
                or not isinstance(expected_sha, str)
                or not re.fullmatch('[0-9a-f]{64}', expected_sha)):
            raise ValueError('unsafe tool manifest member')
        if sha(root / name) != expected_sha:
            raise ValueError('tool bytes differ: ' + name)
        path = root / name
        git_hash = hashlib.sha1(b'blob ' + str(path.stat().st_size).encode('ascii') + b'\0')
        with path.open('rb') as stream:
            while chunk := stream.read(1024 * 1024):
                git_hash.update(chunk)
        if git_hash.hexdigest() != committed[name]:
            raise ValueError('tool bytes are not from pinned commit: ' + name)
    if entry is not None:
        relative = Path(entry).resolve().relative_to(root).as_posix()
        if relative not in files:
            raise ValueError('executing tool is outside pinned closure')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--entry', required=True, type=Path)
    args = parser.parse_args()
    validate(args.root, args.manifest, args.sha256, args.entry)


if __name__ == '__main__':
    main()
