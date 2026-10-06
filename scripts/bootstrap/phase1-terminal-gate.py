#!/usr/bin/env python3
"""Wait for exact Phase1 completion; test failure permits later suite execution."""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path


def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('terminal evidence is not a regular file')
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def validate_terminal(path, request_sha):
    if not re.fullmatch('[0-9a-f]{64}', request_sha):
        raise ValueError('invalid expected Phase1 request digest')
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 64 * 1024 * 1024:
        raise ValueError('terminal receipt is absent, linked, or too large')
    value = json.loads(path.read_text(encoding='utf-8'))
    if (value.get('schema') != 'simple-phase1-whole-tests-result-v1'
            or value.get('phase') != 'phase1'
            or value.get('status') not in ('PASS', 'FAIL', 'INFRASTRUCTURE_FAILED')
            or type(value.get('process_exit')) is not int
            or value.get('request_sha256') != request_sha
            or digest(path.parent / 'request.json') != request_sha):
        raise ValueError('Phase1 terminal identity differs')
    for stream in ('stdout', 'stderr'):
        if value.get(stream + '_sha256') != digest(path.parent / (stream + '.log')):
            raise ValueError('Phase1 terminal stream changed')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', required=True, type=Path)
    parser.add_argument('--request-sha256', required=True)
    args = parser.parse_args()
    # The enclosing retained owner must publish infrastructure completion even
    # if its Phase1 callback fails before starting the runner. No time limit is
    # reclassified as a compiler or test failure here.
    while not args.receipt.exists():
        if args.receipt.is_symlink():
            raise ValueError('linked terminal receipt')
        time.sleep(1)
    value = validate_terminal(args.receipt, args.request_sha256)
    print(json.dumps(dict(phase1_status=value['status'], request_sha256=args.request_sha256,
                          terminal_sha256=digest(args.receipt), full_run_permitted=True)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
