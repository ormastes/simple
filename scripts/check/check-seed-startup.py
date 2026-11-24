#!/usr/bin/env python3
"""Execute the exact native seed before publishing it; retain failure evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def check(seed, output, timeout=30):
    seed = seed.resolve(strict=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    before = sha256(seed)
    status, code, stdout, stderr = 'FAIL', None, b'', b''
    try:
        result = subprocess.run([str(seed), '--version'], capture_output=True, timeout=timeout)
        code, stdout, stderr = result.returncode, result.stdout, result.stderr
        if code == 0 and re.search(rb'\bsimple\b', stdout, re.IGNORECASE):
            status = 'PASS'
    except subprocess.TimeoutExpired as error:
        status, stdout, stderr = 'TIMEOUT', error.stdout or b'', error.stderr or b''
    except OSError as error:
        stderr = str(error).encode('utf-8')
    after = sha256(seed)
    if before != after:
        status = 'FAIL'
    output.write_text(json.dumps(dict(schema='simple-native-seed-startup-v1',
        status=status, seed=str(seed), seed_sha256=before, seed_sha256_after=after,
        command=[str(seed), '--version'], exit_code=code,
        stdout=stdout.decode('utf-8', errors='replace'),
        stderr=stderr.decode('utf-8', errors='replace'),
        qualification='native startup only; not compiler Hello or bootstrap admission'), indent=2) + '\n',
        encoding='utf-8')
    print(f'{status}: native seed startup; evidence={output}')
    return 0 if status == 'PASS' else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    return check(args.seed, args.output)


if __name__ == '__main__':
    raise SystemExit(main())
