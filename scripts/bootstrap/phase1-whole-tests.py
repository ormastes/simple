#!/usr/bin/env python3
"""Owned Phase1 seed test callback; the caller owns aggregate admission/closure.

Use the repository's Simple runner/configuration, executed by the pinned seed.
Do not substitute the legacy Rust test runner or manufacture skip lists.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

MAX_SUMMARY_BYTES = 32 * 1024 * 1024


def read_summary_lines(path, limit=MAX_SUMMARY_BYTES):
    """Bound each allocation even if a compiler emits a giant unterminated line."""
    with Path(path).open('rb') as stream:
        while True:
            line = stream.readline(limit + 1)
            if not line:
                return
            if len(line) > limit:
                raise ValueError('stdout line exceeds bounded summary size')
            # Canonical formatter prints one compact JSON object per line:
            # test_runner_output.spl:238; test_runner_main.spl:1353.
            if line.lstrip().startswith(b'{'):
                yield line.decode('utf-8', errors='strict')


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def classify(exit_code, output):
    summaries = []
    for line in output.splitlines() if isinstance(output, str) else output:
        try:
            value = json.loads(line)
        except (ValueError, TypeError):
            continue
        if isinstance(value, dict) and all(k in value for k in ('success', 'spec', 'spl_doctest', 'sdoctest')):
            summaries.append(value)
    if len(summaries) != 1:
        return 'INFRASTRUCTURE_FAILED', None, 'expected one combined runner summary'
    summary = summaries[0]
    if any(not isinstance(summary[k], dict) for k in ('spec', 'spl_doctest', 'sdoctest')):
        return 'INFRASTRUCTURE_FAILED', summary, 'whole run omitted a required test category'
    # Never turn a crash/nonzero process into PASS using partial stdout.
    if exit_code not in (0, 1):
        return 'INFRASTRUCTURE_FAILED', summary, 'runner process did not complete normally'
    spec = summary['spec']
    for category, names in ((spec, ('total_passed', 'total_failed', 'total_skipped', 'total_pending')),
                            (summary['spl_doctest'], ('passed', 'failed', 'skipped', 'errors')),
                            (summary['sdoctest'], ('passed', 'failed', 'skipped', 'errors'))):
        if any(type(category.get(name)) is not int or category[name] < 0 for name in names):
            return 'INFRASTRUCTURE_FAILED', summary, 'missing or invalid result counters'
    tested = spec.get('total_passed', 0) + spec.get('total_failed', 0)
    tested += sum(summary[k].get('passed', 0) + summary[k].get('failed', 0)
                  for k in ('spl_doctest', 'sdoctest'))
    if tested == 0:
        return 'INFRASTRUCTURE_FAILED', summary, 'no assertions executed'
    failures = spec['total_failed'] + sum(summary[k]['failed'] + summary[k]['errors']
                                        for k in ('spl_doctest', 'sdoctest'))
    if exit_code == 0 and summary['success'] is True and failures == 0 and spec.get('success') is True:
        return 'PASS', summary, ''
    return 'FAIL', summary, 'runner reported failures; skips remain separate'


def validate_partitions(summary):
    if summary is None:
        return ''
    for key in ('spec', 'spl_doctest', 'sdoctest'):
        category = summary.get(key)
        if not isinstance(category, dict):
            return 'required category absent'
        files = category.get('files')
        if not isinstance(files, list):
            return 'per-file result inventory absent'
        counters = ('passed', 'failed', 'skipped', 'pending') if key == 'spec' else ('passed', 'failed', 'skipped', 'errors')
        prefix = 'total_' if key == 'spec' else ''
        paths = set()
        for row in files:
            if not isinstance(row, dict) or not isinstance(row.get('path'), str) or row['path'] in paths:
                return 'invalid or duplicate per-file result identity'
            paths.add(row['path'])
            if any(type(row.get(n)) is not int or row[n] < 0 for n in counters):
                return 'invalid per-file counters'
        for name in counters:
            if sum(row[name] for row in files) != category.get(prefix+name):
                return 'per-file and aggregate counts disagree'
        if key == 'spec' and any(row.get('error') for row in files) and summary.get('success') is True:
            return 'success summary contains aborted or errored file'
        if key != 'spec' and category.get('total') != sum(category[n] for n in counters):
            return 'doctest total does not partition into outcomes'
    return ''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', required=True, type=Path)
    parser.add_argument('--seed-sha256', required=True)
    parser.add_argument('--source-root', required=True, type=Path)
    parser.add_argument('--output-root', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=20)
    operation = parser.add_mutually_exclusive_group()
    operation.add_argument('--prepare-only', action='store_true')
    operation.add_argument('--resume-prepared', action='store_true')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 128:
        parser.error('jobs must be 1..128 and match the caller-admitted lane')
    seed, source, output = args.seed.resolve(), args.source_root.resolve(), args.output_root.resolve()
    if digest(seed) != args.seed_sha256:
        parser.error('seed byte identity differs')
    inputs = ['config/simple.test.sdn', 'config/sdoctest.sdn',
              'src/app/test_runner_new/main.spl',
              'src/app/test_runner_new/test_runner_main.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl']
    pins = {name: digest(source / name) for name in inputs}
    if not args.resume_prepared:
        output.mkdir(parents=True, exist_ok=False)
    elif not output.is_dir() or output.is_symlink():
        parser.error('prepared physical output root unavailable')
    command = [str(seed), 'test', '--whole', '--parallel', f'--max-workers={args.jobs}',
               '--unstable', '--mode=interpreter', '--json']
    environment = os.environ.copy()
    environment.pop('SIMPLE_TEST_RUNNER_RUST', None)
    environment.update(SIMPLE_BINARY=str(seed), SIMPLE_RUNTIME=str(seed),
                       SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source / 'src'),
                       SIMPLE_TEST_JOBS=str(args.jobs))
    request = dict(schema='simple-phase1-whole-tests-v1', seed=str(seed),
                   seed_sha256=args.seed_sha256, source_root=str(source),
                   input_hashes=pins, command=command, jobs=args.jobs,
                   cache_policy='runner-owned compatible cache; no clean/force-rebuild',
                   admission='caller-owned; this callback creates no background owners')
    request_path = output / 'request.json'
    if args.resume_prepared:
        if request_path.is_symlink() or request_path.stat().st_size > 1048576:
            parser.error('prepared request is not a bounded regular file')
        if json.loads(request_path.read_text(encoding='utf-8')) != request:
            parser.error('prepared request identity differs')
        if any((output / name).exists() for name in ('stdout.log', 'stderr.log', 'result.json')):
            parser.error('prepared request has already executed')
    else:
        request_path.write_text(json.dumps(request, indent=2) + '\n', encoding='utf-8')
    if args.prepare_only:
        return 0
    started = time.monotonic()
    with (output / 'stdout.log').open('wb') as stdout, (output / 'stderr.log').open('wb') as stderr:
        child = subprocess.run(command, cwd=source, env=environment, stdout=stdout, stderr=stderr)
    try:
        status, summary, reason = classify(child.returncode, read_summary_lines(output / 'stdout.log'))
        partition_error = validate_partitions(summary)
        if partition_error:
            status, reason = 'INFRASTRUCTURE_FAILED', partition_error
    except (ValueError, UnicodeError) as error:
        status, summary, reason = 'INFRASTRUCTURE_FAILED', None, str(error)
    unchanged = digest(seed) == args.seed_sha256 and all(digest(source / name) == sha for name, sha in pins.items())
    if not unchanged:
        status, reason = 'INFRASTRUCTURE_FAILED', 'pinned seed or runner/configuration changed during execution'
    result = dict(schema='simple-phase1-whole-tests-result-v1', status=status,
                  process_exit=child.returncode, elapsed_seconds=time.monotonic()-started,
                  runner_summary=summary, reason=reason, request_sha256=digest(output / 'request.json'),
                  stdout_sha256=digest(output / 'stdout.log'), stderr_sha256=digest(output / 'stderr.log'),
                  coverage_status='NOT_PROVEN: runner JSON has no discovered/excluded/aborted inventory totals',
                  phase='phase1', qualification='seed-only; not pure-Simple Phase2/product qualification')
    temporary = output / 'result.json.tmp'
    temporary.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    os.replace(temporary, output / 'result.json')
    return 0 if status == 'PASS' else 1 if status == 'FAIL' else 2


if __name__ == '__main__':
    raise SystemExit(main())
