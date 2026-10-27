#!/usr/bin/env python3
"""Owned Phase1 seed test callback; the caller owns aggregate admission/closure.

Use the repository's Simple runner/configuration, executed by the pinned seed.
Do not substitute the legacy Rust test runner or manufacture skip lists.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import time

MAX_REPORT_BYTES = 32 * 1024 * 1024
MAX_LINE_BYTES = 1024 * 1024
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
SPEC = re.compile(r'^SPEC FILE VERDICT: (.+?) outcome=(OK|ERROR|NOT_RUN) declared>=(\d+) executed=(\d+) passed=(\d+) failed=(\d+)(?: skipped=(\d+))?(?: in_development=(\d+))? dropped=(\d+)(.*)$')
FILES = re.compile(r'^Files:\s+(\d+) discovered, (\d+) executed$')
RESULTS = re.compile(r'^Results: (\d+) total, (\d+) passed, (\d+) failed(?:, (\d+) skipped)?(?:, (\d+) pending)?(.*)$')
SPL_DOC = re.compile(r'^SPL Doctest: (\d+) passed, (\d+) failed, (\d+) skipped$')
SDOC = re.compile(r'^SDoctest Results(?: \(fail-as-success\))?: (\d+) total, (\d+) passed, (\d+) failed(?:, (\d+) accepted)?, (\d+) skipped, (\d+) errors$')


def read_report(path, limit=MAX_REPORT_BYTES):
    """Read bounded human report bytes; retain every original line in the receipt."""
    if Path(path).stat().st_size > limit:
        raise ValueError('stdout report exceeds bounded report size')
    with Path(path).open('rb') as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise ValueError('stdout report exceeds bounded report size')
    text = data.decode('utf-8', errors='strict')
    if any(len(line.encode('utf-8')) > MAX_LINE_BYTES for line in text.splitlines()):
        raise ValueError('stdout report line exceeds bounded line size')
    return text


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def classify(exit_code, output):
    """Parse observed text summaries without collapsing category or per-file evidence."""
    lines = [ANSI.sub('', line).strip() for line in output.splitlines()]
    files = [FILES.fullmatch(line) for line in lines if line.startswith('Files:')]
    specs = [SPEC.fullmatch(line) for line in lines if line.startswith('SPEC FILE VERDICT:')]
    results = [RESULTS.fullmatch(line) for line in lines if line.startswith('Results:')]
    spldocs = [SPL_DOC.fullmatch(line) for line in lines if line.startswith('SPL Doctest:') and not re.fullmatch(r'SPL Doctest:\s+Running doctests from \d+ source file\(s\)\.\.\.', line)]
    sdocs = [SDOC.fullmatch(line) for line in lines if line.startswith('SDoctest Results')]
    report = dict(format='text-diagnostic', lines=lines, file_summary=None, spec_files=[], categories={})
    if any(len(found) != 1 or found[0] is None for found in (files, results, spldocs, sdocs)) or any(m is None for m in specs):
        return 'INFRASTRUCTURE_FAILED', report, 'missing, duplicate, or unrecognized category summary'
    fm, rm, sm, dm = files[0], results[0], spldocs[0], sdocs[0]
    if len(specs) != int(fm.group(1)) or int(fm.group(2)) != int(fm.group(1)):
        return 'INFRASTRUCTURE_FAILED', report, 'per-file verdict count disagrees with discovery summary'
    report['file_summary'] = dict(discovered=int(fm.group(1)), executed=int(fm.group(2)))
    paths = set()
    for match in specs:
        path, outcome, declared, executed, passed, failed, skipped, dev, dropped, suffix = match.groups()
        if path in paths:
            return 'INFRASTRUCTURE_FAILED', report, 'duplicate per-file identity'
        paths.add(path)
        row = dict(path=path, outcome=outcome, declared_at_least=int(declared), executed=int(executed),
                   passed=int(passed), failed=int(failed), skipped=int(skipped or 0),
                   in_development=int(dev or 0), dropped=int(dropped), degraded=('degraded=' in suffix), details=suffix.strip())
        report['spec_files'].append(row)
        if re.search(r'(?:^|\s)process_error=1(?:\s|$)', suffix):
            return 'INFRASTRUCTURE_FAILED', report, 'spec child process failed after authenticated execution'
        if outcome == 'NOT_RUN' or row['dropped'] or 'timeout=' in suffix or 'inconclusive=' in suffix:
            return 'INFRASTRUCTURE_FAILED', report, 'spec file has unverified, dropped, timed-out, or not-run work'
        if row['declared_at_least'] > row['executed']:
            return 'INFRASTRUCTURE_FAILED', report, 'declared spec work exceeds executed work'
        if row['executed'] != row['passed'] + row['failed'] + row['in_development']:
            return 'INFRASTRUCTURE_FAILED', report, 'spec verdict does not partition executed work'
        if outcome == 'OK' and row['failed'] > 0:
            return 'INFRASTRUCTURE_FAILED', report, 'successful spec verdict contains failed examples'
        if outcome == 'ERROR' and row['failed'] == 0:
            return 'INFRASTRUCTURE_FAILED', report, 'spec file error lacks corresponding failed work'
        if row['executed'] < row['passed'] + row['failed']:
            return 'INFRASTRUCTURE_FAILED', report, 'spec file executed count is below pass/fail outcomes'
    result_suffix = rm.group(6).strip()
    if re.search(r'\b(crashed|terminated|timed out|not run)\b', result_suffix):
        return 'INFRASTRUCTURE_FAILED', report, 'summary reports crashed, terminated, timed-out, or unrun work'
    report['categories'] = dict(spec=dict(total=int(rm.group(1)), passed=int(rm.group(2)), failed=int(rm.group(3)), skipped=int(rm.group(4) or 0), pending=int(rm.group(5) or 0), summary_suffix=result_suffix),
                                spl_doctest=dict(passed=int(sm.group(1)), failed=int(sm.group(2)), skipped=int(sm.group(3))),
                                sdoctest=dict(total=int(dm.group(1)), passed=int(dm.group(2)), failed=int(dm.group(3)), accepted=int(dm.group(4) or 0), skipped=int(dm.group(5)), errors=int(dm.group(6))))
    category = report['categories']
    if category['spec']['total'] != category['spec']['passed'] + category['spec']['failed']:
        return 'INFRASTRUCTURE_FAILED', report, 'spec result total does not equal passed plus failed'
    if sum(r['passed'] for r in report['spec_files']) != category['spec']['passed'] or sum(r['failed'] for r in report['spec_files']) != category['spec']['failed']:
        return 'INFRASTRUCTURE_FAILED', report, 'per-file and aggregate spec counters disagree'
    if category['sdoctest']['total'] != category['sdoctest']['passed'] + category['sdoctest']['failed'] + category['sdoctest']['skipped'] + category['sdoctest']['errors']:
        return 'INFRASTRUCTURE_FAILED', report, 'sdoctest total does not partition into terminal outcomes'
    if exit_code not in (0, 1):
        return 'INFRASTRUCTURE_FAILED', report, 'runner process did not complete normally'
    executed = sum(category[k].get('passed', 0) + category[k].get('failed', 0) for k in ('spec', 'spl_doctest', 'sdoctest'))
    failures = category['spec']['failed'] + category['spl_doctest']['failed'] + category['sdoctest']['failed'] + category['sdoctest']['errors']
    accepted = category['sdoctest']['accepted']
    if executed == 0:
        return 'INFRASTRUCTURE_FAILED', report, 'no assertions or examples executed'
    if exit_code == 0 and failures == 0 and accepted == 0:
        return 'PASS', report, ''
    if exit_code == 1 and failures > 0:
        return 'FAIL', report, 'runner reported test failures; skips and pending remain separate'
    return 'INFRASTRUCTURE_FAILED', report, 'process status conflicts with reported outcomes'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', required=True, type=Path)
    parser.add_argument('--seed-sha256', required=True)
    parser.add_argument('--source-root', required=True, type=Path)
    parser.add_argument('--output-root', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=20)
    parser.add_argument('--worker-memory-mb', type=int, default=0)
    parser.add_argument('--timeout-seconds', type=int, default=7200)
    operation = parser.add_mutually_exclusive_group()
    operation.add_argument('--prepare-only', action='store_true')
    operation.add_argument('--resume-prepared', action='store_true')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 128:
        parser.error('jobs must be 1..128 and match the caller-admitted lane')
    if not 0 <= args.worker_memory_mb <= 1048576:
        parser.error('worker-memory-mb must be 0 (disabled) or 1..1048576 MiB')
    seed, source, output = args.seed.resolve(), args.source_root.resolve(), args.output_root.resolve()
    if digest(seed) != args.seed_sha256:
        parser.error('seed byte identity differs')
    inputs = ['config/simple.test.sdn', 'config/sdoctest.sdn',
              'src/app/test_runner_new/main.spl',
              'src/app/test_runner_new/test_runner_main.spl',
              'src/app/test_daemon/light_protocol.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl',
              'src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl',
              'src/lib/nogc_sync_mut/spec.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_output.spl',
              'src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_files.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_args.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_types.spl',
              'src/lib/nogc_sync_mut/test_runner/test_runner_async.spl',
              'src/lib/nogc_sync_mut/test_runner/worker_memory.spl',
              'src/lib/common/convert.spl']
    pins = {name: digest(source / name) for name in inputs}
    if not args.resume_prepared:
        output.mkdir(parents=True, exist_ok=False)
    elif not output.is_dir() or output.is_symlink():
        parser.error('prepared physical output root unavailable')
    if not 1 <= args.timeout_seconds <= 86400:
        parser.error('timeout-seconds must be 1..86400')
    command = [str(seed), 'test', '--whole', '--parallel', f'--max-workers={args.jobs}',
               '--unstable', '--mode=interpreter', '--format=text']
    if args.worker_memory_mb:
        command.append(f'--worker-memory-mb={args.worker_memory_mb}')
    environment = os.environ.copy()
    environment.pop('SIMPLE_TEST_RUNNER_RUST', None)
    environment.update(SIMPLE_BINARY=str(seed), SIMPLE_RUNTIME=str(seed),
                       SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source / 'src'),
                       SIMPLE_TEST_JOBS=str(args.jobs))
    request = dict(schema='simple-phase1-whole-tests-v1', seed=str(seed),
                   seed_sha256=args.seed_sha256, source_root=str(source),
                   input_hashes=pins, command=command, jobs=args.jobs,
                   worker_memory_mb=args.worker_memory_mb, timeout_seconds=args.timeout_seconds,
                   report_format='text-diagnostic',
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
        status, summary, reason = classify(child.returncode, read_report(output / 'stdout.log'))
    except (ValueError, UnicodeError) as error:
        status, summary, reason = 'INFRASTRUCTURE_FAILED', None, str(error)
    unchanged = digest(seed) == args.seed_sha256 and all(digest(source / name) == sha for name, sha in pins.items())
    if not unchanged:
        status, reason = 'INFRASTRUCTURE_FAILED', 'pinned seed or runner/configuration changed during execution'
    result = dict(schema='simple-phase1-whole-tests-result-v1', status=status,
                  process_exit=child.returncode, elapsed_seconds=time.monotonic()-started,
                  runner_summary=summary, reason=reason, request_sha256=digest(output / 'request.json'),
                  stdout_sha256=digest(output / 'stdout.log'), stderr_sha256=digest(output / 'stderr.log'),
                  coverage_status='NOT_PROVEN: human text summary does not reconcile complete discovered, excluded, or aborted inventory',
                  phase='phase1', qualification='seed-only; not pure-Simple Phase2/product qualification')
    temporary = output / 'result.json.tmp'
    temporary.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    os.replace(temporary, output / 'result.json')
    return 0 if status == 'PASS' else 1 if status == 'FAIL' else 2


if __name__ == '__main__':
    raise SystemExit(main())
