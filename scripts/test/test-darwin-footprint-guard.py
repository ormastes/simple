#!/usr/bin/env python3
"""Small policy-helper tests; no language compiler/runtime/bootstrap build."""
import argparse
import os
from pathlib import Path
import shlex
import subprocess
import sys


def read_receipt(path):
    rows = {}
    for line in path.read_text().splitlines():
        key, value = line.split('=', 1)
        assert key not in rows, key
        rows[key] = value
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--case', action='append', choices=['legacy', 'success', 'aggregate', 'drain', 'query_failure'])
    args = parser.parse_args()
    if sys.platform != 'darwin':
        print('UNSUPPORTED: Darwin physical-footprint fixture was not executed')
        return 77
    root = Path(__file__).resolve().parents[2]
    out = Path(args.output).resolve()
    out.mkdir()
    guard = root / 'scripts/resource/process-tree-rss-watchdog.pl'
    compiler = '/usr/bin/cc'
    source = out / 'small-memory.c'
    source.write_text(r'''
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <libproc.h>
static volatile sig_atomic_t terminated;
static void mark_term(int sig) { (void)sig; terminated = 1; }
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (!strcmp(argv[1], "drain")) {
        signal(SIGTERM, mark_term);
        while (!terminated) usleep(10000);
    }
    volatile unsigned char *data = malloc(16 * 1024 * 1024);
    if (!data) return 3;
    for (size_t i = 0; i < 16 * 1024 * 1024; i += 4096) data[i] = 1;
    struct rusage_info_v4 usage = {0};
    if (proc_pid_rusage(getpid(), RUSAGE_INFO_V4, (rusage_info_t *)&usage)) return 4;
    printf("MEMBER_FOOTPRINT_KIB=%llu\n", (unsigned long long)(usage.ri_phys_footprint / 1024));
    fflush(stdout);
    for (;;) usleep(10000);
}
''')
    payload = out / 'small-memory'
    subprocess.run([compiler, '-O2', str(source), '-o', str(payload)], check=True)
    # Fault injection uses the pre-existing trusted-CC seam only in this test.
    # No production observer/parser or hash validation is weakened.
    fault_cc = out / 'fault-cc.py'
    fault_cc.write_text('#!/usr/bin/python3\n' + r'''
import os, sys
from pathlib import Path
args = sys.argv[1:]
for i, arg in enumerate(args):
    if arg.endswith('/macos-process-observer.c'):
        source = Path(arg).read_text()
        assert source.count('n = proc_pid_rusage(') == 1
        source = source.replace('n = proc_pid_rusage(', 'n = fixture_failed_rusage(')
        marker = '#include <mach/mach_time.h>'
        assert source.count(marker) == 1
        source = source.replace(marker, marker + '\nstatic int fixture_failed_rusage(int pid, int flavor, rusage_info_t *value) { (void)pid; (void)flavor; (void)value; errno = EIO; return -1; }\n')
        target = Path(sys.argv[0]).parent / 'fault-observer.c'
        target.write_text(source)
        args[i] = str(target)
        break
os.execv('/usr/bin/cc', ['/usr/bin/cc'] + args)
''')
    fault_cc.chmod(0o700)
    base_env = os.environ.copy()
    base_env.pop('SIMPLE_BOOTSTRAP_PROCESS_TREE_PHYS_FOOTPRINT_CAP_KIB', None)
    inherited = bool(base_env.get('SIMPLE_BOOTSTRAP_SESSION_ID'))
    mode = 'inherit' if inherited else 'new'

    def run_case(name, command, cap=None, fault=False, timeout=10, grace=1):
        directory = out / name
        directory.mkdir()
        env = base_env.copy()
        env['CC'] = str(fault_cc) if fault else compiler
        receipt = directory / 'guard.env'
        argv = ['perl', str(guard), '--session-mode=' + mode,
                '--scope-group=1', '--max-rss-kib=262144', '--interval-ms=20',
                '--timeout-seconds=' + str(timeout), '--term-grace-seconds=' + str(grace),
                '--receipt=' + str(receipt)]
        if cap is not None:
            argv.append('--max-phys-footprint-kib=' + str(cap))
        with (directory / 'run.log').open('w') as log:
            result = subprocess.run(argv + ['--'] + command, env=env,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=35)
        rows = read_receipt(receipt)
        assert rows['quiescent'] == '1', rows
        return result.returncode, rows, (directory / 'run.log').read_text()

    executed = passed = 0

    def check(name, operation):
        nonlocal executed, passed
        executed += 1
        try:
            operation()
        except Exception as error:
            print('FAIL', name, str(error), flush=True)
        else:
            passed += 1
            print('PASS', name, flush=True)

    def legacy():
        raw, rows, _ = run_case('legacy', ['/usr/bin/true'], fault=True)
        assert raw == 0 and rows['status'] == 'complete', rows
        assert rows['max_rss_kib'] == '262144'
        assert rows['phys_footprint_cap_enforced'] == '0'
        assert rows['phys_footprint_metric'] == 'disabled'

    def success():
        raw, rows, _ = run_case('success', ['/usr/bin/true'], cap=65536)
        assert raw == 0 and rows['status'] == 'complete', rows
        assert rows['max_rss_kib'] == '262144'
        assert rows['max_phys_footprint_kib'] == '65536'
        assert rows['phys_footprint_cap_enforced'] == '1'
        assert int(rows['peak_phys_footprint_kib']) > 0

    def aggregate():
        command = shlex.quote(str(payload)) + ' allocate & ' + shlex.quote(str(payload)) + ' allocate & wait'
        raw, rows, log = run_case('aggregate', ['/bin/sh', '-c', command], cap=24576)
        assert raw == 88 and rows['status'] == 'phys-footprint-cap-exceeded', rows
        assert int(rows['peak_phys_footprint_kib']) >= 24576
        assert int(rows['peak_rss_kib']) < 262144
        assert int(rows['peak_single_phys_footprint_kib']) < 24576, rows

    def drain():
        raw, rows, _ = run_case('drain', [str(payload), 'drain'], cap=8192, timeout=1, grace=5)
        assert raw == 88 and rows['status'] == 'phys-footprint-cap-exceeded', rows
        assert int(rows['peak_phys_footprint_kib']) >= 8192
        assert int(rows['peak_rss_kib']) < 262144

    def query_failure():
        marker = out / 'must-not-execute'
        raw, rows, _ = run_case('query-failure', ['/usr/bin/touch', str(marker)], cap=65536, fault=True)
        assert raw == 89 and rows['status'] == 'rss-measurement-failed', rows
        assert not marker.exists()
        assert rows['phys_footprint_samples'] == '0'
        assert rows['peak_phys_footprint_kib'] == 'unavailable'

    cases = [('legacy', 'legacy RSS protocol does not query footprint', legacy),
             ('success', 'explicit current-footprint success keeps RSS separate', success),
             ('aggregate', 'two live members breach summed footprint below RSS cap', aggregate),
             ('drain', 'footprint is enforced during TERM drain', drain),
             ('query_failure', 'live rusage failure refuses payload execution', query_failure)]
    for key, description, operation in cases:
        if args.case is None or key in args.case:
            check(description, operation)
    print(f'TEST_RESULT executed={executed} passed={passed} failed={executed-passed} skipped=0', flush=True)
    return 0 if passed == executed else 1


if __name__ == '__main__':
    sys.exit(main())
