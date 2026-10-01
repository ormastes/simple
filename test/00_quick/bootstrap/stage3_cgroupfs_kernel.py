#!/usr/bin/env python3
"""Real Linux kernel regression; requires explicit root provisioning invocation.

This exercises containment, not compiler admission or a bootstrap PASS.
"""
import os
import json
from pathlib import Path
import signal
import subprocess
import sys
import time


def terminal_cases(helper, evidence):
    evidence = Path(evidence)
    evidence.mkdir()
    os.chown(evidence, 1000, 1000)
    for name, command, expected in (
        ('allocation-limit', ['/usr/bin/python3', '-I', __file__, 'cap-coordinator', helper], 0),
        ('launch-failure', ['/does-not-exist/stage3-worker'], 125),
        ('signal-cleanup', ['/usr/bin/python3', '-I', __file__, 'signal-coordinator', helper, str(evidence / 'ready')], 125),
    ):
        receipt = evidence / (name + '.json')
        high = '256' if name == 'allocation-limit' else '64'
        launch = ['/usr/bin/python3', '-I', helper, 'root-run', '--high', high, '--maximum', '128', '--receipt', str(receipt), '--'] + command
        with open(evidence / (name + '.log'), 'w') as log:
            process = subprocess.Popen(launch, stdout=log, stderr=subprocess.STDOUT)
            try:
                if name == 'signal-cleanup':
                    deadline = time.monotonic() + 10
                    while not (evidence / 'ready').exists():
                        assert process.poll() is None, 'coordinator ended before signal test'
                        assert time.monotonic() < deadline, 'coordinator startup timeout'
                        time.sleep(.05)
                    process.send_signal(signal.SIGTERM)
                assert process.wait(timeout=15) == expected, name
            finally:
                if process.poll() is None:
                    process.terminate()
                    process.wait(timeout=10)
        result = json.loads(receipt.read_text())
        assert result['cleanup_errors'] == [], result
        assert result['worker_populated_after_cleanup'] is False
        assert result['supervisor_populated_after_cleanup'] is False
        assert not Path(result['path']).exists()
        print(name + '=PASS', flush=True)


def denied(path, value):
    try:
        with open(path, 'w') as output:
            output.write(value)
    except OSError:
        return
    raise AssertionError('protected write succeeded: ' + str(path))


def main():
    if sys.argv[1] == 'terminal-cases':
        terminal_cases(sys.argv[2], sys.argv[3])
        return
    group = Path(os.environ['SIMPLE_BOOTSTRAP_STAGE3_CGROUPFS_WORKER'])
    if sys.argv[1] == 'cap-worker':
        allocation = bytearray(256 * 1024 * 1024)
        # Fault every page; zero-filled anonymous mappings can remain lazy.
        for offset in range(0, len(allocation), 4096):
            allocation[offset] = 1
        assert int((group / 'memory.current').read_text()) <= 128 * 1024 * 1024
        return
    if sys.argv[1] in ('cap-coordinator', 'signal-coordinator'):
        args = ['/usr/bin/python3', '-I', sys.argv[2], 'join', '--group', str(group), '--high', os.environ['SIMPLE_BOOTSTRAP_STAGE3_HEADROOM_MIB'], '--maximum', '128', '--']
        if sys.argv[1] == 'cap-coordinator':
            child = subprocess.run(args + ['/usr/bin/python3', '-I', __file__, 'cap-worker'], timeout=10)
            assert child.returncode in (0, -signal.SIGKILL), child.returncode
            events = dict(row.split() for row in (group / 'memory.events').read_text().splitlines())
            assert int(events['max']) >= 1, events
            if child.returncode == -signal.SIGKILL:
                assert int(events['oom_kill']) >= 1, events
            print('enforced_cap_events=' + json.dumps(events), flush=True)
            return
        child = subprocess.Popen(args + ['/bin/sleep', '120'])
        deadline = time.monotonic() + 5
        while (group / 'cgroup.events').read_text().find('populated 1') < 0:
            assert child.poll() is None
            assert time.monotonic() < deadline
            time.sleep(.05)
        Path(sys.argv[3]).touch()
        time.sleep(120)
        return
    assert os.getuid() == os.geteuid() != 0
    assert os.environ['HOME'] == '/home/ormastes'
    assert not any(name in os.environ for name in ('LD_PRELOAD', 'PYTHONPATH', 'BASH_ENV'))
    status = dict(row.split(':', 1) for row in Path('/proc/self/status').read_text().splitlines() if ':' in row)
    assert int(status['CapEff'].strip(), 16) == 0
    for descriptor in Path('/proc/self/fd').iterdir():
        try:
            target = os.readlink(descriptor)
        except OSError:
            continue
        assert not target.startswith('/sys/fs/cgroup'), target
    denied(group / 'memory.max', 'max')
    denied(group / 'cgroup.subtree_control', '+memory')
    denied(group / 'cgroup.threads', str(os.getpid()))
    denied(group.parent / 'supervisor' / 'cgroup.procs', str(os.getpid()))
    denied(Path('/sys/fs/cgroup/cgroup.procs'), str(os.getpid()))
    if sys.argv[1] == 'worker':
        expected = '0::/' + group.parent.name + '/worker'
        assert Path('/proc/self/cgroup').read_text().strip() == expected
        assert (group / 'memory.high').read_text().strip() == str(64 * 1024 * 1024)
        assert (group / 'memory.max').read_text().strip() == str(128 * 1024 * 1024)
        denied(group.parent / 'cgroup.procs', str(os.getpid()))
        child = subprocess.Popen(['/bin/sleep', '120'])
        print('owned_descendant_pid=' + str(child.pid), flush=True)
        return
    helper = sys.argv[2]
    args = ['/usr/bin/python3', '-I', helper]
    limits = ['--group', str(group), '--high', '64', '--maximum', '128']
    subprocess.run(args + ['validate'] + limits, check=True)
    subprocess.run(args + ['join'] + limits + ['--', '/usr/bin/python3', '-I', __file__, 'worker'], check=True)
    subprocess.run(args + ['stop'] + limits, check=True)
    subprocess.run(args + ['inactive'] + limits, check=True)
    print('KERNEL_CONTAINMENT_PASS', flush=True)


if __name__ == '__main__':
    main()
