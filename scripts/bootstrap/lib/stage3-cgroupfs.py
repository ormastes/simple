#!/usr/bin/env python3
"""Explicit, delegated cgroup-v2 containment for the canonical Stage3 worker.

root-run provisions a fresh private hierarchy and drops uid before running the
canonical coordinator. Other modes operate only on its root-controlled worker
leaf. Neither a fallback to uncapped execution nor a global controller write is
allowed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import signal
import stat
import subprocess
import sys
import time
import uuid

ROOT = Path('/sys/fs/cgroup')
PREFIX = 'simple-bootstrap-stage3.'
MIB = 1024 * 1024


def current_group(pid='self'):
    rows = Path('/proc/' + str(pid) + '/cgroup').read_text().splitlines()
    matches = [r[3:] for r in rows if r.startswith('0::')]
    if len(matches) != 1:
        raise RuntimeError('cgroup v2 membership unavailable')
    return matches[0]


def root_directory(path):
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != 0 or info.st_mode & 0o022:
        raise RuntimeError('cgroup directory is not root-controlled: ' + str(path))


def read_fd(directory, name):
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory)
    try:
        return os.read(fd, 4096).decode().strip()
    finally:
        os.close(fd)


def write_fd(directory, name, value):
    fd = os.open(name, os.O_WRONLY | os.O_NOFOLLOW, dir_fd=directory)
    try:
        os.write(fd, str(value).encode())
    finally:
        os.close(fd)


def validate(group, high, maximum):
    path = Path(group)
    if not re.fullmatch(re.escape(str(ROOT)) + '/' + PREFIX.replace('.', r'\.') + r'[0-9a-f]{32}/worker', group):
        raise RuntimeError('not a private Stage3 worker leaf')
    parent = path.parent
    for directory in (ROOT, parent, parent / 'supervisor', path):
        root_directory(directory)
    if current_group() != '/' + parent.name + '/supervisor':
        raise RuntimeError('coordinator is outside the delegated supervisor leaf')
    parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    leaf_fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        if read_fd(parent_fd, 'cgroup.type') != 'domain' or read_fd(leaf_fd, 'cgroup.type') != 'domain':
            raise RuntimeError('cgroup is not a domain')
        if 'memory' not in read_fd(parent_fd, 'cgroup.subtree_control').split():
            raise RuntimeError('private memory controller is not enabled')
        for name, expected in [('memory.high', high * MIB), ('memory.max', maximum * MIB)]:
            actual = read_fd(leaf_fd, name)
            info = os.stat(name, dir_fd=leaf_fd, follow_symlinks=False)
            if actual != str(expected) or info.st_uid != 0 or info.st_mode & 0o022:
                raise RuntimeError('memory limit is not effective/root-controlled: ' + name)
        for directory, name in [(parent_fd, 'cgroup.procs'), (leaf_fd, 'cgroup.procs'), (leaf_fd, 'cgroup.kill')]:
            info = os.stat(name, dir_fd=directory, follow_symlinks=False)
            if info.st_uid != os.geteuid() or info.st_mode & 0o022:
                raise RuntimeError('delegated file owner/permissions mismatch: ' + name)
        supervisor = parent / 'supervisor' / 'cgroup.procs'
        info = supervisor.lstat()
        if info.st_uid != 0 or info.st_mode & 0o022:
            raise RuntimeError('supervisor membership is not protected')
        if os.geteuid() == 0:
            raise RuntimeError('canonical build must not run as root')
        return leaf_fd, path
    except BaseException:
        os.close(leaf_fd)
        raise
    finally:
        os.close(parent_fd)


def populated(directory):
    value = dict(line.split() for line in read_fd(directory, 'cgroup.events').splitlines()).get('populated')
    if value not in ('0', '1'):
        raise RuntimeError('missing or invalid cgroup populated state')
    return value == '1'


def drain(directory):
    # The pinned directory FD cannot be substituted with another cgroup path.
    write_fd(directory, 'cgroup.kill', 1)
    deadline = time.monotonic() + 5
    while populated(directory) and time.monotonic() < deadline:
        time.sleep(.05)
    if populated(directory):
        raise RuntimeError('owned cgroup remains populated after kernel kill')


def root_run(args):
    if os.geteuid() != 0:
        raise RuntimeError('root-run requires the explicit privileged provisioning invocation')
    user = pwd.getpwnam(args.user)
    if user.pw_uid == 0 or not args.command:
        raise RuntimeError('non-root canonical user and command are required')
    command = args.command[1:] if args.command[0] == '--' else args.command
    if not command:
        raise RuntimeError('empty coordinator command')
    root_directory(ROOT)
    if 'memory' not in (ROOT / 'cgroup.subtree_control').read_text().split():
        raise RuntimeError('enclosing memory controller is not enabled; no global changes permitted')
    parent = ROOT / (PREFIX + uuid.uuid4().hex)
    created = []
    fds = {}
    child = None
    outcome = {'backend': 'cgroupfs', 'root_helper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'root_pid': os.getpid(), 'uid': user.pw_uid, 'high_bytes': args.high * MIB, 'max_bytes': args.maximum * MIB, 'path': str(parent), 'command': command}
    def interrupted(signum, _frame):
        raise InterruptedError('root supervisor signal ' + str(signum))
    try:
        # Cover provisioning and the spawn window, not only child.wait().
        for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(signum, interrupted)
        parent.mkdir(mode=0o755)
        created.append(parent)
        if (parent / 'cgroup.type').read_text().strip() != 'domain':
            raise RuntimeError('fresh parent is not a domain')
        # Enable only this new task-owned hierarchy, never the enclosing root.
        (parent / 'cgroup.subtree_control').write_text('+memory')
        for name in ('supervisor', 'worker'):
            path = parent / name
            path.mkdir(mode=0o755)
            created.append(path)
            fds[name] = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        worker = parent / 'worker'
        for name, value in [('memory.high', args.high * MIB), ('memory.max', args.maximum * MIB), ('memory.oom.group', 1)]:
            write_fd(fds['worker'], name, value)
        for path in (parent / 'cgroup.procs', worker / 'cgroup.procs', worker / 'cgroup.kill'):
            os.chown(path, user.pw_uid, user.pw_gid)
            os.chmod(path, 0o600)
        for directory in created:
            os.chmod(directory, 0o555)
        env = os.environ.copy()
        for name in ('LD_PRELOAD', 'LD_AUDIT', 'PYTHONPATH', 'PYTHONHOME', 'BASH_ENV', 'ENV'):
            env.pop(name, None)
        env.update({'HOME': user.pw_dir, 'USER': user.pw_name, 'LOGNAME': user.pw_name, 'SIMPLE_BOOTSTRAP_STAGE3_CONTAINMENT': 'cgroupfs', 'SIMPLE_BOOTSTRAP_STAGE3_CGROUPFS_WORKER': str(worker), 'SIMPLE_BOOTSTRAP_STAGE3_HEADROOM_MIB': str(args.high), 'SIMPLE_BOOTSTRAP_STAGE3_PROCESS_MAX_MIB': str(args.maximum)})
        # No writable cgroup/escape FDs enter the unprivileged coordinator.
        def enter():
            write_fd(fds['supervisor'], 'cgroup.procs', os.getpid())
            os.initgroups(user.pw_name, user.pw_gid)
            os.setgid(user.pw_gid)
            os.setuid(user.pw_uid)
        child = subprocess.Popen(command, env=env, preexec_fn=enter, close_fds=True, start_new_session=True)
        outcome['coordinator_pid'] = child.pid
        outcome['exit_code'] = child.wait()
    except BaseException as error:
        outcome['error'] = str(error)
        outcome['exit_code'] = 125
    finally:
        for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(signum, signal.SIG_IGN)
        errors = []
        # A signal may arrive between mkdir/open and Python recording its
        # result. Recover only this fresh UUID's fixed, root-controlled leaves.
        if parent.exists():
            created = [parent]
            for name in ('supervisor', 'worker'):
                path = parent / name
                if path.exists():
                    try:
                        root_directory(path)
                        created.append(path)
                        if name not in fds:
                            fds[name] = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                    except BaseException as error:
                        errors.append(str(error))
        for name in ('worker', 'supervisor'):
            if name in fds:
                try:
                    drain(fds[name])
                    outcome[name + '_populated_after_cleanup'] = False
                except BaseException as error:
                    errors.append(str(error))
                finally:
                    os.close(fds[name])
        if child is not None:
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                errors.append('coordinator did not terminate after cgroup cleanup')
        if not errors:
            for path in reversed(created):
                try:
                    path.rmdir()
                except OSError as error:
                    errors.append(str(error))
        outcome['cleanup_errors'] = errors
        if errors:
            outcome['exit_code'] = 125
        if args.receipt:
            # All privileged work is complete. Evidence follows ordinary user
            # permissions and an existing path cannot be overwritten/followed.
            os.setgroups([])
            os.setgid(user.pw_gid)
            os.setuid(user.pw_uid)
            with open(args.receipt, 'x') as receipt:
                receipt.write(json.dumps(outcome, indent=2) + '\n')
        print(json.dumps(outcome), flush=True)
    return outcome['exit_code'] if outcome['exit_code'] >= 0 else 128 - outcome['exit_code']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['root-run', 'validate', 'join', 'stop', 'inactive'])
    parser.add_argument('--group')
    parser.add_argument('--high', type=int, required=True)
    parser.add_argument('--maximum', type=int, required=True)
    parser.add_argument('--user', default='ormastes')
    parser.add_argument('--receipt')
    args, command = parser.parse_known_args()
    args.command = command
    if args.high <= 0 or args.maximum <= 0:
        raise RuntimeError('positive memory limits required')
    if args.mode == 'root-run':
        return root_run(args)
    if not args.group:
        raise RuntimeError('worker path required')
    directory, path = validate(args.group, args.high, args.maximum)
    try:
        if args.mode == 'validate':
            print('containment_backend=cgroupfs')
            print('containment_worker_path=' + str(path))
            print('containment_parent_path=' + str(path.parent))
            print('containment_run_identity=' + path.parent.name)
            print('containment_helper_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
            print('containment_memory_high_bytes=' + read_fd(directory, 'memory.high'))
            print('containment_memory_max_bytes=' + read_fd(directory, 'memory.max'))
        elif args.mode == 'join':
            if populated(directory):
                raise RuntimeError('worker leaf is not fresh/empty')
            write_fd(directory, 'cgroup.procs', os.getpid())
            if current_group() != '/' + path.parent.name + '/worker':
                raise RuntimeError('self migration did not take effect')
            command = command[1:] if command and command[0] == '--' else command
            if not command:
                raise RuntimeError('empty worker command')
            os.execvp(command[0], command)
        elif args.mode == 'stop':
            drain(directory)
        elif populated(directory):
            return 125
    finally:
        os.close(directory)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except BaseException as error:
        if isinstance(error, SystemExit):
            raise
        print('stage3 cgroupfs: ' + str(error), file=sys.stderr)
        sys.exit(125)
