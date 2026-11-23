"""Read-only symbol/RSS observer; executed inside GDB, never compiler code."""
import gdb
import hashlib
import json
import os
from pathlib import Path
import time

config = json.loads(Path(os.environ['UNIT_DIAGNOSTIC_CONFIG']).read_text())
validated = False
active = False
target_pid = 0


def compiler_child():
    pid = gdb.selected_inferior().pid
    if not pid:
        return False
    argv = Path(f'/proc/{pid}/cmdline').read_bytes().decode().split('\0')[:-1]
    if config['required_worker_arg'] not in argv:
        return False
    with Path(f'/proc/{pid}/exe').open('rb') as f:
        digest = hashlib.file_digest(f, 'sha256').hexdigest()
    return digest == config['binary_sha256']


def stop_all(code):
    ids = [str(i.num) for i in gdb.inferiors() if i.pid]
    if ids:
        gdb.execute('kill inferiors '+' '.join(ids))
    gdb.execute(f'quit {code}')


def record(stage, check=False):
    global validated
    pid = gdb.selected_inferior().pid
    status = Path(f'/proc/{pid}/status').read_text()
    row = {'stage': stage, 'time': time.time(), 'pid': pid, 'comparable': active,
           'rss_kib': int(next(x.split()[1] for x in status.splitlines() if x.startswith('VmRSS:')))}
    if check:
        snapshot = Path(config['snapshot'])
        paths = sorted(str(Path(p.read_text().strip()).relative_to(snapshot))
                       for p in (Path(config['queue'])/'owner_picks').rglob('*.pick'))
        validated = paths == config['targets']
        row.update(targets=paths, target_equality=validated, observer_control_only=config.get('observer_control_only', False))
        row['comparable'] = validated
        row['actual_argv'] = Path(f'/proc/{pid}/cmdline').read_bytes().decode().split('\0')[:-1]
    with Path(config['events']).open('a') as f:
        f.write(json.dumps(row)+'\n')
        f.flush()
        os.fsync(f.fileno())
    if check and not validated:
        stop_all(2)


class Returned(gdb.FinishBreakpoint):
    def __init__(self, stage):
        super().__init__(gdb.newest_frame(), internal=True)
        self.stage = stage

    def stop(self):
        if gdb.selected_inferior().pid != target_pid:
            return False
        record(self.stage+':return')
        if self.stage == 'promote' and active and validated:
            # Attribution ends before HIR/MIR/codegen: no product is requested.
            stop_all(0)
        return False


class Entered(gdb.Breakpoint):
    def __init__(self, symbol, stage):
        super().__init__(symbol, internal=True)
        self.stage = stage

    def stop(self):
        global active, target_pid
        if not compiler_child():
            return False
        if self.stage == 'finish' and (config.get('observer_control_only') or list((Path(config['queue'])/'owner_picks').rglob('*.pick'))):
            record(self.stage+':entry', check=True)
            active = validated
            target_pid = gdb.selected_inferior().pid
        else:
            record(self.stage+':entry')
        if active:
            Returned(self.stage)
        return False


gdb.execute('set follow-fork-mode child')
gdb.execute('set detach-on-fork off')
gdb.execute('set schedule-multiple on')
gdb.execute('set breakpoint pending on')
gdb.execute('set startup-with-shell off')
Entered('compiler__hir__hir_lowering__module_surface_registry__ModuleSurfaceBuilder_dot_finish_into', 'finish')
Entered('compiler__hir__hir_lowering__module_surface_registry_index__module_surfaces_freeze', 'freeze')
Entered('compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote_reason', 'promote')
gdb.execute('run')
while any(i.pid for i in gdb.inferiors()):
    if not gdb.selected_inferior().pid:
        live = next(i for i in gdb.inferiors() if i.pid)
        gdb.execute(f'inferior {live.num}')
    gdb.execute('continue')
