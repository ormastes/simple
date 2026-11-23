"""Read-only symbol/RSS observer; executed inside GDB, never compiler code."""
import gdb
import json
import os
from pathlib import Path
import time

config = json.loads(Path(os.environ['UNIT_DIAGNOSTIC_CONFIG']).read_text())
validated = False
active = False


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
        row.update(targets=paths, target_equality=validated)
        row['comparable'] = validated
        row['actual_argv'] = Path(f'/proc/{pid}/cmdline').read_bytes().decode().split('\0')[:-1]
    with Path(config['events']).open('a') as f:
        f.write(json.dumps(row)+'\n')
        f.flush()
        os.fsync(f.fileno())
    if check and not validated:
        gdb.execute('kill')
        gdb.execute('quit 2')


class Returned(gdb.FinishBreakpoint):
    def __init__(self, stage):
        super().__init__(gdb.newest_frame(), internal=True)
        self.stage = stage

    def stop(self):
        record(self.stage+':return')
        if self.stage == 'promote' and active and validated:
            # Attribution ends before HIR/MIR/codegen: no product is requested.
            gdb.execute('kill')
            gdb.execute('quit 0')
        return False


class Entered(gdb.Breakpoint):
    def __init__(self, symbol, stage):
        super().__init__(symbol, internal=True)
        self.stage = stage

    def stop(self):
        global active
        if self.stage == 'finish' and list((Path(config['queue'])/'owner_picks').rglob('*.pick')):
            record(self.stage+':entry', check=True)
            active = validated
        else:
            record(self.stage+':entry')
        if active:
            Returned(self.stage)
        return False


Entered('compiler__hir__hir_lowering__module_surface_registry__ModuleSurfaceBuilder_dot_finish_into', 'finish')
Entered('compiler__hir__hir_lowering__module_surface_registry_index__module_surfaces_freeze', 'freeze')
Entered('compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote_reason', 'promote')
gdb.execute('run')
