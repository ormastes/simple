"""Windows diagnostic wall drain with immutable workload/argv authority binding.

Never launches a compiler or terminates its coordinator or outer guard. A worker
cutoff is deliberately incomplete diagnostic work, even when captured logs are
complete. The existing finite Job owner remains responsible for cleanup.
"""
import ctypes as C
from ctypes import wintypes as W
import datetime as D
import hashlib
import json
import os
import re
import time
from pathlib import Path

K = C.WinDLL('kernel32', use_last_error=True)
K.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
K.OpenProcess.restype = W.HANDLE
K.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]
K.CreateToolhelp32Snapshot.restype = W.HANDLE
K.CloseHandle.argtypes = [W.HANDLE]
K.GetProcessTimes.argtypes = [W.HANDLE] + [C.POINTER(W.FILETIME)] * 4
K.QueryFullProcessImageNameW.argtypes = [W.HANDLE, W.DWORD, W.LPWSTR, C.POINTER(W.DWORD)]
K.WaitForSingleObject.argtypes = [W.HANDLE, W.DWORD]
K.TerminateProcess.argtypes = [W.HANDLE, W.UINT]
K.GetExitCodeProcess.argtypes = [W.HANDLE, C.POINTER(W.DWORD)]

class Entry(C.Structure):
    _fields_ = [('size', W.DWORD), ('usage', W.DWORD), ('pid', W.DWORD),
                ('heap', C.c_size_t), ('module', W.DWORD), ('threads', W.DWORD),
                ('parent', W.DWORD), ('priority', W.LONG), ('flags', W.DWORD),
                ('exe', W.WCHAR * 260)]

K.Process32FirstW.argtypes = [W.HANDLE, C.POINTER(Entry)]
K.Process32NextW.argtypes = [W.HANDLE, C.POINTER(Entry)]

def utc_ns(value):
    """Require one-line UTC ISO timestamp, retaining all seven CIM decimal digits."""
    m = re.fullmatch(r'(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(?:\.(\d{1,9}))?Z', value)
    if not m:
        raise ValueError('invalid single-line UTC timestamp')
    stamp = D.datetime.strptime(m[1], '%Y-%m-%dT%H:%M:%S').replace(tzinfo=D.timezone.utc)
    return int(stamp.timestamp()) * 10**9 + int((m[2] or '').ljust(9, '0'))

def read_sdn(path):
    result = {}
    for line in Path(path).read_text(encoding='utf-8-sig').splitlines():
        if not line or line.startswith('#'):
            continue
        m = re.fullmatch(r'([a-z][a-z0-9_]*): ([^\r\n]+)', line)
        if not m or m[1] in result:
            raise ValueError('invalid/duplicate flat SDN field')
        result[m[1]] = m[2]
    return result

def validate_launch_binding(plan):
    """Bind actual canonical collector envelope; never create a worker packet."""
    for prefix in ('workload_spec', 'launch_argv'):
        path = Path(plan[prefix + '_path'])
        if hashlib.sha256(path.read_bytes()).hexdigest() != plan[prefix + '_sha256']:
            raise ValueError(prefix + ' authority drift')
    text = Path(plan['launch_argv_path']).read_text(encoding='utf-8-sig')
    body = text.split('argv: [\n', 1)[1].split('\n]', 1)[0]
    args = [json.loads(line.strip().rstrip(',')) for line in body.splitlines() if line.strip()]
    outer = [arg.split('=', 1)[1] for arg in args if arg.startswith('--timeout-seconds=')]
    def single_arg(name):
        positions = [i for i, arg in enumerate(args) if arg == name]
        if len(positions) != 1 or positions[0] + 1 >= len(args):
            raise ValueError('ambiguous collector argument ' + name)
        return args[positions[0] + 1]
    if len(outer) != 1 or not outer[0].isdigit() or not 0 < int(outer[0]) <= 7200:
        raise ValueError('missing or invalid finite outer wall')
    if single_arg('--timeout-seconds') != outer[0] or plan['outer_wall_seconds'] != outer[0]:
        raise ValueError('outer/collector wall mismatch')
    if single_arg('--max-bytes') != '8388608' or single_arg('--root-exit-policy') != 'wait-job':
        raise ValueError('canonical bounded collector policy required')
    if args.count('--rss-cap-mode=monitor') != 1:
        raise ValueError('diagnostic monitor-only outer guard required')
    if not any(os.path.normcase(os.path.normpath(arg)) == os.path.normcase(os.path.normpath(plan['parent_image'])) for arg in args):
        raise ValueError('bound parent image missing from launch argv')

def clock_budget(plan, now_ns=None, now_mono=None):
    outer = utc_ns(plan['outer_deadline_utc'])
    target = utc_ns(plan['drain_target_utc'])
    now_ns = time.time_ns() if now_ns is None else now_ns
    now_mono = time.monotonic() if now_mono is None else now_mono
    if outer - target < 30 * 10**9 or target <= now_ns:
        raise ValueError('requires future drain target and at least30 seconds parent grace')
    return (now_mono + (target - now_ns) / 10**9,
            now_mono + (outer - now_ns) / 10**9)

def deadline(plan, now_ns=None, now_mono=None):
    return clock_budget(plan, now_ns, now_mono)[0]

def validate_guard_deadline(plan, created_filetime):
    guard_start_ns = (created_filetime - 116444736000000000) * 100
    if utc_ns(plan['outer_deadline_utc']) > guard_start_ns + int(plan['outer_wall_seconds']) * 10**9:
        raise ValueError('plan deadline exceeds bound native guard lifetime budget')

def require_grace(plan, outer_mono, now_ns=None, now_mono=None):
    now_ns = time.time_ns() if now_ns is None else now_ns
    now_mono = time.monotonic() if now_mono is None else now_mono
    if outer_mono - now_mono < 25 or utc_ns(plan['outer_deadline_utc']) - now_ns < 25 * 10**9:
        raise ValueError('insufficient remaining parent grace')

def wait_for_target(target, live, clock=time.monotonic, sleep=time.sleep):
    while clock() < target:
        if not live():
            raise ValueError('process terminal before drain; no action')
        remaining = target - clock()
        if remaining > 0:
            sleep(min(.1, remaining))

def snapshot():
    h = K.CreateToolhelp32Snapshot(2, 0)
    if h == C.c_void_p(-1).value:
        raise C.WinError(C.get_last_error())
    try:
        e = Entry(); e.size = C.sizeof(e); rows = {}
        ok = K.Process32FirstW(h, C.byref(e))
        while ok:
            rows[e.pid] = e.parent
            ok = K.Process32NextW(h, C.byref(e))
        if C.get_last_error() != 18:  # ERROR_NO_MORE_FILES is the only complete snapshot end.
            raise C.WinError(C.get_last_error())
        return rows
    finally:
        K.CloseHandle(h)

class Process:
    def __init__(self, pid, terminate=False):
        self.pid = int(pid)
        self.h = K.OpenProcess(0x100000 | 0x1000 | (1 if terminate else 0), False, self.pid)
        if not self.h:
            raise C.WinError(C.get_last_error())
        try:
            ts = [W.FILETIME() for _ in range(4)]
            if not K.GetProcessTimes(self.h, *[C.byref(x) for x in ts]):
                raise C.WinError(C.get_last_error())
            self.created = ts[0].dwHighDateTime << 32 | ts[0].dwLowDateTime
            size = W.DWORD(32768); buf = C.create_unicode_buffer(size.value)
            if not K.QueryFullProcessImageNameW(self.h, 0, buf, C.byref(size)):
                raise C.WinError(C.get_last_error())
            self.image = str(Path(buf.value).resolve())
        except BaseException:
            self.close(); raise
    def close(self):
        if self.h:
            K.CloseHandle(self.h); self.h = None
    def live(self):
        return K.WaitForSingleObject(self.h, 0) == 258

def identity(proc):
    return {'pid': str(proc.pid), 'created_filetime': str(proc.created),
            'image': proc.image, 'sha256': hashlib.sha256(Path(proc.image).read_bytes()).hexdigest()}

def validate_scope(plan, handles, rows, chain=None):
    guard, parent, worker = handles
    for name, proc in zip(('guard', 'parent', 'worker'), handles):
        actual = identity(proc)
        if any(str(plan[name + '_' + key]) != value for key, value in actual.items()):
            raise ValueError(name + ' identity mismatch')
        if not proc.live():
            raise ValueError(name + ' already terminal')
    if len({x.pid for x in handles}) != 3 or rows.get(worker.pid) != parent.pid:
        raise ValueError('worker must be distinct immediate child of bound parent')
    if worker.pid in rows.values():
        raise ValueError('worker has descendants: inherited pipe holders possible')
    seen = set(); current = parent.pid
    child = parent
    while current != guard.pid:
        if current in seen or current not in rows:
            raise ValueError('parent not beneath bound guard')
        seen.add(current); current = rows[current]
        if chain is not None:
            ancestor = chain.get(current)
            if ancestor is None or not ancestor.live() or ancestor.created > child.created:
                raise ValueError('intermediate ancestry identity or creation order mismatch')
            child = ancestor
    if not guard.created <= parent.created <= worker.created:
        raise ValueError('creation order mismatch')

def drain(plan, receipt, wait_target=True, plan_path=None):
    """Caller supplies genuine existing guard/parent/worker. Stop ONLY held worker handle."""
    if plan['classification'] != 'diagnostic-wall-drain-not-RSS' or plan['rss_enforcement'] != 'disabled':
        raise ValueError('diagnostic/no-RSS policy required')
    validate_launch_binding(plan)
    target, outer_mono = clock_budget(plan)
    handles = []
    try:
        for name in ('guard', 'parent', 'worker'):
            handles.append(Process(plan[name + '_pid'], name == 'worker'))
        validate_guard_deadline(plan, handles[0].created)
        rows = snapshot()
        validate_scope(plan, handles, rows)
        chain = {handles[0].pid: handles[0], handles[1].pid: handles[1]}
        current = handles[1].pid
        while current != handles[0].pid:
            current = rows[current]
            if current not in chain:
                ancestor = Process(current)
                handles.append(ancestor); chain[current] = ancestor
        bound = handles[:3]
        validate_scope(plan, bound, snapshot(), chain)
        if wait_target:
            wait_for_target(target, lambda: all(p.live() for p in handles))
        require_grace(plan, outer_mono)
        validate_scope(plan, bound, snapshot(), chain)
        plan_bytes = Path(plan_path).read_bytes() if plan_path else ''.join(k+': '+v+'\n' for k,v in sorted(plan.items())).encode()
        if plan_path and read_sdn(plan_path) != plan:
            raise ValueError('plan file changed')
        record = ('schema: owned-worker-drain-action-v2\nclassification: deliberate-diagnostic-wall-drain\n'
                  'plan_sha256: '+hashlib.sha256(plan_bytes).hexdigest()+'\nhelper_sha256: '+hashlib.sha256(Path(__file__).read_bytes()).hexdigest()+'\n'
                  + ''.join(name+'_'+key+': '+value+'\n' for name,p in zip(('guard','parent','worker'),bound) for key,value in identity(p).items())
                  + 'parent_terminated: false\nguard_terminated: false\nrss_enforcement: disabled\nouter_deadline_changed: false\ncapture_complete: pending-parent-and-collector-terminal-proof\n')
        # Only this verified worker handle has PROCESS_TERMINATE rights.
        with Path(receipt).open('x', encoding='utf-8') as out:
            out.write(record+'action_state: reserved\n'); out.flush(); os.fsync(out.fileno())
            require_grace(plan, outer_mono)
            validate_scope(plan, bound, snapshot(), chain)
            validate_launch_binding(plan)
            out.write('action_utc: '+D.datetime.now(D.timezone.utc).isoformat().replace('+00:00','Z')+'\n'); out.flush(); os.fsync(out.fileno())
            require_grace(plan, outer_mono)
            if not K.TerminateProcess(bound[2].h, 124):
                out.write('action_result: failed\nwinerror: '+str(C.get_last_error())+'\n'); out.flush(); os.fsync(out.fileno())
                raise C.WinError(C.get_last_error())
            ended = K.WaitForSingleObject(bound[2].h, 5000) == 0
            code = W.DWORD()
            if not K.GetExitCodeProcess(bound[2].h, C.byref(code)):
                raise C.WinError(C.get_last_error())
            out.write('action_result: terminated-worker-only\nworker_terminal: '+str(ended).lower()+'\nworker_exit_code: '+str(code.value)+'\n'); out.flush(); os.fsync(out.fileno())
        return ended
    finally:
        for proc in handles:
            proc.close()

if __name__ == '__main__':
    import sys
    if len(sys.argv) != 6 or sys.argv[1] != '--execute-reviewed-plan':
        raise SystemExit('usage: --execute-reviewed-plan PLAN.sdn ACTION.sdn PLAN_SHA256 HELPER_SHA256')
    if hashlib.sha256(Path(sys.argv[2]).read_bytes()).hexdigest() != sys.argv[4] or hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != sys.argv[5]:
        raise SystemExit('reviewed plan/helper hash mismatch')
    drain(read_sdn(sys.argv[2]), sys.argv[3], plan_path=sys.argv[2])
