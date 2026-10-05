"""Diagnostic executable admission; RSS estimates are not enforced memory limits."""
import ctypes, hashlib, json, sys
GIB=1024**3

def available_commit_bytes():
    if sys.platform!='win32':raise RuntimeError('Windows available-commit admission required')
    class PERF(ctypes.Structure):
        _fields_=[('cb',ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in ('CommitTotal','CommitLimit','CommitPeak','PhysicalTotal','PhysicalAvailable','SystemCache','KernelTotal','KernelPaged','KernelNonpaged','PageSize')]+[(n,ctypes.c_ulong) for n in ('HandleCount','ProcessCount','ThreadCount')]
    p=PERF();p.cb=ctypes.sizeof(p)
    if not ctypes.windll.psapi.GetPerformanceInfo(ctypes.byref(p),p.cb):raise ctypes.WinError()
    return int(p.CommitLimit-p.CommitTotal)*int(p.PageSize)

def may_start(active, observations, free_commit, config):
    maximum=config['max_executables'];assert 1<=maximum<=20 and active>=0
    if active>=maximum:return False
    # With no measurement, admit one task only. Unknown memory never means20.
    if not observations:return active==0 and free_commit>=config['headroom_bytes']
    estimate=max(config['minimum_estimate_bytes'],max(observations)*config['rss_to_commit_safety_factor'])
    ramp=min(maximum,len(observations)+1)
    return active<ramp and free_commit>=config['headroom_bytes']+estimate*(active+1)

def closed_rss(fields):
    return fields.get('quiescent')=='1' and fields.get('observer_errors')=='0' and fields.get('status') in ('complete','interrupted')

def outcome(exit_code,result,receipts):
    # A crash without process-tree closure stops admission, never assumes reap.
    if not result or result.get('compile_exit') is None:return 'BLOCKED_UNVERIFIED_CHILD'
    if not receipts or not all(closed_rss(r) for r in receipts):return 'BLOCKED_UNVERIFIED_CHILD'
    if exit_code!=0 and (result.get('terminal_status','').startswith('LINKED') or result.get('sanity_pass') is True):return 'BLOCKED_CHILD_RESULT_MISMATCH'
    return 'CONTINUE'

def identity(target):
    fields={k:target[k] for k in ('producer_sha256','source','backend','entry','options')}
    return hashlib.sha256(json.dumps(fields,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def reusable_success(saved,target,binary_sha):
    return saved.get('identity')==identity(target) and saved.get('binary_sha256')==binary_sha and saved.get('binary_linked') is True and saved.get('sanity_pass') is True and saved.get('closure')=='CLOSED'
