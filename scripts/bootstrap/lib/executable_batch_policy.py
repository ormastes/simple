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

def request_environment(request, inherited):
    return {**inherited, **request.get('environment', {})}

def preflight_invocation(request, inherited):
    return (request.get('preflight_command', request['command'] + ['--preflight']),
            request['cwd'], request_environment(request, inherited))

def validate_owned_ancestry(config, launch, reservation, request, rows, batch_pid,
                            runner_path, packet_path, hash_file):
    """Reject stale receipts and PID reuse; metadata comes from a pinned observer."""
    import datetime
    import pathlib
    import re
    def path(value):
        return str(pathlib.Path(value).resolve()).replace('\\', '/').casefold()
    owner = int(reservation['owner_pid'])
    collector = int(launch['collector_pid'])
    assert launch['owner_pid'] == owner and owner != collector
    assert launch['threads'] == reservation['threads'] == request['threads'] == 20
    assert reservation['schema'] == 'diagnostic-downstream-reservation/1'
    assert reservation['total_job_budget'] == config['global_job_budget']
    assert path(pathlib.Path(launch['reservation']).parent) == path(config['admission_root'])
    assert path(reservation['receipt_path']) == path(config['parent_collector_receipt'])
    assert hash_file(launch['request']) == launch['request_sha256']
    assert request['files']['config.json'] == hash_file(pathlib.Path(packet_path)/'config.json')
    helper = config['collector']
    assert pathlib.Path(helper['path']).is_absolute(), 'Collector pin requires an absolute path'
    assert hash_file(helper['path']) == helper['sha256'] == reservation['helper_sha256']
    tokens = [path(x) for x in request['command']]
    assert path(runner_path) in tokens and path(packet_path) in tokens
    processes = {int(row['pid']): row for row in rows}
    assert owner in processes, 'Reservation owner is no longer live'
    assert processes[owner]['start_utc'] == reservation['owner_start_utc'], 'Owner PID was reused'
    current = int(batch_pid)
    seen = set()
    found_collector = False
    for _ in range(32):
        assert current in processes and current not in seen, 'Incomplete or cyclic ancestry'
        row = processes[current]
        seen.add(current)
        if current == collector:
            command = row['command_line'].replace('\\', '/').casefold()
            helper_path = str(helper['path']).replace('\\', '/').casefold()
            assert re.search(r'(?:^|[\s"])'+re.escape(helper_path)+r'(?=$|[\s"])', command)
            assert re.search(r'--timeout-seconds\s+0(?:\s|$)', command)
            assert re.search(r'--root-exit-policy\s+terminate-job(?:\s|$)', command)
            found_collector = True
        if current == owner:
            assert found_collector, 'Caller is not under the recorded collector'
            return
        parent = int(row['parent_pid'])
        assert parent in processes, 'Live parent missing'
        child_time = datetime.datetime.fromisoformat(row['start_utc'].replace('Z', '+00:00'))
        parent_time = datetime.datetime.fromisoformat(processes[parent]['start_utc'].replace('Z', '+00:00'))
        assert parent_time <= child_time, 'Ancestor PID was reused after child creation'
        current = parent
    raise AssertionError('Owner is not in bounded live ancestry')
