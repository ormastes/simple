"""Read-only paired containment benchmark; no source extraction or native build."""
import argparse
import ctypes
import hashlib
import importlib.util
import json
from pathlib import Path
import statistics
import subprocess
import sys
import time


def peak_rss():
    class Counters(ctypes.Structure):
        _fields_ = [('cb', ctypes.c_ulong), ('faults', ctypes.c_ulong)] + [
            (name, ctypes.c_size_t) for name in ('peak_working_set', 'working_set',
                'peak_paged', 'paged', 'peak_nonpaged', 'nonpaged', 'pagefile', 'peak_pagefile')]
    counters = Counters()
    counters.cb = ctypes.sizeof(counters)
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.GetCurrentProcess.restype = ctypes.c_void_p
    psapi = ctypes.WinDLL('psapi', use_last_error=True)
    psapi.GetProcessMemoryInfo.argtypes = [ctypes.c_void_p, ctypes.POINTER(Counters), ctypes.c_ulong]
    if not psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(), ctypes.byref(counters), counters.cb):
        raise ctypes.WinError(ctypes.get_last_error())
    return counters.peak_working_set, counters.working_set


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--inventory', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--count', type=int, default=2000)
    parser.add_argument('--samples', type=int, default=5)
    parser.add_argument('--child', choices=('baseline', 'candidate'))
    args = parser.parse_args()
    helper = Path(__file__).parents[1] / 'materialization-path-boundary.py'
    spec = importlib.util.spec_from_file_location('boundary', helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if args.child:
        boundary = module.MaterializationBoundary(args.root)
        digest = hashlib.sha256()
        count = 0
        started = time.perf_counter()
        with args.inventory.open(encoding='utf-8') as stream:
            for line in stream:
                _, relative = line.rstrip('\n').split('\t', 1)
                path = args.root / relative
                accepted = (path.resolve().is_relative_to(args.root.resolve())
                    if args.child == 'baseline' else boundary.contains(path))
                if not accepted:
                    raise ValueError('authenticated inventory path escaped')
                digest.update(relative.encode() + b'\0')
                count += 1
                if count == args.count:
                    break
        boundary.verify_root()
        elapsed = time.perf_counter() - started
        peak, steady = peak_rss()
        print(json.dumps(dict(mode=args.child, count=count, elapsed_seconds=elapsed,
            peak_rss_bytes=peak, steady_rss_bytes=steady, accepted_digest=digest.hexdigest())))
        return
    if not args.output or args.output.exists() or args.samples < 3:
        parser.error('fresh output and at least three paired samples required')
    samples = []
    for index in range(args.samples):
        for mode in (('baseline', 'candidate') if index % 2 == 0 else ('candidate', 'baseline')):
            command = [sys.executable, '-B', str(Path(__file__).resolve()), '--root', str(args.root),
                '--inventory', str(args.inventory), '--count', str(args.count), '--child', mode]
            samples.append(json.loads(subprocess.check_output(command, text=True)))
    assert len({(row['count'], row['accepted_digest']) for row in samples}) == 1
    report = dict(scope='Windows physical containment only; not end-to-end materialization',
        python_sha256=sha(sys.executable), helper_sha256=sha(helper),
        inventory_sha256=sha(args.inventory), root=str(args.root), samples=samples)
    for mode in ('baseline', 'candidate'):
        rows = [row for row in samples if row['mode'] == mode]
        times = sorted(row['elapsed_seconds'] for row in rows)
        report[mode] = dict(p50_seconds=statistics.median(times), p95_seconds=times[-1],
            peak_rss_bytes=max(row['peak_rss_bytes'] for row in rows),
            steady_rss_bytes=statistics.median(row['steady_rss_bytes'] for row in rows))
    report['time_ratio'] = report['candidate']['p95_seconds'] / report['baseline']['p95_seconds']
    report['memory_ratio'] = report['candidate']['peak_rss_bytes'] / report['baseline']['peak_rss_bytes']
    report['joint_ratio'] = report['time_ratio'] + report['memory_ratio']
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('baseline', 'candidate', 'time_ratio', 'memory_ratio', 'joint_ratio')}))


if __name__ == '__main__':
    main()
