#!/usr/bin/env python3
"""Real GNU COFF provider links; requires a production Simple time-utils object.

The supplied object must come from compiling src/lib/common/time_utils.spl with
the selected producer. This test retains input hashes and link maps; it does not
claim whole-compiler qualification or manufacture a replacement Simple owner.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


SYMBOLS = [
    'rt_timestamp_get_year', 'rt_timestamp_get_month', 'rt_timestamp_get_day',
    'rt_timestamp_get_hour', 'rt_timestamp_get_minute', 'rt_timestamp_get_second',
    'rt_timestamp_get_microsecond', 'rt_timestamp_from_components',
    'rt_timestamp_add_days', 'rt_timestamp_diff_days', 'rt_progress_init',
    'rt_progress_reset', 'rt_progress_get_elapsed_seconds',
]
LIBS = ['kernel32', 'ntdll', 'userenv', 'ws2_32', 'winhttp', 'mswsock',
        'dbghelp', 'advapi32', 'bcrypt', 'ole32', 'oleaut32', 'shell32',
        'propsys', 'runtimeobject', 'synchronization', 'crypt32', 'secur32',
        'ncrypt', 'iphlpapi', 'pdh', 'netapi32', 'psapi', 'powrprof', 'd3d11',
        'dxgi', 'user32', 'gdi32', 'dwmapi', 'imm32', 'uxtheme', 'winmm',
        'shlwapi', 'msvcrt', 'mingwex', 'mingw32']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--runtime-archive', required=True, type=Path)
    parser.add_argument('--simple-object', required=True, type=Path)
    parser.add_argument('--producer', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    tool = args.toolchain.resolve() / 'bin'
    env = dict(os.environ, PATH=str(tool) + os.pathsep + os.environ.get('PATH', ''))

    def command(argv, name, expected=0):
        argv = list(map(str, argv))
        (out / (name + '.argv.json')).write_text(json.dumps(argv, indent=2))
        result = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=120, env=env)
        (out / (name + '.log')).write_bytes(result.stdout)
        (out / (name + '.exit')).write_text(str(result.returncode) + '\n')
        if expected == 0 and result.returncode != 0:
            raise RuntimeError(f'{name} failed: {result.returncode}; see retained log')
        if expected != 0 and result.returncode == 0:
            raise RuntimeError(f'{name} unexpectedly accepted a strong duplicate')
        return result.stdout.decode('utf-8', errors='replace')

    members = command([tool/'llvm-ar.exe', 't', args.runtime_archive], 'members').splitlines()
    matches = [name for name in members if name.endswith('-runtime_timestamp.o')]
    if len(matches) != 1 or Path(matches[0]).name != matches[0]:
        raise RuntimeError('expected exactly one flat runtime_timestamp archive member')
    member = out / matches[0]
    source = root / 'src/runtime/runtime_timestamp.c'
    command([tool/'clang.exe', '--target=x86_64-w64-windows-gnu', '-O2',
             '-DSIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT', '-c', source, '-o', member], 'compile-provider')
    runtime = out / 'libsimple_native_all.a'
    shutil.copyfile(args.runtime_archive, runtime)
    command([tool/'llvm-ar.exe', 'r', runtime, member], 'replace-provider')
    simple = out / 'real-time-utils.o'
    shutil.copyfile(args.simple_object, simple)
    definitions = command([tool/'llvm-nm.exe', '--defined-only', '--extern-only', simple], 'simple-symbols')
    for symbol in SYMBOLS:
        if not any(line.split()[-2:] == ['T', symbol] for line in definitions.splitlines()):
            raise RuntimeError('real Simple object missing strong export ' + symbol)
    common = [tool/'clang.exe', '--target=x86_64-w64-windows-gnu', '-fuse-ld=lld',
              '--rtlib=compiler-rt', '--unwindlib=libunwind',
              root/'src/runtime/test/windows_timestamp_provider_selfcheck.c']
    for name, objects in [('compat-only', []), ('simple-owner', [simple])]:
        executable = out / (name + '.exe')
        command(common + objects + [runtime] + ['-l' + lib for lib in LIBS] +
                ['-Wl,-Map,' + str(out/(name+'.map')), '-o', executable], name + '-link')
        stdout = command([executable], name + '-run')
        if stdout.strip() != 'PASS: calendar/progress C ABI':
            raise RuntimeError('unexpected ABI selfcheck output')
    # Map provenance distinguishes the real Simple owner from the fallback,
    # even though both intentionally return the same calendar/progress values.
    lines = (out/'simple-owner.map').read_text().splitlines()
    current_object = ''
    owners = {}
    for line in lines:
        if ':(' in line:
            current_object = line
        for symbol in SYMBOLS:
            if line.split() and line.split()[-1] == symbol:
                owners[symbol] = current_object
    if any('real-time-utils.o:(' not in owners.get(symbol, '') for symbol in SYMBOLS):
        raise RuntimeError('link map does not bind every export to the real Simple owner')
    negative = out/'strong-conflict.c'
    negative.write_text('#include <stdint.h>\nint32_t rt_timestamp_get_year(int64_t x) { return 2001; }\n')
    log = command(common + [simple, negative, runtime] + ['-l' + lib for lib in LIBS] +
                  ['-o', out/'must-not-link.exe'], 'strong-conflict', expected=1)
    if 'duplicate symbol: rt_timestamp_get_year' not in log:
        raise RuntimeError('negative control failed for an unrelated reason')
    paths = [source, args.runtime_archive, args.simple_object, args.producer, runtime]
    identities = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    (out/'inputs.json').write_text(json.dumps(identities, indent=2))
    print('PASS: compatibility-only execution, real Simple owner execution/map, strong duplicate rejected')


if __name__ == '__main__':
    main()
