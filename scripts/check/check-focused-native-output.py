#!/usr/bin/env python3
"""Exercise a freshly compiled actual focused dispatcher, without compiler mocks.

The caller owns the finite process-tree governor. The dispatcher must be outside
any source checkout so its executable ancestors cannot provide runtime.c.
This is a bootstrap diagnostic, not compiler-generation qualification.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import struct


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dispatcher', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    dispatcher = args.dispatcher.resolve(strict=True)
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    for location in (dispatcher.parent, root):
        assert not any((p / 'src/runtime/runtime.c').exists()
                       for p in (location, *location.parents)), location
    source = root / 'main.spl'
    source.write_bytes(b'fn main() -> i64:\n    return 7\n')
    expected_dispatcher = digest(dispatcher)
    env = os.environ.copy()
    for name in ('SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4',
                 'SIMPLE_NATIVE_BUILD_EMIT_OBJECT', 'SIMPLE_RUNTIME_PATH',
                 'SIMPLE_NATIVE_RUNTIME_BUNDLE', 'SIMPLE_MIR_SHARD_LINK'):
        env.pop(name, None)
    env['SIMPLE_PROJECT_ROOT'] = str(root)
    env['SIMPLE_LIB'] = str(root)
    env['SIMPLE_NO_STUB_FALLBACK'] = '1'
    results = []

    def case(name, flags, code, extra_env=None):
        output = root / (name + '.o')
        argv = [str(dispatcher), 'native-build', '--backend', 'llvm',
                '--source', str(root), '--entry', str(source),
                '--cache-dir', str(root / (name + '-cache')),
                '--output', str(output), *flags]
        (root / (name + '.argv.json')).write_text(json.dumps(argv, indent=2))
        with (root / (name + '.stdout')).open('wb') as out, \
                (root / (name + '.stderr')).open('wb') as err:
            process = subprocess.run(argv, cwd=root, env=env | (extra_env or {}),
                                     stdout=out, stderr=err, timeout=120)
        assert process.returncode == code, (name, process.returncode)
        log = ((root / (name + '.stdout')).read_text(errors='replace') +
               (root / (name + '.stderr')).read_text(errors='replace'))
        assert 'focused output mode escaped' not in log
        results.append({'case': name, 'exit': process.returncode,
                        'stdout_sha256': digest(root / (name + '.stdout')),
                        'stderr_sha256': digest(root / (name + '.stderr'))})
        return output, log

    obj, log = case('object', ['--emit-object'], 0)
    data = obj.read_bytes()
    assert len(data) > 20
    if data[:4] == b'\x7fELF':
        assert int.from_bytes(data[16:18], 'little' if data[5] == 1 else 'big') == 1
    else:
        assert data[:2] in (b'\x64\x86', b'\x4c\x01'), 'not ELF REL or x86 COFF'
        _, sections, _, symbol_offset, symbols, optional, _ = struct.unpack_from('<HHLLLHH', data)
        assert sections > 0 and optional == 0
        assert 20 + sections * 40 <= len(data)
        assert symbol_offset + symbols * 18 <= len(data)
        code_sections = 0
        for index in range(sections):
            offset = 20 + index * 40
            size, raw = struct.unpack_from('<LL', data, offset + 16)
            flags = struct.unpack_from('<L', data, offset + 36)[0]
            if flags & 0x20 and size:
                assert raw >= 20 + sections * 40 and raw + size <= len(data)
                code_sections += 1
        assert code_sections > 0, 'COFF has no nonempty bounded code section'
    assert 'Runtime source directory not found' not in log
    results[-1]['object_sha256'] = digest(obj)
    absent, log = case('default-link', [], 1)
    assert not absent.exists()
    assert 'Runtime source directory not found' in log
    absent, log = case('conflict', ['--emit-object', '--emit-shared'], 1)
    assert not absent.exists() and 'mutually exclusive' in log
    absent, log = case('stage4-refusal', ['--emit-object'], 1,
                       {'SIMPLE_BOOTSTRAP_STAGE4': '1'})
    assert not absent.exists() and 'Stage4 strict profile does not support' in log
    assert digest(dispatcher) == expected_dispatcher
    (root / 'result.json').write_text(json.dumps({
        'status': 'PASS', 'scope': 'actual focused caller; no compiler admission',
        'dispatcher_sha256': expected_dispatcher, 'source_sha256': digest(source),
        'cases': results}, indent=2) + '\n')


if __name__ == '__main__':
    main()
