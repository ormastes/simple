#!/usr/bin/env python3
"""Reconstruct the d342 Linux-host link, requiring byte/metadata-only equality.

No module is compiled. This baseline uses the ORIGINAL stub object. A changed
provider replay is forbidden unless this comparison establishes its inputs.
"""
import argparse
import hashlib
import json
import pathlib
import re
import struct
import subprocess

p = argparse.ArgumentParser(description=__doc__)
for name in ['retained', 'native', 'reference', 'cc', 'nm', 'out']:
    p.add_argument('--'+name, type=pathlib.Path, required=True)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=False)
objects = a.retained/'native-objects-hC48Eg'
capsule = objects/'bootstrap_mutex_runtime_capsule/libsimple_bootstrap_mutex_runtime.a'
digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
assert digest(a.reference) == 'a60b9ff3aa41e5ada5a1884a3f729791f4576518f996ba8b4d3f55bc463db446'
assert digest(a.native) == '7fc91928c1ff216caa45375f62aff87c174b31a6893f8ea21ff9b544ad1e40f9'
log = (a.retained/'windows-stage2.log').read_text(encoding='utf-8')
assert '[native-build] compiled=1612 reused=0 failed=0' in log
assert 'Runtime retention roots (3): rt_function_not_found, rt_set_args, rt_string_bytes' in log

def run(argv, name, timeout=180):
    (a.out/(name+'.argv.json')).write_text(json.dumps(list(map(str, argv)), indent=2))
    result = subprocess.run(list(map(str, argv)), capture_output=True, timeout=timeout)
    (a.out/(name+'.stdout')).write_bytes(result.stdout)
    (a.out/(name+'.stderr')).write_bytes(result.stderr)
    assert result.returncode == 0, (name, result.returncode, result.stderr[-4000:])
    return result.stdout.decode()

def symbols(path, name):
    rows = run([a.nm, '-g', path], name).splitlines()
    defined, undefined = set(), set()
    for row in rows:
        parts = row.split()
        if len(parts) == 3:
            kind, symbol = parts[1:]
        elif len(parts) == 2:
            kind, symbol = parts
        else:
            continue
        if len(kind) != 1:
            continue
        (undefined if kind in ['U', 'w', 'v'] else defined).add(symbol)
    return defined, undefined

native_defined, _ = symbols(a.native, 'native-symbols')
capsule_defined, _ = symbols(capsule, 'capsule-symbols')
_, init_undefined = symbols(objects/'_init_all.o', 'init-symbols')
roots = sorted(native_defined.intersection(['__simple_runtime_init', '__simple_runtime_shutdown',
    'rt_set_args', 'rt_function_not_found', 'rt_string_bytes', 'prof_sample_force_link']))
if 'rt_security_load_registry_sdn' in init_undefined and 'rt_security_load_registry_sdn' in native_defined:
    roots = sorted(set(roots+['rt_security_load_registry_sdn']))
assert roots == ['rt_function_not_found', 'rt_set_args', 'rt_string_bytes']
roots += sorted(capsule_defined.intersection(native_defined))
for name in ['rt_fd_stat_snapshot_v1', 'rt_array_bytes_validate', 'rt_array_bytes_copy_checked']:
    assert name in native_defined
    roots.append(name)
(a.out/'roots.json').write_text(json.dumps(roots, indent=2))
recorded = (objects/'spl_objects.rsp').read_text().splitlines()
modules = [objects/pathlib.PurePosixPath(row.strip('"')).name for row in recorded]
assert len(modules) == 1612 and len(set(modules)) == 1612 and all(path.is_file() for path in modules)
rsp = a.out/'spl_objects.rsp'
rsp.write_text(''.join('"'+str(path.resolve()).replace('"', '\\"')+'"\n' for path in modules))
root = pathlib.Path(__file__).resolve().parents[2]
source = subprocess.check_output(['git', '-C', str(root), 'show', 'd3422d488768713c1e6153bd2a7766ff22cbbd23:src/compiler_rust/common/src/platform/link_config.rs'], text=True)
owner_source = subprocess.check_output(['git', '-C', str(root), 'show', 'd3422d488768713c1e6153bd2a7766ff22cbbd23:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs'])
(a.out/'source-binding.json').write_text(json.dumps({'source_revision': 'd3422d488768713c1e6153bd2a7766ff22cbbd23',
    'linker_sha256': hashlib.sha256(owner_source).hexdigest(),
    'link_config_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'replay_script_sha256': digest(pathlib.Path(__file__)), 'artifact_id': 14863320409,
    'artifact_declared_sha256': 'b1b4a164fcf5313ed76a5c39c47d85f6223c91152e1e3448b8b8cc2022b6ab1e'}, indent=2))
libs = re.findall(r'"([a-z0-9_]+)"', source.split('pub fn windows_mingw()')[1].split('libraries: vec![')[1].split(']')[0])
output = a.out/'simple_stage2.exe'
argv = [a.cc, '--target=x86_64-w64-windows-gnu', '-fuse-ld=lld', '--rtlib=compiler-rt',
    '--unwindlib=libunwind', '-fuse-ld=lld', '-fPIC', '-o', output,
    objects/'_main_stub.o', objects/'_init_all.o', '@'+str(rsp.resolve()),
    *['-Wl,-u,'+name for name in roots], a.native, capsule, '-Wl,--gc-sections',
    *['-l'+lib for lib in libs], objects/'_stubs.o', a.native,
    '-Wl,--allow-multiple-definition', '-Wl,--no-fatal-warnings']
inputs = [*modules, objects/'_main_stub.o', objects/'_init_all.o', objects/'_stubs.o',
          objects/'spl_objects.rsp', a.native, capsule, a.reference,
          a.retained/'windows-stage2-cache/x86_64-pc-windows-gnu/scope-8aab416bf118ff8b/incremental_manifest.txt']
before = {str(path): digest(path) for path in inputs}
(a.out/'inputs.json').write_text(json.dumps(before, indent=2))
run(argv, 'baseline-link', 300)
assert before == {str(path): digest(path) for path in inputs}, 'input changed during replay'

def metadata(data):
    pe = struct.unpack_from('<I', data, 0x3c)[0]
    assert data[pe:pe+4] == b'PE\0\0'
    count, optional_size = struct.unpack_from('<H', data, pe+6)[0], struct.unpack_from('<H', data, pe+20)[0]
    optional = pe+24
    assert struct.unpack_from('<H', data, optional)[0] == 0x20b
    sections = []
    for i in range(count):
        at = optional+optional_size+40*i
        name = data[at:at+8].rstrip(b'\0').decode()
        virtual_size, rva, size, offset = struct.unpack_from('<IIII', data, at+8)
        sections.append((name, rva, max(virtual_size, size), offset, size))
    def file_offset(rva):
        for _, base, size, offset, _ in sections:
            if base <= rva < base+size:
                return offset+rva-base
        raise AssertionError(('unmapped metadata RVA', rva))
    fields = [('coff_timestamp', pe+8, 4)]
    debug_rva, debug_size = struct.unpack_from('<II', data, optional+112+6*8)
    if debug_rva:
        debug = file_offset(debug_rva)
        for index in range(debug_size//28):
            at = debug+index*28
            fields.append(('debug_timestamp', at+4, 4))
            kind, size, _, pointer = struct.unpack_from('<IIII', data, at+12)
            if kind == 2 and size >= 24 and data[pointer:pointer+4] == b'RSDS':
                fields.append(('codeview_guid', pointer+4, 16))
    export_rva = struct.unpack_from('<I', data, optional+112)[0]
    if export_rva:
        fields.append(('export_timestamp', file_offset(export_rva)+4, 4))
    return fields, sections

old, new = a.reference.read_bytes(), output.read_bytes()
old_fields, old_sections = metadata(old)
new_fields, new_sections = metadata(new)
report = {'reference_sha256': digest(a.reference), 'baseline_sha256': digest(output),
          'byte_identical': old == new, 'reference_bytes': len(old), 'baseline_bytes': len(new),
          'metadata_differences': [], 'section_differences': []}
normalized_old, normalized_new = bytearray(old), bytearray(new)
if old_fields == new_fields and old_sections == new_sections:
    for name, offset, size in old_fields:
        if old[offset:offset+size] != new[offset:offset+size]:
            report['metadata_differences'].append({'field': name, 'offset': offset, 'old': old[offset:offset+size].hex(), 'new': new[offset:offset+size].hex()})
        normalized_old[offset:offset+size] = b'\0'*size
        normalized_new[offset:offset+size] = b'\0'*size
    for name, _, _, offset, size in old_sections:
        if old[offset:offset+size] != new[offset:offset+size]:
            report['section_differences'].append({'section': name, 'reference_sha256': hashlib.sha256(old[offset:offset+size]).hexdigest(), 'baseline_sha256': hashlib.sha256(new[offset:offset+size]).hexdigest()})
report['metadata_only_equal'] = normalized_old == normalized_new
(a.out/'comparison.json').write_text(json.dumps(report, indent=2))
assert report['byte_identical'] or report['metadata_only_equal'], 'baseline differs beyond declared PE metadata; do not repair/relink/qualify'
