#!/usr/bin/env python3
"""Explicit retained-object lane; legacy Stage4 admission is never synthesized.

Receipts are env text for interoperability with the existing shell controller.
All path/hash joins are reopened. Object production and independent review are
separate operations: a missing qualification leaves a retained object, not PASS.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('legacy', HERE/'stage4-retained-self-evidence.py')
legacy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(legacy)
need, file, sha, env, eq, bound = legacy.need, legacy.file, legacy.sha, legacy.env, legacy.eq, legacy.bound
FORBIDDEN = {'SIMPLE_BOOTSTRAP', 'SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4',
             'SIMPLE_NATIVE_BUILD_RUST', 'SIMPLE_BOOTSTRAP_WHOLE_PROGRAM', 'SIMPLE_TEST_RUNNER_RUST'}
ROLES = {'compiler_cli_build': 'src/app/cli/_CliMain/main_and_help.spl',
         'test_runner_build': 'src/app/test_runner_new/main.spl',
         'mcp_build': 'src/app/mcp/main.spl', 'lsp_build': 'src/app/simple_lsp_mcp/main.spl'}
ARGV_LAUNCHER = ('import os,sys\nfrom pathlib import Path\n'
                 'args=Path(sys.argv[1]).read_bytes().split(b"\\0");assert args.pop()==b""\n'
                 'os.execv(args[0],args)\n').encode()


def write_env(path, data):
    p = Path(path)
    need(not p.exists(), 'receipt already exists: '+str(p))
    need(all('\n' not in str(v) for v in data.values()), 'receipt encoding')
    p.write_text(''.join(str(k)+'='+str(v)+'\n' for k, v in data.items()))


def joins(data, name):
    return bound(data, name+'_path', name+'_sha256')


def invocation(data, prefix, binary, root, leading):
    transcript = joins(data, prefix+'_transcript')
    try:
        return legacy.transcript(transcript, binary, root, leading)
    except ValueError:
        # Prepared gates use a tiny reviewed execv launcher to preserve NUL argv.
        # Its exact bytes, argv file and actual transcribed wrapper are reopened.
        launcher = joins(data, prefix+'_launcher')
        need(file(launcher).read_bytes() == ARGV_LAUNCHER, 'unreviewed argv launcher')
        argv_path = joins(data, prefix+'_argv')
        values = file(argv_path).read_bytes().split(b'\0')
        need(values.pop() == b'', 'argv terminator')
        args = list(map(os.fsdecode, values))
        need(args and args[0] == binary and args[1:1+len(leading)] == leading, 'launched producer/argv')
        wrapped, settings = legacy.transcript(transcript, '/usr/bin/python3', root, [launcher, argv_path])
        need(wrapped == [launcher, argv_path], 'extra wrapper argv')
        return args[1:], settings


def expand_response(args, linked):
    if len(args) == 1 and args[0].startswith('@'):
        response = args[0][1:]
        need(response in linked and sha(response) == linked[response], 'unbound response file')
        values = [json.loads(line) for line in file(response).read_text().splitlines()]
        need(all(isinstance(value, str) and value and '\0' not in value for value in values), 'response grammar')
        args = values
    need(not any(value.startswith('@') for value in args), 'nested/mixed response arguments')
    return args


def manifest(path):
    """New lane uses hash|path; the historical lane keeps path|hash."""
    result = {}
    for row in file(path).read_text().splitlines():
        h, name = row.split('|')
        need(re.fullmatch('[a-f0-9]{64}', h), 'manifest digest')
        need(name not in result, 'duplicate manifest path')
        need(sha(name) == h, 'changed manifest input: '+name)
        result[name] = h
    need(result, 'empty manifest')
    return result


def macho(path, kind):
    with file(path).open('rb') as f:
        header = f.read(32)
    need(len(header) == 32, 'truncated Mach-O')
    magic, cpu, _, actual = struct.unpack('<IIII', header[:16])
    need((magic, cpu, actual) == (0xfeedfacf, 0x100000c, kind), 'wrong arm64 artifact kind')
    if kind == 2:
        need(os.access(path, os.X_OK), 'nonexecutable product')


def rss(path, raw):
    d = env(path)
    for k, v in {'status': 'complete', 'exit_status': str(raw), 'quiescent': '1',
                 'rss_cap_mode': 'enforce', 'rss_cap_enforced': '1', 'observer_errors': '0',
                 'observer_restarts': '0', 'measurement_budget_complete': '1',
                 'sample_budget_exceeded': '0'}.items():
        eq(d, k, v)
    need(int(d['max_rss_kib']) > 0, 'missing enforced cap')


def phase_counts(line):
    d = dict(word.split('=', 1) for word in line.split()[1:] if '=' in word)
    for k in ('done', 'total', 'remaining', 'succeeded', 'cached', 'failed'):
        d[k] = int(d[k])
    need(d['total'] > 0 and d['done'] == d['total'], 'incomplete native modules')
    need(d['remaining'] == d['failed'] == 0, 'failed native modules')
    need(d['succeeded']+d['cached'] == d['total'], 'native ledger mismatch')
    need(d['unit_kind'] == 'modules', 'wrong ledger units')
    return d


def native_log(path, raw, obj):
    need(str(raw) in ('0', '1'), 'unsupported compiler exit status')
    expected = 'error: native-build worker exited 0 but produced no output binary: '+str(obj)
    observed = 0
    published = 0
    complete = None
    mir = None
    with file(path).open() as f:
        for row in f:
            line = row.rstrip('\n')
            if line == '[native-build] Artifact published: '+str(obj):
                published += 1
                continue
            if line == expected:
                observed += 1
                continue
            need(not re.search(r'(^|\s)(error:|fatal error:|panic:|LLVM ERROR:|internal compiler error)', line, re.I),
                 'compiler error: '+line[:200])
            need('DROPPED to wildcard' not in line, 'dropped module')
            if line.startswith('[build] '):
                failed = re.search(r'(?:^| )failed=([0-9]+)(?: |$)', line)
                need(not failed or int(failed[1]) == 0, 'phase failure')
                if ' phase=native_compile ' in line and ' current=complete' in line:
                    complete = phase_counts(line)
                    need(complete['current'] == 'complete', 'native completion marker')
                if ' phase=mir ' in line:
                    counters = dict(x.split('=', 1) for x in line.split()[1:] if '=' in x)
                    if counters.get('done') == counters.get('total') and int(counters.get('total', 0)) > 0:
                        mir = phase_counts(line)
    need(complete is not None, 'native completion absent')
    need(mir is not None and mir['total'] == complete['total'], 'MIR completion absent/mismatched')
    need(observed == (1 if str(raw) == '1' else 0), 'unclassified coordinator failure')
    need(published == 1, 'missing/duplicate actual aggregate publication')
    return complete


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def runtime_snapshot(facade, output, runtime):
    subprocess.run(['sh', '-c', 'BOOTSTRAP_STAGE3_FACADE_PATH=$1; export BOOTSTRAP_STAGE3_FACADE_PATH; . "$1"; bootstrap_stage3_directory_snapshot "$2" "$3"',
                    'runtime-snapshot', str(facade), str(output), str(runtime)], check=True)


def source_map(path, payload):
    """Full payload bytes and gitlinks must match the chain's Git tree."""
    d = env(path)
    eq(d, 'schema', 'simple-retained-source-map-v1')
    eq(d, 'payload_root', payload)
    for root in (d['original_root'], payload):
        need(git(root, 'rev-parse', 'HEAD').decode().strip() == d['source_head'], 'source HEAD changed')
        need(git(root, 'rev-parse', 'HEAD^{tree}').decode().strip() == d['source_tree'], 'source tree changed')
        need(not git(root, 'status', '--porcelain', '--untracked-files=all'), 'dirty source')
    freeze = json.loads(file(joins(d, 'freeze_plan')).read_text())
    status = json.loads(file(joins(d, 'freeze_status')).read_text())
    need(freeze['source_root'] == d['original_root'] and freeze['source_head'] == d['source_head'], 'freeze source')
    need(status['status'] == 'protected' and status['source_clean'] is True, 'source not protected')
    need(status['source_root'] == freeze['source_root'] and status['source_head'] == freeze['source_head'], 'freeze status source')
    need(status['plan'] == d['freeze_plan_path'], 'freeze status plan')
    if 'index_sparse_tags_sha256' in freeze:
        need(hashlib.sha256(git(d['original_root'], 'ls-files', '-v', '-z')).hexdigest() == freeze['index_sparse_tags_sha256'], 'sparse index changed')
    for rel in freeze.get('absent_sparse_paths', []):
        need(not os.path.lexists(Path(d['original_root'])/rel), 'sparse path materialized')
    if 'absent_sparse_paths_sha256' in freeze:
        absent = b'\0'.join(os.fsencode(x) for x in freeze['absent_sparse_paths'])
        need(hashlib.sha256(absent).hexdigest() == freeze['absent_sparse_paths_sha256'], 'absent census changed')
    present = manifest(joins(d, 'original_present'))
    need(all(str(name).startswith(d['original_root']+'/') for name in present), 'present source escapes root')
    counts = {'file': 0, 'dir': 0}
    for row in freeze['records']:
        counts[row['kind']] += 1
        st = Path(row['path']).lstat()
        need(not stat.S_ISLNK(st.st_mode), 'freeze record symlink')
        need(stat.S_ISREG(st.st_mode) if row['kind'] == 'file' else stat.S_ISDIR(st.st_mode), 'freeze record type')
        need(st.st_dev == row['dev'] and st.st_ino == row['ino'], 'source inode changed')
        need(stat.S_IMODE(st.st_mode) == row['mode'] & ~0o222, 'source permissions changed')
        if row['kind'] == 'file':
            need(row['path'] in present, 'unbound frozen source file')
            need(st.st_flags == row['flags'] | stat.UF_IMMUTABLE, 'source protection changed')
        else:
            need(st.st_flags == row['flags'], 'source directory flags changed')
    need(counts['file'] == status['protected_files'] and counts['dir'] == status['protected_dirs'], 'freeze census changed')
    # gitlinks are recursively verified rather than accepted from HEAD alone.
    def tree(root, prefix=''):
        for record in git(root, 'ls-tree', '-rz', 'HEAD').split(b'\0'):
            if not record:
                continue
            meta, rel = record.split(b'\t', 1)
            mode, kind, oid = meta.decode().split()
            name = os.fsdecode(rel)
            p = Path(root)/name
            if kind == 'commit':
                need(p.is_dir() and not p.is_symlink(), 'missing nested module: '+prefix+name)
                need(git(p, 'rev-parse', 'HEAD').decode().strip() == oid, 'nested gitlink changed')
                need(not git(p, 'status', '--porcelain', '--untracked-files=all'), 'dirty nested module')
                tree(p, prefix+name+'/')
            else:
                need(mode in ('100644', '100755', '120000'), 'unsupported tracked kind')
                data = os.fsencode(os.readlink(p)) if mode == '120000' else file(p).read_bytes()
                object_hash = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
                need(object_hash == oid, 'tracked bytes changed: '+prefix+name)
    tree(payload)
    return d


def product(path, producer=None, source=None, runtime=None):
    d = env(path)
    eq(d, 'schema', 'simple-retained-manual-product-v1')
    inputs = manifest(joins(d, 'inputs'))
    for key in ('object', 'artifact', 'build_log', 'build_transcript', 'build_rss', 'qualification',
                'link_result', 'link_inputs', 'shim_transcript', 'shim_rss', 'link_transcript', 'link_rss',
                'c_runtime_manifest', 'shim_source', 'shim_object', 'module_init', 'toolchain'):
        p = joins(d, key)
        need(p in inputs, 'product evidence not in manifest: '+key)
    if producer is not None:
        eq(d, 'producer_path', producer)
    eq(d, 'producer_sha256', sha(d['producer_path']))
    if source is not None:
        eq(d, 'source_root', source)
    if runtime is not None:
        eq(d, 'runtime_path', runtime)
    macho(d['object_path'], 1)
    macho(d['artifact_path'], 2)
    native_log(d['build_log_path'], d['build_raw_status'], d['object_path'])
    rss(d['build_rss_path'], d['build_raw_status'])
    args, settings = invocation(d, 'build', d['producer_path'], d['source_root'], ['native-build'])
    need('--emit-object' in args, 'product was not aggregate emission')
    for flag, value in (('--entry', d['entry']), ('--runtime-path', d['runtime_path']), ('--mode', 'dynload')):
        need(args.count(flag) == 1 and args[args.index(flag)+1] == value, 'wrong product '+flag)
    need(not any(x.split('=', 1)[0] in FORBIDDEN for x in settings), 'bootstrap selector')
    parsed_settings = dict(value.split('=', 1) for value in settings)
    need(len(parsed_settings) == len(settings), 'duplicate explicit environment')
    settings = parsed_settings
    for key, expected in {'SIMPLE_BINARY': d['producer_path'], 'SIMPLE_RUNTIME_PATH': d['runtime_path'],
                          'SIMPLE_NO_STUB_FALLBACK': '1'}.items():
        need(settings.get(key) == expected, 'wrong worker/runtime selector: '+key)
    q = env(d['qualification_path'])
    for k, value in {'schema': 'simple-retained-object-qualification-v1', 'artifact_path': d['object_path'],
                     'artifact_sha256': d['object_sha256'], 'artifact_validation': 'PASS',
                     'coordinator_raw_status': d['build_raw_status'], 'normal_build_qualification': 'NOT_QUALIFIED'}.items():
        eq(q, k, value)
    reviewed = manifest(joins(q, 'evidence_manifest'))
    for key in ('object', 'build_log', 'build_transcript', 'build_rss'):
        need(d[key+'_path'] in reviewed, 'qualification omitted '+key)
    link = env(d['link_result_path'])
    for k, value in {'shim_raw_status': '0', 'link_raw_status': '0', 'guard_validation_status': '0',
                     'boundaries': 'PASS', 'artifact_sha256': d['artifact_sha256']}.items():
        eq(link, k, value)
    linked = manifest(d['link_inputs_path'])
    need(d['object_path'] in linked and linked[d['object_path']] == d['object_sha256'], 'link lost aggregate')
    c_objects = manifest(d['c_runtime_manifest_path'])
    need(len(c_objects) == 39 and all(p in linked and linked[p] == h for p, h in c_objects.items()), 'link runtime provider set changed')
    for p in c_objects:
        macho(p, 1)
    archives = json.loads(d.get('archive_paths', '[]'))
    config = env(joins(d, 'toolchain'))
    for name in ('cc', 'nm', 'entry_template', 'sdk_settings'):
        joins(config, name)
    eq(d, 'cc_path', config['cc_path']); eq(d, 'cc_sha256', config['cc_sha256'])
    shim_source, shim_object = joins(d, 'shim_source'), joins(d, 'shim_object')
    macho(shim_object, 1)
    module_init = joins(d, 'module_init')
    init = file(module_init).read_text().splitlines()
    need(init == sorted(set(init)) and all(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', name) for name in init), 'initializer inventory')
    aggregate_defs, _, _ = symbols(config['nm_path'], d['object_path'])
    need(aggregate_defs.get('___simple_main') is True, 'aggregate main provider missing/nonunique')
    actual_init = sorted({name[1:] for name in aggregate_defs
                          if name == '___module_init' or name.startswith('___module_init_')})
    need(init == actual_init, 'initializer inventory does not match actual aggregate')
    need(file(shim_source).read_text() == canonical_shim(config['entry_template_path'], init), 'noncanonical entry shim')
    need(shim_source in linked and module_init in linked, 'unbound shim source/initializers')
    common = ['--target=aarch64-apple-darwin', '-mmacosx-version-min=26.5', '-isysroot', config['sdk_path']]
    if archives:
        expected = [str(Path(d['original_runtime_path'])/name) for name in ('libsimple_compiler_backfill.a', 'libsimple_native_all.a')]
        need(archives == expected and all(p in linked for p in archives), 'noncanonical archive provider order')
        authority = {}
        for row in file(joins(d, 'runtime_snapshot')).read_text().splitlines():
            fields = row.split(':')
            if len(fields) == 4 and fields[0] == 'file-hex':
                authority[bytes.fromhex(fields[1]).decode()] = fields[3]
        need(all(sha(p) == authority[Path(p).name] == linked[p] for p in archives), 'archive authority changed')
    for name in ('shim', 'link'):
        rss(d[name+'_rss_path'], 0)
        t = file(d[name+'_transcript_path']).read_text().splitlines()
        need(t[0] == 'schema=simple-bootstrap-command-transcript-v2', 'link transcript schema')
        rows = {}
        for line in t[1:]:
            if line == 'runtime-env-contract:bootstrap-session-v1':
                continue
            k, length, value = line.split(':', 2)
            need(int(length) == len(value.encode()), 'link transcript length')
            rows.setdefault(k, []).append(value)
        args = expand_response(rows.get('argv', []), linked)
        need(rows.get('executable') == [d['cc_path']] and sha(d['cc_path']) == d['cc_sha256'], 'link compiler changed')
        need(rows.get('cwd') == [d['source_root']], 'link cwd changed')
        if name == 'shim':
            expected = ['-c', *common, '-fPIC', '-O2', '-ffunction-sections', '-fdata-sections', '-o', shim_object, shim_source]
            need(args == expected, 'changed shim compile argv')
        if name == 'link':
            support = archive_support(config) if archives else []
            expected = [d['object_path'], *c_objects, shim_object, *archives, *support, *common,
                        '-Wl,-dead_strip', '-Wl,-undefined,error', '-o', d['artifact_path']]
            need(args == expected, 'changed/unbound link provider or flags')
    return d


def sanity(path, compiler, runtime, c_manifest):
    d = env(path)
    eq(d, 'schema', 'simple-retained-manual-sanity-v1')
    eq(d, 'compiler_path', compiler)
    eq(d, 'compiler_sha256', sha(compiler))
    v = env(joins(d, 'version_result'))
    eq(v, 'version_qualification', 'PASS'); eq(v, 'raw_status', 0); eq(v, 'boundaries', 'PASS')
    eq(v, 'p3_sha256', sha(compiler))
    version_log = joins(d, 'version_stdout')
    eq(v, 'log_sha256', sha(version_log))
    need(file(version_log).read_bytes() == file(joins(d, 'version_expected')).read_bytes(), 'version stdout changed')
    args, _ = invocation(d, 'version', compiler, d['version_source_root'], ['--version'])
    need(args == ['--version'], 'version command changed')
    rss(joins(d, 'version_rss'), 0)
    eq(v, 'transcript_sha256', sha(d['version_transcript_path']))
    eq(v, 'log.rss.env_sha256', sha(d['version_rss_path']))
    hello = product(joins(d, 'hello_product'), producer=compiler, runtime=runtime)
    eq(hello, 'c_runtime_manifest_path', c_manifest)
    eq(hello, 'c_runtime_manifest_sha256', sha(c_manifest))
    out = joins(d, 'hello_stdout')
    need(file(out).read_bytes() == b'hello\n', 'native Hello output')
    run = env(joins(d, 'hello_run_result'))
    eq(run, 'raw_status', 0); eq(run, 'hello_output', 'PASS'); eq(run, 'boundaries', 'PASS')
    eq(run, 'hello_sha256', hello['artifact_sha256'])
    args, _ = legacy.transcript(joins(d, 'hello_run_transcript'), hello['artifact_path'], d['hello_run_source_root'], [])
    need(args == [], 'native Hello argv changed')
    rss(joins(d, 'hello_run_rss'), 0)
    eq(run, 'log_sha256', sha(out))
    eq(run, 'transcript_sha256', sha(d['hello_run_transcript_path']))
    eq(run, 'log.rss.env_sha256', sha(d['hello_run_rss_path']))
    return d


def chain(path, selected, payload, runtime):
    d = env(path)
    eq(d, 'schema', 'simple-stage4-retained-manual-self-v1')
    inputs = manifest(joins(d, 'inputs'))
    for key in ('source_map', 'producer_product', 'producer_sanity', 'self_product', 'self_sanity', 'runtime_snapshot',
                'fixed_p2', 'fixed_p2_result', 'toolchain', 'c_runtime_manifest'):
        need(joins(d, key) in inputs, 'unbound chain '+key)
    sm = source_map(d['source_map_path'], payload)
    eq(d, 'runtime_path', runtime)
    # Runtime snapshot is a canonical source-owned directory receipt, not an arbitrary digest.
    original = sm['original_root']
    config = env(joins(d, 'toolchain'))
    eq(config, 'entry_template_path', original+'/src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl')
    joins(config, 'entry_template')
    with tempfile.TemporaryDirectory(prefix='retained-runtime-') as tmp:
        snapshot = str(Path(tmp)/'runtime.snapshot')
        runtime_snapshot(original+'/scripts/check/lib/bootstrap-stage3-provenance.shs', snapshot, runtime)
        need(file(snapshot).read_bytes() == file(d['runtime_snapshot_path']).read_bytes(), 'runtime changed')
    fixed_p2 = joins(d, 'fixed_p2')
    fixed_result = env(joins(d, 'fixed_p2_result'))
    eq(fixed_result, 'schema', 'pure-spl-aliasfix-p2-native-build-v1')
    eq(fixed_result, 'native_build_raw_status', 0); eq(fixed_result, 'artifact_status', 'present')
    eq(fixed_result, 'artifact_path', fixed_p2); eq(fixed_result, 'artifact_sha256', sha(fixed_p2))
    eq(fixed_result, 'runtime_snapshot_sha256', d['runtime_snapshot_sha256'])
    macho(fixed_p2, 2)
    bound(fixed_result, 'native_build_log', 'native_build_log_sha256')
    bound(fixed_result, 'native_build_transcript', 'native_build_transcript_sha256')
    rss(bound(fixed_result, 'rss_receipt', 'rss_receipt_sha256'), 0)
    pa = product(d['producer_product_path'], producer=fixed_p2, source=original, runtime=runtime)
    pa_sanity = sanity(d['producer_sanity_path'], pa['artifact_path'], runtime, d['c_runtime_manifest_path'])
    pb = product(d['self_product_path'], producer=pa['artifact_path'], source=original, runtime=runtime)
    eq(pb, 'artifact_path', selected)
    for p in (pa, pb):
        eq(p, 'entry', 'src/app/cli/bootstrap_main.spl')
        eq(p, 'source_head', sm['source_head']); eq(p, 'source_tree', sm['source_tree'])
        eq(p, 'runtime_snapshot_sha256', d['runtime_snapshot_sha256'])
        eq(p, 'c_runtime_manifest_path', d['c_runtime_manifest_path'])
        eq(p, 'c_runtime_manifest_sha256', d['c_runtime_manifest_sha256'])
        eq(p, 'toolchain_path', d['toolchain_path']); eq(p, 'toolchain_sha256', d['toolchain_sha256'])
    args_a, _ = invocation(pa, 'build', pa['producer_path'], original, ['native-build'])
    args_b, _ = invocation(pb, 'build', pb['producer_path'], original, ['native-build'])
    roots = lambda args: [args[i+1] for i, value in enumerate(args[:-1]) if value == '--source']
    need(roots(args_a) == roots(args_b) == ['src/compositions/kernel_llvm_cranelift', 'src/compositions/cuda_static',
         'src/compiler', 'src/app', 'src/lib', 'src/plugins'], 'self source closure changed')
    pb_sanity = sanity(d['self_sanity_path'], selected, runtime, d['c_runtime_manifest_path'])
    need(file(pa_sanity['version_stdout_path']).read_bytes() == file(pb_sanity['version_stdout_path']).read_bytes(), 'self version changed')
    return d


def symbols(nm, path):
    result = subprocess.run([nm, '--extern-only', '--format=darwin', str(path)],
                            check=True, capture_output=True, text=True)
    defs, undefs = {}, set()
    for line in result.stdout.splitlines():
        fields = line.split()
        if 'external' not in fields:
            continue
        name = fields[-1]
        if '(undefined)' in line:
            if 'weak' not in fields:
                undefs.add(name)
        else:
            defs[name] = 'weak' not in fields and '(common)' not in line
    return defs, undefs, result.stdout


def archive_symbols(nm, path):
    text = subprocess.check_output([nm, '--print-file-name', '--extern-only', '--format=darwin', str(path)], text=True)
    members = {}
    for line in text.splitlines():
        if ': ' not in line:
            continue
        owner, body = line.split(': ', 1)
        fields = body.split()
        if 'external' not in fields:
            continue
        defs, undef = members.setdefault(owner, ({}, set()))
        if '(undefined)' in body:
            if 'weak' not in fields:
                undef.add(fields[-1])
        else:
            defs[fields[-1]] = 'weak' not in fields and '(common)' not in body
    return members, text


def archive_support(config):
    text = file(joins(config, 'native_all_support')).read_text()
    block = text[text.index('if os == "macos" or os == "darwin":'):]
    array = re.search(r'return\s*(\[.*?\])', block, re.S)[1]
    array = array.replace('"-L" + macos_prefix + "/lib"', json.dumps('-L'+config['macos_prefix']+'/lib'))
    return json.loads(array)


def providers(obj, runtime_manifest, config, out, runtime_snapshot=None, original_runtime=None):
    c_objects = manifest(runtime_manifest)
    need(len(c_objects) == 39, 'retained core-C manifest must contain exactly 39 objects')
    defs, needed, aggregate, audit = {}, set(), set(), []
    for index, p in enumerate([str(obj), *c_objects]):
        macho(p, 1)
        found, missing, text = symbols(config['nm_path'], p)
        audit.append(str(p)+'\n'+text)
        if index == 0:
            aggregate = set(found)
        needed.update(missing)
        for name, strong in found.items():
            need(not (strong and defs.get(name, False)), 'strong duplicate provider: '+name)
            defs[name] = defs.get(name, False) or strong
    need('___simple_main' in aggregate and defs.get('___simple_main'), 'missing aggregate main')
    needed.difference_update(defs)
    archives, support, selected = [], [], []
    if runtime_snapshot and original_runtime and any(s.startswith(('_rt_', '_spl_', '___simple', '__RN', '_LLVM')) for s in needed):
        authority = {}
        for row in file(runtime_snapshot).read_text().splitlines():
            fields = row.split(':')
            if len(fields) == 4 and fields[0] == 'file-hex':
                authority[bytes.fromhex(fields[1]).decode()] = fields[3]
        pair = [Path(original_runtime)/name for name in ('libsimple_compiler_backfill.a', 'libsimple_native_all.a')]
        members = []
        if all(p.name in authority for p in pair):
            for p in pair:
                need(sha(p) == authority[p.name], 'runtime archive changed')
                table, text = archive_symbols(config['nm_path'], p)
                members.append(table); audit.append(str(p)+'\n'+text)
            # Use the canonical pair only when actual unresolved symbols can
            # select a member. Merely having archives is not a requirement.
            if any(found.keys() & needed for table in members for found, _ in table.values()):
                archives = list(map(str, pair)); support = archive_support(config)
                needed.add('_rt_vulkan_provider_is_available')
                needed.difference_update(defs)
                changed = True
                seen = set()
                while changed:
                    changed = False
                    for table in members:
                        for owner, (found, missing) in table.items():
                            if owner in seen or not (found.keys() & needed):
                                continue
                            seen.add(owner); selected.append(owner); changed = True
                            needed.update(missing)
                            for name, strong in found.items():
                                need(not (strong and defs.get(name, False)), 'strong selected archive duplicate: '+name)
                                defs[name] = defs.get(name, False) or strong
                            needed.difference_update(defs)
    unresolved = sorted(s for s in needed if s.startswith(('_rt_', '_spl_', '___simple', '__RN')))
    need(not unresolved, 'retained provider qualification failed: '+','.join(unresolved))
    for required in ('_spl_init_args', '___simple_runtime_init', '___simple_runtime_shutdown'):
        need(required in defs, 'entry runtime provider missing: '+required)
    init = sorted({s[1:] for s in aggregate if s == '___module_init' or s.startswith('___module_init_')})
    need(all(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', s) for s in init), 'invalid initializer name')
    Path(out, 'providers.nm').write_text('\n'.join(audit))
    Path(out, 'remaining-host-symbols.txt').write_text('\n'.join(sorted(needed))+'\n')
    Path(out, 'module-init-symbols.txt').write_text('\n'.join(init)+'\n')
    Path(out, 'selected-archive-members-model.txt').write_text('\n'.join(selected)+'\n')
    return list(c_objects), init, archives, support


def canonical_shim(template, init):
    text = file(template).read_text()
    chunk = text[text.index('    var c_source ='):text.index('    file_write(entry_c, c_source)')]
    code = ''
    for line in chunk.splitlines():
        m = re.search(r'c_source = (?:c_source \+ )?(".*")$', line)
        if m:
            value = json.loads(m[1])
            code += ''.join(value.replace('{name}', n) for n in init) if '{name}' in value else value
    need(code.count('int main(int argc, char** argv)') == 1, 'noncanonical entry template')
    return code


def tool_argv(producer, original_argv, obj):
    args = list(original_argv)
    need(args and args[0] == 'native-build', 'tool command must be native-build')
    need('--emit-object' not in args and '--mode' not in args, 'unexpected existing tool output mode')
    outputs = [i for i, v in enumerate(args) if v in ('-o', '--output')]
    need(len(outputs) == 1, 'tool output missing/nonunique')
    args[outputs[0]+1] = str(obj)
    return [producer, *args, '--emit-object', '--mode', 'dynload']


def run_command(controller, source, producer, runtime, out, name, argv):
    home, tmp = out/(name+'-home'), out/(name+'-tmp')
    home.mkdir(); tmp.mkdir()
    command = controller/'scripts/bootstrap/run-retained-manual-command.shs'
    return subprocess.run(['sh', str(command), source, str(out/(name+'.log')),
                           str(out/(name+'.transcript')), str(home), str(tmp), producer, runtime,
                           '--', *map(str, argv)], check=False).returncode


def retained_object(out, argv, producer, source, runtime, controller, prepare_only):
    obj, build = out/'aggregate.o', out/'object-build.env'
    if not build.exists():
        need(prepare_only, 'qualified mode requires retained object preparation first')
        need(not obj.exists(), 'unowned retained aggregate')
        (out/'object.argv').write_bytes(b'\0'.join(os.fsencode(x) for x in argv)+b'\0')
        raw = run_command(controller, source, producer, runtime, out, 'object', argv)
        write_env(build, {'raw_status': raw, 'producer_sha256': sha(producer),
                          'object_sha256': sha(obj) if obj.exists() else 'NOT_PRODUCED',
                          'argv_sha256': sha(out/'object.argv')})
    b = env(build)
    eq(b, 'producer_sha256', sha(producer))
    need(file(out/'object.argv').read_bytes() == b'\0'.join(os.fsencode(x) for x in argv)+b'\0', 'retained argv changed')
    eq(b, 'argv_sha256', sha(out/'object.argv'))
    macho(obj, 1); eq(b, 'object_sha256', sha(obj))
    native_log(out/'object.log', b['raw_status'], obj)
    rss(out/'object.log.rss.env', b['raw_status'])
    return obj, build, b


def build_tool(a):
    """Retain object when review is absent. Never turn a raw1 into build raw0."""
    receipt = chain(a.chain, a.selected, a.source, a.original_runtime)
    config = env(joins(receipt, 'toolchain'))
    for name in ('cc', 'nm', 'entry_template'):
        joins(config, name)
    joins(config, 'sdk_settings')
    retained = joins(receipt, 'c_runtime_manifest')
    controller = HERE.parents[2]
    # Existing capsule authority verifies the selected compiler and original
    # retained hosted/runtime artifacts; it performs no Rust/runtime build.
    legacy.verify_capsule_copy(str(Path(a.runtime)/'phase2-runtime-capsule.env'),
                               a.selected, a.source, a.original_runtime)
    need(sha(a.producer) == sha(a.selected), 'tool producer snapshot changed')
    need(a.role in ROLES, 'unknown tool role')
    original = a.argv[1:] if a.argv[:1] == ['--'] else a.argv
    need(original[original.index('--entry')+1] == ROLES[a.role], 'wrong tool role entry')
    need(original[original.index('--runtime-bundle')+1] == 'host-gpu', 'changed role runtime bundle')
    expected_sources = ['src/compiler', 'src/app', 'src/lib']
    if a.role in ('compiler_cli_build', 'test_runner_build'):
        expected_sources = ['src/compositions/kernel_llvm_cranelift', *expected_sources, 'src/os']
    actual_sources = [original[i+1] for i, value in enumerate(original[:-1]) if value == '--source']
    need(actual_sources == expected_sources, 'changed role source closure')
    out = Path(a.work)
    out.mkdir(parents=True, exist_ok=True)
    argv = tool_argv(a.producer, original, out/'aggregate.o')
    obj, build, b = retained_object(out, argv, a.producer, a.source, a.runtime, controller, a.prepare_only)
    qualification = Path(a.qualification)
    if a.prepare_only or not qualification.exists():
        print('retained-manual: independent qualification required: '+str(obj), file=sys.stderr)
        return 86
    q = env(qualification)
    for k, v in {'schema': 'simple-retained-object-qualification-v1', 'artifact_path': str(obj),
                 'artifact_sha256': sha(obj), 'artifact_validation': 'PASS',
                 'coordinator_raw_status': b['raw_status'], 'normal_build_qualification': 'NOT_QUALIFIED'}.items():
        eq(q, k, v)
    reviewed = manifest(joins(q, 'evidence_manifest'))
    for p in (obj, build, out/'object.argv', out/'object.log', out/'object.transcript', out/'object.log.rss.env'):
        need(str(p) in reviewed, 'qualification omitted actual evidence: '+str(p))
    c_objects, init, archives, support = providers(obj, retained, config, out,
                                                receipt['runtime_snapshot_path'], a.original_runtime)
    entry = out/'simple_entry.c'
    entry.write_text(canonical_shim(config['entry_template_path'], init))
    common = ['--target=aarch64-apple-darwin', '-mmacosx-version-min=26.5', '-isysroot', config['sdk_path']]
    artifact = Path(a.output)
    need(not artifact.exists(), 'tool output must be fresh')
    shim_argv = [config['cc_path'], '-c', *common, '-fPIC', '-O2', '-ffunction-sections', '-fdata-sections',
                 '-o', str(out/'simple_entry.o'), str(entry)]
    link_argv = [config['cc_path'], str(obj), *c_objects, str(out/'simple_entry.o'), *archives, *support, *common,
                 '-Wl,-dead_strip', '-Wl,-undefined,error', '-o', str(artifact)]
    link_inputs = {str(p): sha(p) for p in [obj, qualification, retained, Path(a.chain), entry,
                  Path(config['cc_path']), Path(config['nm_path']), Path(config['sdk_settings_path']),
                  Path(config['entry_template_path']), out/'module-init-symbols.txt', *map(Path, c_objects), *map(Path, archives)]}
    if archives:
        link_inputs[config['native_all_support_path']] = config['native_all_support_sha256']
    (out/'link-inputs.manifest').write_text(''.join(h+'|'+p+'\n' for p, h in sorted(link_inputs.items())))
    shim_raw = run_command(controller, a.source, a.producer, a.runtime, out, 'shim', shim_argv)
    link_raw = 'NOT_RUN'
    if shim_raw == 0:
        rss(out/'shim.log.rss.env', 0)
        link_raw = run_command(controller, a.source, a.producer, a.runtime, out, 'link', link_argv)
    guard = 1
    if link_raw == 0:
        rss(out/'link.log.rss.env', 0); macho(artifact, 2)
        manifest(out/'link-inputs.manifest')
        chain(a.chain, a.selected, a.source, a.original_runtime)
        guard = 0
    write_env(out/'link-result.env', {'shim_raw_status': shim_raw, 'link_raw_status': link_raw,
              'guard_validation_status': guard, 'boundaries': 'PASS' if guard == 0 else 'FAIL',
              'artifact_sha256': sha(artifact) if artifact.exists() else 'NOT_PRODUCED'})
    need(guard == 0, 'manual tool link failed')
    entries = [obj, artifact, build, out/'object.log', out/'object.transcript', out/'object.log.rss.env',
               qualification, out/'link-result.env', out/'link-inputs.manifest',
               out/'shim.transcript', out/'shim.log.rss.env', out/'link.transcript', out/'link.log.rss.env', Path(retained), Path(receipt['runtime_snapshot_path']),
               entry, out/'simple_entry.o', out/'module-init-symbols.txt', Path(receipt['toolchain_path'])]
    (out/'inputs.manifest').write_text(''.join(sha(p)+'|'+str(p)+'\n' for p in entries))
    data = {'schema': 'simple-retained-manual-product-v1', 'role': a.role, 'producer_path': a.producer,
            'producer_sha256': sha(a.producer), 'source_root': a.source,
            'source_head': git(a.source, 'rev-parse', 'HEAD').decode().strip(),
            'source_tree': git(a.source, 'rev-parse', 'HEAD^{tree}').decode().strip(),
            'entry': ROLES[a.role], 'runtime_path': a.runtime, 'build_raw_status': b['raw_status'],
            'cc_path': config['cc_path'], 'cc_sha256': config['cc_sha256'],
            'archive_paths': json.dumps(archives), 'original_runtime_path': a.original_runtime,
            'runtime_snapshot_sha256': receipt['runtime_snapshot_sha256']}
    for key, p in {'object': obj, 'artifact': artifact, 'inputs': out/'inputs.manifest',
                   'build_log': out/'object.log', 'build_transcript': out/'object.transcript',
                   'build_rss': out/'object.log.rss.env', 'qualification': qualification,
                   'link_result': out/'link-result.env', 'link_inputs': out/'link-inputs.manifest',
                   'shim_transcript': out/'shim.transcript', 'shim_rss': out/'shim.log.rss.env',
                   'link_transcript': out/'link.transcript', 'link_rss': out/'link.log.rss.env',
                   'c_runtime_manifest': Path(retained), 'runtime_snapshot': Path(receipt['runtime_snapshot_path']),
                   'shim_source': entry, 'shim_object': out/'simple_entry.o', 'module_init': out/'module-init-symbols.txt',
                   'toolchain': Path(receipt['toolchain_path'])}.items():
        data[key+'_path'], data[key+'_sha256'] = str(p), sha(p)
    write_env(out/'product.env', data)
    product(out/'product.env', producer=a.producer, source=a.source, runtime=a.runtime)
    # Existing controller role-specific help/stdio/essential-tools and whole
    # repository gates remain mandatory; this receipt is build readiness only.
    return 0


def candidate(path, binary, source):
    d = env(path)
    eq(d, 'schema', 'simple-stage4-retained-manual-provenance-v1')
    eq(d, 'output_path', binary); eq(d, 'output_sha256', sha(binary)); macho(binary, 2)
    eq(d, 'source_root', source)
    bundle = manifest(joins(d, 'controller_bundle'))
    controller = Path(joins(d, 'controller'))
    controller_root = controller.parents[2]
    expected_bundle = {str(controller), str(controller_root/'scripts/check/lib/stage4-retained-manual.py'),
          str(controller_root/'scripts/check/lib/stage4-retained-self-evidence.py'),
          str(controller_root/'scripts/bootstrap/run-retained-manual-command.shs'),
          str(controller_root/'scripts/check/lib/stage4-candidate-provenance.shs')}
    need(set(bundle) == expected_bundle, 'controller bundle members changed')
    parent = joins(d, 'parent_compiler')
    authority = chain(joins(d, 'chain'), parent, source, d['original_runtime_path'])
    config = env(joins(authority, 'toolchain'))
    legacy.verify_capsule_copy(joins(d, 'runtime_capsule_receipt'), parent, source, d['original_runtime_path'])
    products = {}
    for role in ROLES:
        products[role] = product(joins(d, role), source=source, runtime=d['runtime_path'])
        eq(products[role], 'producer_sha256', sha(parent))
        eq(products[role], 'role', role)
        eq(products[role], 'c_runtime_manifest_path', authority['c_runtime_manifest_path'])
        eq(products[role], 'c_runtime_manifest_sha256', authority['c_runtime_manifest_sha256'])
        eq(products[role], 'cc_path', config['cc_path']); eq(products[role], 'cc_sha256', config['cc_sha256'])
        eq(products[role], 'toolchain_path', authority['toolchain_path'])
        eq(products[role], 'toolchain_sha256', authority['toolchain_sha256'])
        eq(products[role], 'original_runtime_path', d['original_runtime_path'])
        eq(products[role], 'runtime_snapshot_sha256', authority['runtime_snapshot_sha256'])
    eq(products['compiler_cli_build'], 'artifact_path', binary)
    owners = env(joins(d, 'command_owner'))
    eq(owners, 'schema', 'simple-bootstrap-command-owners-v3'); eq(owners, 'phase', 'stage4')
    eq(owners, 'status', 'frozen'); eq(owners, 'compiler_snapshot_sha256', sha(parent))
    for key, role in [('compiler_cli', 'compiler_cli_build'), ('test_runner', 'test_runner_build'), ('mcp_server', 'mcp_build')]:
        eq(owners, key+'_path', products[role]['artifact_path'])
        eq(owners, key+'_sha256', products[role]['artifact_sha256'])
    tools = env(joins(d, 'tooling_owner'))
    eq(tools, 'schema', 'simple-bootstrap-stage4-tooling-owners-v1'); eq(tools, 'status', 'frozen')
    eq(tools, 'phase', 'stage4'); eq(tools, 'compiler_snapshot_sha256', sha(parent))
    joins(tools, 'compiler_snapshot')
    eq(tools, 'command_owner_receipt_path', d['command_owner_path'])
    eq(tools, 'command_owner_receipt_sha256', d['command_owner_sha256'])
    eq(tools, 'hosted_runtime_path', d['runtime_path'])
    for key, role in [('mcp_server', 'mcp_build'), ('lsp_server', 'lsp_build')]:
        eq(tools, key+'_path', products[role]['artifact_path'])
        eq(tools, key+'_sha256', products[role]['artifact_sha256'])
    smoke = env(joins(d, 'smoke'))
    eq(smoke, 'schema', 'simple-phase-verification-command-v1')
    eq(smoke, 'task', 'stage4_essential_tools'); eq(smoke, 'status', 0); eq(smoke, 'source_root', source)
    log = bound(smoke, 'log_path', 'log_sha256')
    eq(d, 'smoke_log_path', log); eq(d, 'smoke_log_sha256', sha(log))
    rss(bound(smoke, 'rss_receipt_path', 'rss_receipt_sha256'), 0)
    selectors = env(bound(smoke, 'selector_environment_path', 'selector_environment_sha256'))
    for key in FORBIDDEN:
        eq(selectors, key, 'absent')
    args = file(bound(smoke, 'argv_path', 'argv_sha256')).read_text().splitlines()
    need(args == ['env', 'SIMPLE_BINARY='+binary, 'sh', source+'/scripts/check/check-bootstrap-essential-tools-smoke.shs'], 'essential tools command changed')
    lines = file(log).read_text().splitlines()
    for marker in ('essential_tools_pure_simple_identity=true', 'essential_test_runner_smoke=true',
                   'essential_lint_smoke=true', 'essential_duplicate_checker_smoke=true', 'bootstrap_essential_tools_smoke=true'):
        need(lines.count(marker) == 1, 'missing/duplicate essential verdict: '+marker)
    eq(d, 'whole_suite_status', 'NOT_CLAIMED')
    return d


def publish_candidate(a):
    data = {'schema': 'simple-stage4-retained-manual-provenance-v1', 'status': 'pass',
            'output_path': a.artifact, 'output_sha256': sha(a.artifact), 'source_root': a.source,
            'original_runtime_path': a.original_runtime, 'runtime_path': a.runtime,
            'whole_suite_status': 'NOT_CLAIMED'}
    paths = {'chain': a.chain, 'parent_compiler': a.selected, 'command_owner': a.command_owner,
             'tooling_owner': a.tooling_owner, 'smoke': a.smoke, 'smoke_log': a.smoke_log,
             'controller': a.controller, 'validator': str(Path(__file__).resolve()),
             'runtime_capsule_receipt': str(Path(a.runtime)/'phase2-runtime-capsule.env'),
             'controller_bundle': a.controller_bundle}
    paths.update({role: str(Path(a.work)/role/'product.env') for role in ROLES})
    for name, p in paths.items():
        data[name+'_path'], data[name+'_sha256'] = p, sha(p)
    request = Path(a.work)/'candidate.request.env'
    write_env(request, data)
    candidate(request, a.artifact, a.source)
    output = Path(a.artifact+'.provenance.env')
    need(not output.exists(), 'candidate provenance exists')
    output.write_bytes(request.read_bytes()); output.chmod(0o400)
    candidate(output, a.artifact, a.source)


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('verify-chain')
    p.add_argument('receipt'); p.add_argument('compiler'); p.add_argument('source'); p.add_argument('runtime')
    p = sub.add_parser('verify-product'); p.add_argument('receipt')
    p = sub.add_parser('verify-candidate'); p.add_argument('receipt'); p.add_argument('compiler'); p.add_argument('source')
    p = sub.add_parser('publish-candidate')
    for name in ('chain', 'selected', 'source', 'original-runtime', 'runtime', 'work', 'artifact',
                 'command-owner', 'tooling-owner', 'smoke', 'smoke-log', 'controller', 'controller-bundle'):
        p.add_argument('--'+name, required=True)
    p = sub.add_parser('build-tool')
    for name in ('chain', 'selected', 'source', 'original-runtime', 'runtime', 'producer', 'role', 'work', 'qualification', 'output'):
        p.add_argument('--'+name, required=True)
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('argv', nargs=argparse.REMAINDER)
    a = parser.parse_args()
    if a.command == 'verify-chain':
        chain(a.receipt, a.compiler, a.source, a.runtime)
    elif a.command == 'verify-product':
        product(a.receipt)
    elif a.command == 'verify-candidate':
        candidate(a.receipt, a.compiler, a.source)
    elif a.command == 'publish-candidate':
        publish_candidate(a)
    else:
        return build_tool(a)


if __name__ == '__main__':
    try:
        sys.exit(main() or 0)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print('retained-manual: '+str(error), file=sys.stderr)
        sys.exit(1)
