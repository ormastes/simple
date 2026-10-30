#!/usr/bin/env python3
"""Validate retained native self-build evidence, without executing an artifact.

This is an explicit alternative input contract, not a canonical Stage3 manifest.
The caller additionally checks canonical source/runtime directory snapshots.
"""
import hashlib
import os
from pathlib import Path
import subprocess
import sys


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def file(path):
    p = Path(path)
    need(p.is_absolute() and p.is_file() and not p.is_symlink(), 'regular absolute file: ' + str(p))
    return p


def sha(path):
    h = hashlib.sha256()
    with file(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def env(path):
    result = {}
    for line in file(path).read_text().splitlines():
        key, sep, value = line.partition('=')
        need(sep and key and key not in result, 'malformed/duplicate receipt key: ' + key)
        need('PENDING' not in value, 'pending authority: ' + key)
        result[key] = value
    return result


def eq(data, key, value):
    need(data.get(key) == str(value), 'field mismatch: ' + key)


def bound(data, path_key, hash_key):
    path = data[path_key]
    eq(data, hash_key, sha(path))
    return path


def manifest(path):
    seen = {}
    for row in file(path).read_text().splitlines():
        parts = row.split('|')
        need(len(parts) == 2, 'invalid immutable input row')
        path, digest = parts
        need(path not in seen or seen[path] == digest, 'conflicting immutable input row')
        need(sha(path) == digest, 'immutable input changed: ' + path)
        seen[path] = digest
    need(seen, 'empty immutable manifest')
    return seen


def rss(path, jobs=None):
    d = env(path)
    for key, value in [('status', 'complete'), ('exit_status', '0'), ('quiescent', '1'),
                       ('rss_cap_mode', 'enforce'), ('rss_cap_enforced', '1'),
                       ('observer_errors', '0'), ('observer_restarts', '0'),
                       ('measurement_budget_complete', '1'), ('sample_budget_exceeded', '0')]:
        eq(d, key, value)
    if jobs is not None:
        eq(d, 'compiler_jobs', jobs)
    need(int(d['max_rss_kib']) > 0, 'missing RSS cap')


def transcript(path, binary, root, args_prefix):
    lines = file(path).read_text().splitlines()
    need(lines[0] == 'schema=simple-bootstrap-command-transcript-v2', 'transcript schema')
    rows = {}
    for line in lines[1:]:
        if line == 'runtime-env-contract:bootstrap-session-v1':
            continue
        key, length, value = line.split(':', 2)
        need(int(length) == len(value.encode()), 'transcript byte length')
        rows.setdefault(key, []).append(value)
    need(rows.get('cwd') == [root], 'transcript cwd')
    need(rows.get('executable') == [binary], 'transcript executable')
    args = rows.get('argv', [])
    need(args[:len(args_prefix)] == args_prefix, 'transcript argv')
    return args, rows.get('explicit-env', [])


def gates(path, binary, result_path, root, runtime_digest, original_runtime):
    g = env(path)
    eq(g, 'schema', 'aliasfix-p3-version-hello-gates-v1')
    eq(g, 'p3_path', binary); eq(g, 'p3_sha256', sha(binary))
    eq(g, 'p3_result', result_path); eq(g, 'p3_result_sha256', sha(result_path))
    eq(g, 'runtime_snapshot_sha256', runtime_digest)
    for key in ('p3_version_status', 'p3_native_hello_build_status', 'p3_native_hello_run_status'):
        eq(g, key, 0)
    eq(g, 'p3_version_match_p2', 1)
    manifest(bound(g, 'inputs_manifest', 'inputs_manifest_sha256'))
    base = file(path).parent
    hello = bound(g, 'hello_binary', 'hello_binary_sha256')
    need(os.access(hello, os.X_OK), 'Hello not executable')
    for name, key, output, jobs, prefix in (
            ('p3-version', 'version_receipt_sha256', binary, 0, ['--version']),
            ('p3-hello-build', 'hello_build_receipt_sha256', hello, 10, ['native-build']),
            ('p3-hello-run', 'hello_run_receipt_sha256', hello, 0, [])):
        rp = str(base / (name + '.env')); eq(g, key, sha(rp)); r = env(rp)
        eq(r, 'task', name); eq(r, 'raw_status', 0); eq(r, 'output_path', output)
        log = bound(r, 'log_path', 'log_sha256')
        tr = bound(r, 'transcript_path', 'transcript_sha256')
        rss(bound(r, 'rss_receipt_path', 'rss_receipt_sha256'), jobs)
        args, settings = transcript(tr, hello if name == 'p3-hello-run' else binary, root, prefix)
        settings_map = {}
        for setting in settings:
            key, value = setting.split('=', 1)
            need(key not in settings_map, 'duplicate explicit environment')
            settings_map[key] = value
        eq(settings_map, 'DYLD_LIBRARY_PATH', original_runtime)
        need(not any(v.split('=', 1)[0] in ('SIMPLE_NATIVE_BUILD_RUST', 'SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4') for v in settings), 'forbidden gate selector')
        if name == 'p3-hello-run': need(args == [], 'Hello run arguments')
        if name == 'p3-version': need(args == ['--version'], 'version arguments')
        if name == 'p3-hello-build':
            eq(settings_map, 'SIMPLE_RUNTIME_PATH', original_runtime)
            eq(settings_map, 'SIMPLE_BINARY', binary)
            eq(settings_map, 'SIMPLE_BOOTSTRAP', '1')
            for flag, expected in (('--runtime-path', original_runtime), ('--mode', 'one-binary'), ('--entry', root + '/test/04_smoke/bootstrap_hello_world.spl'), ('-o', hello)):
                need(args.count(flag) == 1 and args[args.index(flag) + 1] == expected, 'Hello ' + flag)
        if name == 'p3-hello-run':
            eq(g, 'hello_run_log', log); need(file(log).read_bytes() == b'hello\n', 'Hello output')
        if name == 'p3-version':
            eq(g, 'version_log', log)
            need(file(log).read_bytes().startswith(b'simple-bootstrap '), 'version banner')
    return g


def verify_self(result_path, selected, root, original_runtime, selected_gates):
    r = env(result_path)
    eq(r, 'schema', 'aliasfix-p3-self-rebuild-v1')
    eq(r, 'diagnostic_only', 1); eq(r, 'admission_status', 'NOT_ATTEMPTED')
    eq(r, 'publication_status', 'NOT_ATTEMPTED'); eq(r, 'native_build_raw_status', 0)
    eq(r, 'source_root', root); eq(r, 'p3b_path', selected); eq(r, 'p3b_sha256', sha(selected))
    need(os.access(selected, os.X_OK), 'selected P3b not executable')
    head = subprocess.check_output(['git', '-C', root, 'rev-parse', 'HEAD'], text=True).strip()
    eq(r, 'source_head', head)
    need(not subprocess.check_output(['git', '-C', root, 'status', '--porcelain', '--untracked-files=all']), 'dirty source')
    eq(r, 'runtime_generation', Path(original_runtime).name)
    manifest(bound(r, 'inputs_manifest', 'inputs_manifest_sha256'))
    p = env(bound(r, 'producer_result', 'producer_result_sha256'))
    eq(p, 'schema', 'aliasfix-p3-diagnostic-v1'); eq(p, 'source_root', root); eq(p, 'source_head', head)
    eq(p, 'runtime_snapshot_sha256', r['runtime_snapshot_sha256'])
    eq(p, 'p3_path', r['producer_path']); eq(p, 'p3_sha256', r['producer_sha256'])
    eq(r, 'producer_sha256', sha(r['producer_path']))
    manifest(bound(p, 'immutable_inputs_manifest', 'immutable_inputs_manifest_sha256'))
    eq(p, 'source_snapshot_before_sha256', r['source_snapshot_sha256'])
    pb = env(bound(p, 'p3_build_receipt', 'p3_build_receipt_sha256'))
    eq(pb, 'raw_status', 0); eq(pb, 'p3_output', r['producer_path'])
    for receipt_key, result_key, hash_key in (
            ('p3_log', 'p3_log', 'p3_log_sha256'), ('p3_transcript', 'p3_transcript', 'p3_transcript_sha256'),
            ('p3_rss_receipt', 'p3_rss', 'p3_rss_sha256')):
        eq(pb, receipt_key, bound(p, result_key, hash_key))
    rss(p['p3_rss'], 10)
    transcript(p['p3_transcript'], p['p2_path'], root, ['native-build'])
    eq(p, 'p2_sha256', sha(p['p2_path'])); eq(p, 'dropped_to_wildcard', 0)

    pg = gates(bound(r, 'producer_gates', 'producer_gates_sha256'), r['producer_path'], r['producer_result'], root, r['runtime_snapshot_sha256'], original_runtime)
    g = gates(selected_gates, selected, result_path, root, r['runtime_snapshot_sha256'], original_runtime)
    eq(g, 'source_head', head)
    need(file(g['version_log']).read_bytes() == file(pg['version_log']).read_bytes(), 'self producer version changed')
    b = env(bound(r, 'build_receipt', 'build_receipt_sha256'))
    eq(b, 'raw_status', 0); eq(b, 'p3b_output', selected)
    for receipt_key, result_key, hash_key in (
            ('p3b_log', 'log_path', 'log_sha256'),
            ('p3b_transcript', 'transcript_path', 'transcript_sha256'),
            ('p3b_rss_receipt', 'rss_receipt_path', 'rss_receipt_sha256')):
        eq(b, receipt_key, bound(r, result_key, hash_key))
    rss(r['rss_receipt_path'], 10)
    args, settings = transcript(r['transcript_path'], r['producer_path'], root, ['native-build'])
    need(not any(v.split('=', 1)[0] in ('SIMPLE_NATIVE_BUILD_RUST', 'SIMPLE_BOOTSTRAP', 'SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4') for v in settings), 'self build selector')
    for flag, expected in (('--mode', 'dynload'), ('--entry', 'src/app/cli/bootstrap_main.spl'), ('-o', selected), ('--runtime-path', original_runtime)):
        need(args.count(flag) == 1 and args[args.index(flag) + 1] == expected, 'self build ' + flag)
    sources = [args[i + 1] for i, arg in enumerate(args[:-1]) if arg == '--source']
    need(sources == ['src/compositions/kernel_llvm_cranelift', 'src/compositions/cuda_static', 'src/compiler', 'src/app', 'src/lib', 'src/plugins'], 'self build source roots')
    eq(r, 'dropped_to_wildcard', 0)
    with file(r['log_path']).open() as log:
        need(not any('DROPPED to wildcard' in line for line in log), 'dropped pattern')
    return r


def verify_capsule_copy(receipt_path, selected, root, original_runtime):
    capsule = env(receipt_path)
    need(capsule['schema'] in ('simple-phase2-runtime-capsule-v1', 'simple-phase2-runtime-capsule-v2'), 'capsule schema')
    eq(capsule, 'status', 'frozen'); eq(capsule, 'compiler_sha256', sha(selected))
    eq(capsule, 'source_authority_path', original_runtime)
    capsule_dir = file(receipt_path).parent
    for rel in ('libsimple_native_all.a', 'hosted-runtime.env', 'simple.inputs.sha256'):
        need(sha(str(capsule_dir / rel)) == sha(str(Path(original_runtime) / rel)), 'runtime copy changed: ' + rel)
    hosted_relative = env(str(capsule_dir / 'hosted-runtime.env'))['relative_path']
    need(hosted_relative.startswith('deps/') and '/' not in hosted_relative[5:] and
         hosted_relative[5:].startswith('libspl_hosted_runtime') and hosted_relative.endswith('.rlib'), 'hosted relative path')
    need(sha(str(capsule_dir / hosted_relative)) == sha(str(Path(original_runtime) / hosted_relative)), 'hosted runtime copy changed')
    for rel in ('libsimple_runtime.dylib', 'libspl_cocoa.dylib', 'libspl_cocoa.producer.txt', 'libsimple_compiler_backfill.a'):
        source = Path(original_runtime) / rel; copied = capsule_dir / rel
        need(source.exists() == copied.exists() and not source.is_symlink() and not copied.is_symlink(), 'optional runtime membership: ' + rel)
        if source.exists(): need(sha(str(source)) == sha(str(copied)), 'optional runtime copy changed: ' + rel)
    # Existing capsule verifier also checks dynamic libraries, optional Cocoa and stamp joins.
    subprocess.run(['sh', root + '/scripts/bootstrap/phase2-runtime-capsule.shs', 'verify', str(capsule_dir)], check=True, stdout=subprocess.DEVNULL)
    return capsule_dir


def verify_candidate(path, binary, root):
    c = env(path)
    eq(c, 'schema', 'simple-stage4-retained-self-provenance-v1')
    eq(c, 'status', 'pass'); eq(c, 'artifact_kind', 'pure-simple-full-cli')
    eq(c, 'output_path', binary); eq(c, 'output_sha256', sha(binary))
    need(os.access(binary, os.X_OK), 'candidate not executable')
    eq(c, 'source_root', root)
    for key in ('self_result', 'selected_sanity', 'command_owner', 'tooling_owner',
                'runtime_capsule_receipt', 'controller', 'helper', 'evidence_validator',
                'essential_tools_owner', 'build_receipt', 'smoke_receipt'):
        bound(c, key + '_path', key + '_sha256')
    tool_scripts = Path(__file__).resolve().parents[2]
    eq(c, 'controller_path', str(tool_scripts / 'bootstrap/bootstrap-phase-verification.shs'))
    eq(c, 'helper_path', str(tool_scripts / 'check/lib/stage4-candidate-provenance.shs'))
    eq(c, 'evidence_validator_path', str(Path(__file__).resolve()))
    eq(c, 'essential_tools_owner_path', root + '/scripts/check/check-bootstrap-essential-tools-smoke.shs')
    selected = c['parent_compiler_path']; eq(c, 'parent_compiler_sha256', sha(selected))
    r = verify_self(c['self_result_path'], selected, root, c['original_runtime_path'], c['selected_sanity_path'])
    eq(c, 'source_head', r['source_head']); eq(c, 'source_snapshot_sha256', r['source_snapshot_sha256'])
    tree = subprocess.check_output(['git', '-C', root, 'rev-parse', 'HEAD^{tree}'], text=True).strip()
    eq(c, 'source_tree', tree)
    eq(c, 'runtime_snapshot_sha256', r['runtime_snapshot_sha256'])
    capsule_dir = verify_capsule_copy(c['runtime_capsule_receipt_path'], selected, root, c['original_runtime_path'])
    eq(c, 'runtime_path', str(capsule_dir))
    cmd = env(c['command_owner_path']); tools = env(c['tooling_owner_path'])
    eq(cmd, 'schema', 'simple-bootstrap-command-owners-v3'); eq(cmd, 'status', 'frozen'); eq(cmd, 'phase', 'stage4')
    eq(cmd, 'compiler_snapshot_sha256', sha(selected)); eq(cmd, 'compiler_cli_path', binary); eq(cmd, 'compiler_cli_sha256', sha(binary))
    for key in ('test_runner', 'mcp_server'):
        member = bound(cmd, key + '_path', key + '_sha256'); need(os.access(member, os.X_OK), 'tool not executable')
    eq(tools, 'schema', 'simple-bootstrap-stage4-tooling-owners-v1'); eq(tools, 'status', 'frozen'); eq(tools, 'phase', 'stage4')
    eq(tools, 'compiler_snapshot_sha256', sha(selected))
    bound(tools, 'compiler_snapshot_path', 'compiler_snapshot_sha256')
    eq(tools, 'command_owner_receipt_path', c['command_owner_path']); eq(tools, 'command_owner_receipt_sha256', sha(c['command_owner_path']))
    eq(tools, 'hosted_runtime_path', str(capsule_dir))
    hosted = env(str(capsule_dir / 'hosted-runtime.env'))
    eq(tools, 'hosted_runtime_sha256', hosted['sha256'])
    for key in ('mcp_server', 'lsp_server'):
        member = bound(tools, key + '_path', key + '_sha256'); need(os.access(member, os.X_OK), 'service not executable')
    eq(tools, 'mcp_server_path', cmd['mcp_server_path']); eq(tools, 'mcp_server_sha256', cmd['mcp_server_sha256'])
    for key, task in (('build_receipt', 'compiler_cli_build'), ('smoke_receipt', 'stage4_essential_tools')):
        receipt = env(c[key + '_path'])
        eq(receipt, 'schema', 'simple-phase-verification-command-v1'); eq(receipt, 'task', task)
        eq(receipt, 'status', 0); eq(receipt, 'source_root', root)
        log = bound(receipt, 'log_path', 'log_sha256')
        rss(bound(receipt, 'rss_receipt_path', 'rss_receipt_sha256'))
        argv_path = bound(receipt, 'argv_path', 'argv_sha256')
        selectors = env(bound(receipt, 'selector_environment_path', 'selector_environment_sha256'))
        for selector_key in ('SIMPLE_BOOTSTRAP', 'SIMPLE_NATIVE_BUILD_RUST', 'SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4', 'SIMPLE_BOOTSTRAP_WHOLE_PROGRAM', 'SIMPLE_TEST_RUNNER_RUST'):
            eq(selectors, selector_key, 'absent')
        argv = file(argv_path).read_text().splitlines()
        if key == 'build_receipt':
            eq(receipt, 'artifact_sha256', sha(binary)); eq(receipt, 'artifact_path', binary)
            need(len(argv) > 2 and sha(argv[0]) == sha(selected) and argv[1] == 'native-build', 'actual CLI producer')
            need('--entry' in argv and argv[argv.index('--entry') + 1] == 'src/app/cli/_CliMain/main_and_help.spl', 'full CLI entry')
            need('--output' in argv and argv[argv.index('--output') + 1] == binary, 'full CLI output')
        else:
            need(argv == ['env', 'SIMPLE_BINARY=' + binary, 'sh', c['essential_tools_owner_path']], 'essential smoke command')
            eq(c, 'essential_tools_log_path', log); eq(c, 'essential_tools_log_sha256', sha(log))
            lines = file(log).read_text().splitlines()
            for marker in ('essential_tools_pure_simple_identity=true', 'essential_test_runner_smoke=true',
                           'essential_lint_smoke=true', 'essential_duplicate_checker_smoke=true',
                           'bootstrap_essential_tools_smoke=true'):
                need(lines.count(marker) == 1, 'missing/duplicate smoke verdict: ' + marker)
    eq(c, 'completed_gate', 'stage4-essential-tools-smoke')
    eq(c, 'whole_suite_status', 'NOT_CLAIMED')


def main():
    if len(sys.argv) == 7 and sys.argv[1] == 'verify-self':
        verify_self(*sys.argv[2:])
    elif len(sys.argv) == 6 and sys.argv[1] == 'verify-capsule-copy':
        verify_capsule_copy(*sys.argv[2:])
    elif len(sys.argv) == 5 and sys.argv[1] == 'verify-candidate':
        verify_candidate(*sys.argv[2:])
    else:
        raise ValueError('invalid retained evidence verifier arguments')
    print('retained_self_evidence=verified')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as exc:
        print('retained_self_evidence_error=' + str(exc), file=sys.stderr)
        sys.exit(1)
