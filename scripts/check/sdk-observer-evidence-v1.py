#!/usr/bin/env python3
"""Bounded observer evidence checks; does not execute a compiler or infer a fix."""
import argparse
import hashlib
import json
import pathlib
import re
import struct

if not __debug__:
    raise RuntimeError('evidence checks require Python assertions enabled')


def digest(path):
    hashed = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            hashed.update(block)
    return hashed.hexdigest()


def pairs(path, separator):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        key, value = line.split(separator, 1)
        assert key not in result, f'duplicate field {key}'
        result[key] = value.strip()
    return result


def bind(args):
    root = pathlib.Path(args.root)
    compiler = root / 'handoff/linux-x86_64-p1/simple'
    phase = root / 'handoff/linux-x86_64-p1/PHASE'
    diag = root / 'diagnostics'
    evidence = diag / 'evidence'
    assert compiler.is_file() and not compiler.is_symlink()
    assert phase.read_bytes() == b'1\n'
    assert compiler.stat().st_size == int(args.bytes)
    assert digest(compiler) == args.sha256
    with compiler.open('rb') as stream:
        header = stream.read(64)
    assert header[:6] == b'\x7fELF\x02\x01'
    assert struct.unpack_from('<HH', header, 16) == (2, 62)
    preflight = pairs(evidence / 'seed-preflight.env', '=')
    seed = diag / 'producer/simple'
    assert seed.is_file() and not seed.is_symlink()
    assert digest(seed) == args.seed_sha256 == preflight['seed_sha256']
    assert preflight['schema'] == 'simple-bootstrap-preflight-v1'
    assert preflight['status'] == 'pass' and preflight['git_head'] == args.source
    bindings = evidence / 'seed-preflight-bindings'
    assert digest(bindings / 'source-inputs.txt') == preflight['source_snapshot_sha256']
    assert digest(bindings / 'git-state.env') == preflight['git_state_sha256']
    assert pairs(bindings / 'git-state.env', '=')['head'] == args.source
    selected = {'src/compiler/00.common/sdk_errno_observer_v1.spl',
                'src/compiler/20.hir/hir_lowering/types.spl',
                'src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl',
                'src/compiler/80.driver/driver_hir_pipeline_lowering.spl'}
    manifest = bindings / 'source-inputs.txt'
    assert manifest.stat().st_size <= 32 * 1024 * 1024
    seen = set()
    for line in manifest.read_text().splitlines():
        if not line.startswith('file-hex:'):
            continue
        parts = line.split(':')
        assert len(parts) == 5
        name = bytes.fromhex(parts[2]).decode('utf-8')
        if name in selected:
            assert name not in seen, 'duplicate selected source witness'
            assert parts[4] == digest(pathlib.Path(args.control_root) / name)
            seen.add(name)
    assert seen == selected, 'instrumented producer source witnesses missing'
    hello = evidence / 'hello'
    assert (hello / 'exit-status').read_bytes().strip() == b'0'
    assert (hello / 'stdout').read_bytes() in (b'phase-ladder-1-ok\n', b'phase-ladder-1-ok\r\n')
    assert (hello / 'stderr').stat().st_size == 0
    link = pairs(hello / 'hello.link-receipt', ':')
    assert link['simple-link-receipt'] == '1'
    assert digest(hello / 'hello') == link['output-sha256']
    output = root / 'producer-binding.sdn'
    output.write_text('schema: sdk-observer-producer-binding-v1\n'
                      f'producer_source: {args.source}\nproducer_sha256: {args.sha256}\n'
                      f'producer_bytes: {args.bytes}\nphase: 1\nseed_sha256: {args.seed_sha256}\n'
                      f'retained_hello_sha256: {link["output-sha256"]}\n'
                      'retained_hello_exit: 0\nhello_rerun: false\n'
                      'qualification: provisional-diagnostic-only\nsdk_qualification: BLOCKED\np3: skipped\n')


def records(args):
    path = pathlib.Path(args.log)
    assert path.stat().st_size <= 64 * 1024 * 1024, 'log exceeds 64MiB bound'
    raw = path.read_bytes()
    lines = raw.splitlines(keepends=True)
    blocks, active = [], None
    for line in lines:
        if line.startswith(b'sdk-observer-begin: '):
            assert active is None, 'nested/interleaved record'
            active = bytearray()
        if active is not None:
            active.extend(line)
            assert len(active) <= 2048, 'record exceeds byte bound'
            if line.startswith(b'sdk-observer-end: '):
                assert line.endswith(b'\n'), 'incomplete terminal line'
                blocks.append(bytes(active))
                assert len(blocks) <= 1024, 'record inventory exceeds bound'
                active = None
        elif b'sdk-observer-' in line:
            raise AssertionError('orphan observer fragment')
    assert active is None, 'unterminated observer record'
    assert blocks, 'no actual worker observer records'
    groups = {}
    rows = []
    required = {'sdk-observer-begin', 'schema', 'sequence', 'process_id',
                'initialization_scope', 'module_name', 'importer', 'normalized_importer',
                'wanted', 'branch', 'registry_generation', 'registry_count', 'facade_index',
                'memo_slot', 'terminal_index', 'terminal_item', 'found', 'complete', 'valid',
                'owner_generation', 'owner_count', 'owner_frozen', 'body_generation',
                'body_count', 'body_frozen', 'sdk-observer-end'}
    for block in blocks:
        fields = {}
        for line in block.decode('utf-8').splitlines():
            key, value = line.split(': ', 1)
            assert key not in fields, f'duplicate record key {key}'
            fields[key] = value
        assert set(fields) == required, 'incomplete/unavailable/foreign record'
        assert fields['schema'] == 'sdk-worker-reexport-observation-v1'
        seq, pid = int(fields['sequence']), int(fields['process_id'])
        assert pid > 0 and 0 <= seq < 8
        assert int(fields['sdk-observer-begin']) == seq == int(fields['sdk-observer-end'])
        assert fields['initialization_scope'] == '0'
        for key in ('found', 'complete', 'valid', 'owner_frozen', 'body_frozen'):
            assert fields[key] in ('true', 'false')
        for key in ('registry_generation', 'registry_count', 'facade_index', 'memo_slot',
                    'terminal_index', 'owner_generation', 'owner_count', 'body_generation', 'body_count'):
            int(fields[key])
        for key in ('module_name', 'importer', 'normalized_importer', 'wanted', 'branch', 'terminal_item'):
            fields[key] = json.loads(fields[key])  # SDN quoted-string interoperability only.
        assert fields['normalized_importer'] == fields['importer'].replace('\\', '/')
        assert fields['normalized_importer'].endswith('/nogc_sync_mut/io/path_identity.spl')
        assert fields['wanted'] == 'path_errno_address'
        allowed = {'registry-invalid', 'index-bounds', 'physical-index', 'generation',
                   'memo-verified-negative', 'memo-negative-recheck-found',
                   'memo-negative-recheck-miss', 'memo-terminal-bounds',
                   'memo-positive', 'fresh-found', 'fresh-miss', 'registered-hop'}
        if args.kind == 'sdk':
            assert fields['branch'] in allowed
            assert args.data_root, 'SDK capture requires physical frozen-data binding'
            data = pathlib.Path(args.data_root).resolve(strict=True)
            expected = data / 'src/lib/nogc_sync_mut/io/path_identity.spl'
            actual = pathlib.Path(fields['normalized_importer'])
            if not actual.is_absolute():
                actual = data / actual
            assert actual.resolve(strict=True) == expected.resolve(strict=True)
        group = groups.setdefault(pid, set())
        assert seq not in group, 'duplicate PID/sequence'
        group.add(seq)
        if args.kind == 'control':
            assert fields['branch'] == 'enabled-native-control'
            assert fields['module_name'] == 'fixture.module'
            assert fields['owner_generation'] == '17' and fields['body_generation'] == '19'
            assert fields['terminal_index'] == '126' and fields['terminal_item'] == 'path_errno_address'
            assert fields['found'] == 'true'
        rows.append((pid, seq, fields['branch']))
    for group in groups.values():
        assert group == set(range(max(group) + 1)), 'missing sequence in retained capture'
    if args.kind == 'control':
        assert len(groups) == 1 and len(blocks) == 8, 'enabled control did not exercise actual shared cap'
    out = pathlib.Path(args.output)
    out.write_text('schema: sdk-observer-capture-v1\nstatus: CAPTURED_DIAGNOSTIC_DATA\n'
                   f'kind: {args.kind}\nraw_sha256: {hashlib.sha256(raw).hexdigest()}\n'
                   f'records: {len(blocks)}\nprocesses: {len(groups)}\n'
                   'resolver_fix_proved: false\nsdk_qualification: none\nrecords_observed:\n' +
                   ''.join(f'  - process: {pid}\n    sequence: {seq}\n    branch: {branch}\n'
                           for pid, seq, branch in rows))


parser = argparse.ArgumentParser()
sub = parser.add_subparsers(dest='mode', required=True)
p = sub.add_parser('bind')
for name in ('root', 'source', 'sha256', 'bytes', 'seed-sha256', 'control-root'):
    p.add_argument('--' + name, required=True)
p = sub.add_parser('records')
for name in ('log', 'output'):
    p.add_argument('--' + name, required=True)
p.add_argument('--kind', choices=('control', 'sdk'), required=True)
p.add_argument('--data-root')
args = parser.parse_args()
if args.mode == 'bind':
    bind(args)
else:
    records(args)
