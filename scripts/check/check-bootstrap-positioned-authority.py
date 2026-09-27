#!/usr/bin/env python3
"""Focused checks of the exact embedded production reader and real map ingress."""
import hashlib
import contextlib
import io
import re
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
VERIFIER = ROOT / 'scripts/check/lib/bootstrap-stage3/manifest-verify.shs'
SOURCE = VERIFIER.read_text().split("<<'BOOTSTRAP_POSITIONED_READ_PY'\n", 1)[1].split('\nBOOTSTRAP_POSITIONED_READ_PY\n', 1)[0]
NAMESPACE = {'__name__': 'production_reader'}
exec(compile(SOURCE, str(VERIFIER), 'exec'), NAMESPACE)
READ = NAMESPACE['positioned_read']
VERIFY_ROLE = NAMESPACE['verify_role']


class PositionedAuthority(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='positioned-authority-')
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name).resolve() / 'map.env'
        self.data = b'schema=authority\nstatus=ready\n'
        self.path.write_bytes(self.data)
        self.fd = os.open(self.path, os.O_RDONLY)
        self.addCleanup(os.close, self.fd)
        self.receipt = READ(self.fd, source_path=self.path)[1]

    def test_repeated_reads_preserve_shared_offset(self):
        os.lseek(self.fd, 7, os.SEEK_SET)
        for _ in range(3):
            self.assertEqual(READ(self.fd, self.receipt)[0], self.data)
            self.assertEqual(os.lseek(self.fd, 0, os.SEEK_CUR), 7)

    def test_unlink_and_replacement_do_not_redirect_authority(self):
        self.path.unlink()
        self.path.write_bytes(b'replacement\n')
        self.assertEqual(READ(self.fd, self.receipt)[0], self.data)
        with self.assertRaises(ValueError):
            READ(self.fd, source_path=self.path)

    def test_symlink_cannot_supply_source_binding(self):
        link = self.path.with_name('link')
        link.symlink_to(self.path)
        with self.assertRaises(ValueError):
            READ(self.fd, source_path=link)

    def test_other_descriptor_with_identical_bytes_is_rejected(self):
        other = self.path.with_name('other')
        other.write_bytes(self.data)
        fd = os.open(other, os.O_RDONLY)
        try:
            with self.assertRaises(ValueError):
                READ(fd, self.receipt)
        finally:
            os.close(fd)

    def test_mutated_content_is_rejected(self):
        self.path.write_bytes(b'x' * len(self.data))
        with self.assertRaises(ValueError):
            READ(self.fd, self.receipt)

    def test_mutation_during_read_is_rejected(self):
        pread = os.pread
        def mutate(fd, length, offset):
            value = pread(fd, length, offset)
            self.path.write_bytes(self.data + b'changed\n')
            return value
        with patch.object(os, 'pread', mutate), self.assertRaises(ValueError):
            READ(self.fd, self.receipt)

    def test_closed_and_directory_descriptors_are_rejected(self):
        closed = os.dup(self.fd)
        os.close(closed)
        with self.assertRaises(OSError):
            READ(closed, self.receipt)
        directory = os.open(self.path.parent, os.O_RDONLY)
        try:
            with self.assertRaises(ValueError):
                READ(directory)
        finally:
            os.close(directory)

    def test_shell_reader_is_offset_independent_and_checks_keys(self):
        script = '''
. "$1"
exec 9<"$2"
receipt=$(bootstrap_stage3_descriptor_read 9 '' seal "$2") || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" value schema || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" value status || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" hash '' || exit 1
if bootstrap_stage3_descriptor_read 9 "$receipt" value missing; then exit 1; fi
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(VERIFIER), str(self.path)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['authority', 'ready', hashlib.sha256(self.data).hexdigest()])

    def test_embedded_reader_is_bound_by_helper_fingerprint(self):
        library = self.path.parent / 'lib'
        library.mkdir()
        shutil.copy(ROOT / 'scripts/check/lib/bootstrap-stage3-provenance.shs', library)
        shutil.copytree(ROOT / 'scripts/check/lib/bootstrap-stage3', library / 'bootstrap-stage3')
        script = '\n'.join([
            'BOOTSTRAP_STAGE3_FACADE_PATH="$1/bootstrap-stage3-provenance.shs"',
            '. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 1',
            'bootstrap_stage3_helper_bundle_fingerprint'])
        def fingerprint():
            return subprocess.check_output(['sh', '-c', script, 'test', str(library)], text=True).strip()
        before = fingerprint()
        helper = library / 'bootstrap-stage3/manifest-verify.shs'
        helper.write_text(helper.read_text().replace('before.st_size > 1048576', 'before.st_size > 2097152', 1))
        self.assertNotEqual(before, fingerprint())

    def test_selected_python_must_match_recorded_authority(self):
        interpreter = str(Path(sys.executable).resolve())
        digest = hashlib.sha256(Path(interpreter).read_bytes()).hexdigest()
        row = f'tool=python3|canonical={interpreter}|sha256={digest}\n'
        script = '''
. "$1/scripts/check/lib/bootstrap-stage3/authority.shs"
. "$1/scripts/check/lib/bootstrap-stage3/manifest-verify.shs"
bootstrap_stage3_portable_python=$3
bootstrap_stage3_portable_python_sha=$4
bootstrap_stage3_verify_portable_python "$2"
'''
        for content, accepted in [
            (row, True), ('', False), (row + row, False),
            (row.replace(digest, '0' * 64), False),
            (row.replace(interpreter, '/wrong/python3'), False),
        ]:
            with self.subTest(content=content):
                self.path.write_text(content)
                result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.path), interpreter, digest], capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, accepted, result.stderr)

    def test_duplicate_keys_and_vector_digest(self):
        self.path.write_bytes(b'schema=a\nstatus=ready\nentry_count=1\nmap_vector_sha256=unused\nseed_authority=file\nseed_dev=1\n')
        script = '''
. "$1"
exec 9<"$2"
receipt=$(bootstrap_stage3_descriptor_read 9 '' seal "$2") || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" roles '' || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" lines '' || exit 1
bootstrap_stage3_descriptor_read 9 "$receipt" vector '' || exit 1
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(VERIFIER), str(self.path)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['seed', '6', hashlib.sha256(b'seed_authority=file\nseed_dev=1\n').hexdigest()])
        self.path.write_bytes(b'schema=a\nschema=b\n')
        script = script.split('bootstrap_stage3_descriptor_read 9 "$receipt" roles')[0]
        script += 'bootstrap_stage3_descriptor_read 9 "$receipt" value schema\n'
        result = subprocess.run(['sh', '-c', script, 'test', str(VERIFIER), str(self.path)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, '')

    @unittest.skipIf(Path('/proc/self/stat').is_file(), 'non-procfs production ingress')
    def test_real_verifier_checks_map_content_on_non_procfs_host(self):
        self.path.write_bytes(b'schema=simple-stage3-bound-artifact-authority-map-v2\nstatus=forged\n')
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT="$1"
unset BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_verify_manifest "$2/manifest" "$2/manifest" "$1" "$2/compiler" "$2/compiler" "$2/map.env"
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.path.parent)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('manifest-stage-map-status', result.stderr)
        self.assertNotIn('manifest-entry-bound-map-hash', result.stderr)


class ManifestAndRoleAuthority(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='manifest-role-authority-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.path = self.root / 'artifact'
        self.data = b'authority bytes\n'
        self.path.write_bytes(self.data)

    def binding(self, path, kind='file'):
        info = path.stat()
        digest = hashlib.sha256(path.read_bytes()).hexdigest() if kind == 'file' else '-'
        return f'{kind}:{info.st_dev}:{info.st_ino}:{info.st_mode & 0o7777:o}:{digest}'

    def test_role_mode_matches_darwin_octal_receipts(self):
        self.path.chmod(0o751)
        binding = self.binding(self.path)
        VERIFY_ROLE(self.path, binding)
        if sys.platform == 'darwin':
            mode = subprocess.check_output(['stat', '-f', '%Lp', str(self.path)], text=True).strip()
            self.assertEqual(binding.split(':')[3], mode)
        with self.assertRaises(ValueError):
            VERIFY_ROLE(self.path, binding.replace(':751:', ':750:'))
        VERIFY_ROLE(self.root, self.binding(self.root, 'directory'))

    def test_role_identity_digest_and_type_rejections(self):
        binding = self.binding(self.path)
        other = self.root / 'other'
        other.write_bytes(self.data)
        with self.assertRaises(ValueError):
            VERIFY_ROLE(other, binding)
        with self.assertRaises(ValueError):
            VERIFY_ROLE(self.path, binding.rsplit(':', 1)[0] + ':' + '0' * 64)
        link = self.root / 'link'
        link.symlink_to(self.path)
        with self.assertRaises(ValueError):
            VERIFY_ROLE(link, binding)
        with self.assertRaises(ValueError):
            VERIFY_ROLE(self.path, self.binding(self.root, 'directory'))

    def test_role_mutation_during_hash_is_rejected(self):
        binding = self.binding(self.path)
        pread = os.pread
        def mutate(fd, count, offset):
            result = pread(fd, count, offset)
            self.path.write_bytes(b'x' * len(self.data))
            return result
        with patch.object(os, 'pread', mutate), self.assertRaises(ValueError):
            VERIFY_ROLE(self.path, binding)

    def test_role_replacement_during_hash_is_rejected(self):
        binding = self.binding(self.path)
        pread = os.pread
        def replace(fd, count, offset):
            result = pread(fd, count, offset)
            self.path.unlink()
            self.path.write_bytes(self.data)
            return result
        with patch.object(os, 'pread', replace), self.assertRaises(ValueError):
            VERIFY_ROLE(self.path, binding)

    def test_nonportable_dispatch_preserves_existing_lookup(self):
        self.path.write_bytes(b'schema=existing-path-reader\n')
        script = '''
. "$1/scripts/check/lib/bootstrap-stage3/command-snapshot.shs"
. "$1/scripts/check/lib/bootstrap-stage3/manifest-verify.shs"
bootstrap_stage3_manifest=$2
bootstrap_stage3_portable_manifest=0
bootstrap_stage3_verify_value schema "$2" || exit 1
printf 'schema=duplicate\n' >>"$2"
if bootstrap_stage3_verify_value schema "$2"; then exit 1; fi
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.path)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, 'existing-path-reader\n')

    def test_manifest_dispatch_retains_inode_and_rejects_later_mutation(self):
        self.path.write_bytes(b'schema=original\nstatus=verified\n')
        script = '''
. "$1"
bootstrap_stage3_manifest_value() { echo unexpected-path-fallback >&2; return 97; }
bootstrap_stage3_manifest=$2
exec 8<"$2"
bootstrap_stage3_manifest_receipt=$(bootstrap_stage3_descriptor_read 8 '' seal "$2") || exit 1
bootstrap_stage3_portable_manifest=1
ln "$2" "$2.retained" || exit 1
rm "$2"
printf 'schema=replacement\n' >"$2"
bootstrap_stage3_verify_value schema "$2" || exit 1
bootstrap_stage3_verify_value status "$2" || exit 1
printf 'mutated\n' >"$2.retained"
if bootstrap_stage3_verify_value schema "$2"; then exit 1; fi
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(VERIFIER), str(self.path)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['original', 'verified'])
        self.assertNotIn('unexpected-path-fallback', result.stderr)

    @unittest.skipIf(Path('/proc/self/stat').is_file(), 'non-procfs production ingress')
    def test_real_verifier_passes_roles_and_seals_manifest(self):
        self.path.chmod(0o755)
        manifest = self.root / 'manifest.env'
        manifest.write_bytes(b'schema=simple-bootstrap-stage3-provenance-v4\n')
        interpreter = Path(sys.executable).resolve()
        tools = self.root / 'tools.env'
        tools.write_text(f'tool=python3|canonical={interpreter}|sha256={hashlib.sha256(interpreter.read_bytes()).hexdigest()}\n')
        map_path = self.root / 'map.env'
        map_path.touch()
        roles = (
            'seed native_all compiler_backfill stage2 stage2_admitted stage2_build_log '
            'stage2_command_transcript stage2_sanity_evidence stage2_sanity_companion_parent '
            'stage2_receiver_evidence stage2_receiver_log stage2_admission_receipt '
            'stage3_build_log stage3_command_transcript stage3_sanity_evidence '
            'stage3_sanity_companion_parent git_state runtime_origin_snapshot '
            'runtime_admitted_snapshot tool_authority seed_inputs_stamp source_snapshot '
            'output bootstrap_script provenance_helper stage2_native_cache_dir '
            'stage3_native_cache_dir runtime_path source_inputs_before tool_authority_before jobs_receipt'
        ).split()
        directories = {'stage2_sanity_companion_parent', 'stage3_sanity_companion_parent',
                       'stage2_native_cache_dir', 'stage3_native_cache_dir', 'runtime_path'}
        rows = []
        for role in roles:
            path = self.root if role in directories else tools if role == 'tool_authority' else self.path
            if role == 'compiler_backfill':
                rows.extend([f'{role}_authority=descriptor-absent', f'{role}_display={path}',
                             f'{role}_dev=absent', f'{role}_ino=absent', f'{role}_mode=absent'])
                continue
            st = path.stat()
            rows.extend([f'{role}_authority={path}', f'{role}_display={path}',
                         f'{role}_dev={st.st_dev}', f'{role}_ino={st.st_ino}',
                         f'{role}_mode={st.st_mode & 0o7777:o}'])
            if role not in directories:
                rows.append(f'{role}_sha256={hashlib.sha256(path.read_bytes()).hexdigest()}')
        vector = '\n'.join(rows) + '\n'
        map_path.write_text('schema=simple-stage3-bound-artifact-authority-map-v2\nstatus=ready\nentry_count=31\n'
                            + f'map_vector_sha256={hashlib.sha256(vector.encode()).hexdigest()}\n' + vector)
        self.assertEqual(len(map_path.read_text().splitlines()), 184)
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$1
unset BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_verify_manifest "$2/manifest.env" "$2/manifest.env" "$1" "$2/artifact" "$2/artifact" "$2/map.env"
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.root)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('manifest-status-not-singular', result.stderr)
        self.assertNotIn('stat:', result.stderr)


class ProducerAuthority(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='producer-authority-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.artifact = self.root / 'artifact'
        self.artifact.write_bytes(b'producer authority bytes\n')
        self.artifact.chmod(0o754)
        self.directory = self.root / 'directory'
        self.directory.mkdir(mode=0o750)
        self.map_path = self.root / 'manifest.env.authority-map.env'

    def produce(self, backfill='absent', missing=None, overrides=None):
        writer = (ROOT / 'scripts/check/lib/bootstrap-stage3/manifest-write.shs').read_text()
        rows = writer.split('bootstrap_stage3_write_authority_map_rows() {', 1)[1].split('\n}', 1)[0]
        variables = set(re.findall(r'\$(BSTAGE3_[A-Z0-9_]+)', rows))
        environment = os.environ.copy()
        for name in variables:
            path = self.directory if ('COMPANION_PARENT' in name or 'CACHE_DIR' in name or name.startswith('BSTAGE3_RUNTIME_PATH')) else self.artifact
            environment[name] = str(path)
        environment['BSTAGE3_MANIFEST'] = str(self.root / 'manifest.env')
        environment['bootstrap_stage3_backfill_status'] = backfill
        environment.update(overrides or {})
        if missing:
            environment[missing] = str(self.root / 'missing')
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$1
unset BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_manifest_descriptor_mode=0
if [ ! -r /proc/self/stat ]; then bootstrap_stage3_prepare_portable_python || exit 3; fi
bootstrap_stage3_write_authority_map
'''
        return subprocess.run(['sh', '-c', script, 'test', str(ROOT)], env=environment, capture_output=True, text=True)

    def assert_map(self, expected_lines):
        raw = self.map_path.read_bytes()
        lines = raw.decode().splitlines()
        values = dict(line.split('=', 1) for line in lines)
        self.assertEqual(len(lines), expected_lines)
        self.assertEqual(len(values), expected_lines)
        self.assertEqual(values['schema'], 'simple-stage3-bound-artifact-authority-map-v2')
        self.assertEqual(values['status'], 'ready')
        self.assertEqual(values['entry_count'], '31')
        self.assertEqual(values['map_vector_sha256'], hashlib.sha256(b'\n'.join(raw.split(b'\n')[4:])).hexdigest())
        self.assertEqual(self.map_path.stat().st_mode & 0o7777, 0o400)
        roles = [key[:-10] for key in values if key.endswith('_authority')]
        self.assertEqual(len(roles), 31)
        for role in roles:
            authority = values[role + '_authority']
            if authority == 'descriptor-absent':
                self.assertEqual(role, 'compiler_backfill')
                self.assertNotIn(role + '_sha256', values)
                continue
            path = Path(authority)
            st = path.stat()
            self.assertEqual(values[role + '_dev'], str(st.st_dev))
            self.assertEqual(values[role + '_ino'], str(st.st_ino))
            self.assertEqual(values[role + '_mode'], format(st.st_mode & 0o7777, 'o'))
            kind = 'directory' if path.is_dir() else 'file'
            digest = '-' if kind == 'directory' else hashlib.sha256(path.read_bytes()).hexdigest()
            if kind == 'file':
                self.assertEqual(values[role + '_sha256'], digest)
            else:
                self.assertNotIn(role + '_sha256', values)
            VERIFY_ROLE(path, ':'.join([kind, values[role + '_dev'], values[role + '_ino'], values[role + '_mode'], digest]))
        self.assertFalse(list(self.root.glob('*.tmp.*')))

    def test_producer_emits_absent_backfill_receipt(self):
        result = self.produce()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_map(184)

    def test_producer_emits_present_backfill_receipt(self):
        result = self.produce(backfill='present')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_map(185)

    def test_failed_first_middle_last_rows_never_publish(self):
        for variable in ['BSTAGE3_SEED', 'BSTAGE3_STAGE2_LOG', 'BSTAGE3_JOBS_RECEIPT']:
            with self.subTest(variable=variable):
                result = self.produce(missing=variable)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(self.map_path.exists())
                self.assertFalse(list(self.root.glob('*.tmp.*')))

    def test_producer_rejects_leaf_symlink(self):
        link = self.root / 'link'
        self.artifact.rename(link)
        self.artifact.symlink_to(link)
        result = self.produce()
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.map_path.exists())

    @unittest.skipIf(Path('/proc/self/stat').is_file(), 'non-procfs production runtime path')
    def test_real_verifier_passes_runtime_boundary_and_rejects_wrong_bindings(self):
        cache2, cache3 = self.root / 'cache2', self.root / 'cache3'
        cache2.mkdir()
        cache3.mkdir()
        interpreter = Path(sys.executable).resolve()
        tools = self.root / 'tools.env'
        tools.write_text(f'tool=python3|canonical={interpreter}|sha256={hashlib.sha256(interpreter.read_bytes()).hexdigest()}\n')
        overrides = {'BSTAGE3_TOOL_AUTHORITY': str(tools), 'BSTAGE3_TOOL_AUTHORITY_DISPLAY': str(tools)}
        for variable, path in [('BSTAGE3_STAGE2_CACHE_DIR', cache2), ('BSTAGE3_STAGE3_CACHE_DIR', cache3)]:
            overrides[variable] = str(path)
            overrides[variable + '_DISPLAY'] = str(path)
        produced = self.produce(overrides=overrides)
        self.assertEqual(produced.returncode, 0, produced.stderr)
        metadata_script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_host_platform
bootstrap_stage3_helper_bundle_fingerprint
'''
        platform, bundle = subprocess.check_output(['sh', '-c', metadata_script, 'test', str(ROOT)], text=True).splitlines()
        source = VERIFIER.read_text()
        required = source.split('for bootstrap_stage3_key in ', 1)[1].split('; do', 1)[0].replace('\\', '').split()
        values = {key: 'fixture' for key in required}
        for key in values:
            if key.endswith(('sha256', 'fingerprint')) or key == 'stage2_admission_identity':
                values[key] = '0' * 64
        values.update({
            'schema': 'simple-bootstrap-stage3-provenance-v4', 'status': 'pass',
            'artifact_kind': 'pure-simple-bootstrap-compiler', 'full_cli_status': 'separate-not-proven',
            'native_build_backfill_status': 'bound-bootstrap-native-all', 'source_roots': 'src/compiler:src/app:src/lib',
            'stage2_sanity_status': 'pass', 'stage2_receiver_status': 'pass', 'stage3_sanity_status': 'pass',
            'stage2_check_policy': 'identity-scoped-receipt-reuse', 'stage2_checks_executed_at_admission': '1',
            'stage2_checks_replayed_during_stage3': '0',
            'bootstrap_script_path': str(ROOT / 'scripts/bootstrap/bootstrap-from-scratch.sh'),
            'provenance_helper_path': str(ROOT / 'scripts/check/lib/bootstrap-stage3-provenance.shs'),
            'provenance_helper_bundle_fingerprint': bundle,
            'source_snapshot_path': str(self.root / 'source-inputs-after.txt'),
            'bound_artifact_authority_map_path': str(self.map_path),
            'bound_artifact_authority_map_sha256': hashlib.sha256(self.map_path.read_bytes()).hexdigest(),
            'platform': platform, 'backend': 'cranelift', 'mode': 'dynload', 'stage2_threads': '1', 'stage3_threads': '1',
            'stage2_native_cache_dir': str(cache2), 'stage3_native_cache_dir': str(cache3),
            'runtime_path': str(self.directory), 'stage2_path': str(self.artifact), 'stage3_path': str(self.artifact),
            'stage2_command_output': str(self.artifact), 'stage3_command_output': str(self.artifact),
        })
        manifest = self.root / 'manifest.env'
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$1
BOOTSTRAP_STAGE3_PHASE_STATUS_FD=159
exec 159>"$2/phases"
unset BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_verify_manifest "$2/manifest.env" "$2/manifest.env" "$1" "$2/artifact" "$2/artifact" "$2/manifest.env.authority-map.env"
'''
        def probe():
            manifest.write_text(''.join(f'{key}={value}\n' for key, value in values.items()))
            return subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.root)], capture_output=True, text=True)
        result = probe()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('stage2-path-outside-canonical-lane', result.stderr)
        self.assertIn('aV6', (self.root / 'phases').read_text())
        self.assertNotIn('stat:', result.stderr)
        values['runtime_path'] = str(cache2)
        rejected = probe()
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn('aV5', (self.root / 'phases').read_text())
        self.assertNotIn('stage2-path-outside-canonical-lane', rejected.stderr)
        values['runtime_path'] = str(self.directory)
        self.directory.rename(self.root / 'old-directory')
        self.directory.mkdir()
        replaced = probe()
        self.assertNotEqual(replaced.returncode, 0)
        self.assertIn('portable-authority-role-', replaced.stderr)
        self.assertNotIn('stage2-path-outside-canonical-lane', replaced.stderr)

    def test_snapshot_mutation_emits_no_receipt(self):
        pread = os.pread
        def mutate(fd, count, offset):
            result = pread(fd, count, offset)
            self.artifact.write_bytes(b'changed size')
            return result
        output = io.StringIO()
        with contextlib.redirect_stdout(output), patch.object(os, 'pread', mutate):
            with self.assertRaises(ValueError):
                NAMESPACE['main'](['0', 'file', 'role-receipt', str(self.artifact)])
        self.assertEqual(output.getvalue(), '')


class RetainedRuntimeSnapshot(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='runtime-fd-authority-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.runtime = self.root / 'runtime'
        self.runtime.mkdir()
        (self.runtime / 'nested').mkdir()
        (self.runtime / 'plain file').write_bytes(b'plain\n')
        executable = self.runtime / 'nested' / 'execute'
        executable.write_bytes(b'executable\n')
        executable.chmod(0o755)
        (self.runtime / 'line\nname').write_bytes(b'newline filename\n')
        self.fd = os.open(self.runtime, os.O_RDONLY | os.O_DIRECTORY)
        self.addCleanup(os.close, self.fd)
        st = os.fstat(self.fd)
        self.binding = f'directory:{st.st_dev}:{st.st_ino}:{st.st_mode & 0o7777:o}:-'

    def snapshot(self):
        return NAMESPACE['directory_snapshot'](self.fd, self.binding, str(self.runtime))

    def test_snapshot_matches_existing_format_and_preserves_offset(self):
        reference = self.root / 'reference'
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_directory_snapshot "$2" "$3"
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(reference), str(self.runtime)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        offset = os.lseek(self.fd, 0, os.SEEK_CUR)
        for _ in range(2):
            self.assertEqual(self.snapshot(), reference.read_bytes())
            self.assertEqual(os.lseek(self.fd, 0, os.SEEK_CUR), offset)

    def test_identical_root_replacement_is_rejected(self):
        old = self.root / 'old-runtime'
        self.runtime.rename(old)
        shutil.copytree(old, self.runtime)
        with self.assertRaises(ValueError):
            self.snapshot()

    def test_replacement_during_snapshot_is_rejected(self):
        pread = os.pread
        changed = False
        def replace(fd, count, offset):
            nonlocal changed
            data = pread(fd, count, offset)
            if not changed:
                changed = True
                old = self.root / 'old-runtime'
                self.runtime.rename(old)
                shutil.copytree(old, self.runtime)
            return data
        with patch.object(os, 'pread', replace), self.assertRaises(ValueError):
            self.snapshot()

    def test_descendant_mutation_and_symlink_are_rejected(self):
        pread = os.pread
        def mutate(fd, count, offset):
            data = pread(fd, count, offset)
            held = os.fstat(fd)
            for candidate in self.runtime.rglob('*'):
                current = candidate.stat()
                if (current.st_dev, current.st_ino) == (held.st_dev, held.st_ino):
                    candidate.write_bytes(b'changed size during snapshot')
                    break
            return data
        with patch.object(os, 'pread', mutate), self.assertRaises(ValueError):
            self.snapshot()
        (self.runtime / 'alias').symlink_to(self.runtime / 'plain file')
        with self.assertRaises(ValueError):
            self.snapshot()

    def test_shell_snapshot_publishes_exclusively_and_rejects_replaced_root(self):
        output = self.root / 'snapshot'
        script = '''
. "$1"
exec 6<"$2/."
bootstrap_stage3_descriptor_read 6 "$3" directory-check "$2" || exit 1
bootstrap_stage3_descriptor_read 6 "$3" directory-snapshot "$2" "$4" || exit 1
if bootstrap_stage3_descriptor_read 6 "$3" directory-snapshot "$2" "$4"; then exit 1; fi
mv "$2" "$2.old"
mkdir "$2"
if bootstrap_stage3_descriptor_read 6 "$3" directory-snapshot "$2" "$4.rejected"; then exit 1; fi
'''
        expected = self.snapshot()
        result = subprocess.run(['sh', '-c', script, 'test', str(VERIFIER), str(self.runtime), self.binding, str(output)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output.read_bytes(), expected)
        self.assertFalse(Path(str(output) + '.rejected').exists())
        self.assertFalse(list(self.root.glob('.stage3-runtime-*')))


class HostedRuntimeAuthority(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='hosted-fd-authority-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.runtime = self.root / 'runtime'
        self.deps = self.runtime / 'deps'
        self.deps.mkdir(parents=True)
        self.relative = b'deps/libspl_hosted_runtime-fixture.rlib'
        self.library = self.runtime / os.fsdecode(self.relative)
        self.library.write_bytes(b'hosted runtime fixture\n')
        self.digest = hashlib.sha256(self.library.read_bytes()).hexdigest().encode('ascii')
        self.receipt = self.runtime / 'hosted-runtime.env'
        self.receipt_bytes = (b'schema=simple-bootstrap-hosted-runtime-authority-v1\nstatus=frozen\nrelative_path='
                              + self.relative + b'\nsha256=' + self.digest + b'\n')
        self.receipt.write_bytes(self.receipt_bytes)
        self.library.chmod(0o400)
        self.receipt.chmod(0o400)
        self.deps.chmod(0o500)
        self.runtime.chmod(0o500)
        self.addCleanup(self.thaw)
        self.fd = os.open(self.runtime, os.O_RDONLY | os.O_DIRECTORY)
        self.addCleanup(os.close, self.fd)
        st = os.fstat(self.fd)
        self.binding = f'directory:{st.st_dev}:{st.st_ino}:{st.st_mode & 0o7777:o}:-'

    def thaw(self):
        for root, dirs, files in os.walk(self.root):
            Path(root).chmod(0o700)
            for name in files:
                path = Path(root) / name
                if not path.is_symlink():
                    path.chmod(0o600)

    def check(self):
        return NAMESPACE['verify_hosted_runtime'](self.fd, self.binding, str(self.runtime))

    def test_existing_and_retained_helpers_match_without_changing_snapshot(self):
        before = NAMESPACE['directory_snapshot'](self.fd, self.binding, str(self.runtime))
        self.assertEqual(self.check(), (self.relative, self.digest))
        self.assertEqual(NAMESPACE['directory_snapshot'](self.fd, self.binding, str(self.runtime)), before)
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
bootstrap_stage3_verify_hosted_runtime_authority "$2" || exit 1
printf '%s\n%s\n' "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_RELATIVE_PATH" "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_SHA256"
exec 6<"$2/."
bootstrap_stage3_portable_map=1
bootstrap_stage3_runtime_path=$2
bootstrap_stage3_runtime_binding=$3
bootstrap_stage3_verify_admission_runtime_authority "$2" || exit 1
printf '%s\n%s\n' "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_RELATIVE_PATH" "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_SHA256"
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.runtime), self.binding], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.encode(), (self.relative + b'\n' + self.digest + b'\n') * 2)

    def test_later_admission_route_rejects_identical_root_replacement(self):
        script = '''
BOOTSTRAP_STAGE3_FACADE_PATH="$1/scripts/check/lib/bootstrap-stage3-provenance.shs"
. "$BOOTSTRAP_STAGE3_FACADE_PATH" || exit 2
exec 6<"$2/."
mv "$2" "$2.old"
cp -Rp "$2.old" "$2"
# Content-only legacy lookup accepts the identical clone.
bootstrap_stage3_verify_hosted_runtime_authority "$2" || exit 1
bootstrap_stage3_portable_map=1
bootstrap_stage3_runtime_path=$2
bootstrap_stage3_runtime_binding=$3
if bootstrap_stage3_verify_admission_runtime_authority "$2"; then exit 1; fi
[ -z "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_RELATIVE_PATH" ] &&
[ -z "$BOOTSTRAP_STAGE3_HOSTED_RUNTIME_SHA256" ]
'''
        result = subprocess.run(['sh', '-c', script, 'test', str(ROOT), str(self.runtime), self.binding], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('runtime directory identity mismatch', result.stderr)

    def test_receipt_schema_duplicates_path_and_digest_reject(self):
        cases = [self.receipt_bytes + b'status=frozen\n', self.receipt_bytes + b'unknown=value\n',
                 self.receipt_bytes.replace(b'status=frozen', b'status=ready'),
                 self.receipt_bytes.replace(self.relative, b'deps/../outside.rlib'),
                 self.receipt_bytes.replace(self.digest, b'0' * 64)]
        for receipt in cases:
            with self.subTest(receipt=receipt):
                self.receipt.chmod(0o600)
                self.receipt.write_bytes(receipt)
                self.receipt.chmod(0o400)
                with self.assertRaises(ValueError):
                    self.check()

    def test_modes_writability_library_count_and_symlinks_reject(self):
        for path, mode in [(self.receipt, 0o444), (self.library, 0o600), (self.deps, 0o555)]:
            old = path.stat().st_mode & 0o7777
            path.chmod(mode)
            with self.subTest(path=path, mode=mode), self.assertRaises(ValueError):
                self.check()
            path.chmod(old)
        self.deps.chmod(0o700)
        extra = self.deps / 'libspl_hosted_runtime-extra.rlib'
        extra.write_bytes(b'extra')
        extra.chmod(0o400)
        self.deps.chmod(0o500)
        with self.assertRaises(ValueError):
            self.check()
        self.deps.chmod(0o700)
        extra.unlink()
        (self.deps / 'alias').symlink_to(self.library)
        self.deps.chmod(0o500)
        with self.assertRaises(ValueError):
            self.check()

    def test_library_mutation_during_retained_read_rejects(self):
        pread = os.pread
        library_id = self.library.stat().st_ino
        def mutate(fd, count, offset):
            data = pread(fd, count, offset)
            if os.fstat(fd).st_ino == library_id:
                self.library.chmod(0o600)
                self.library.write_bytes(b'changed library size')
                self.library.chmod(0o400)
            return data
        with patch.object(os, 'pread', mutate), self.assertRaises(ValueError):
            self.check()


if __name__ == '__main__':
    unittest.main()
