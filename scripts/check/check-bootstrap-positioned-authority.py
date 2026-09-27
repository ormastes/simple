#!/usr/bin/env python3
"""Focused checks of the exact embedded production reader and real map ingress."""
import hashlib
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


if __name__ == '__main__':
    unittest.main()
