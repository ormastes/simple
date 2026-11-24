"""Verify existing ce231 Phase3 evidence; never launch or admit a producer."""
import hashlib
import json
from pathlib import Path

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
CONTROL = 'd18104ea541e35a2fdcbe3561461605c0e6d38ac'
RUNTIME_ID = 14871469985
RUNTIME_ZIP_SHA = '5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9'

def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def read(path):
    return json.loads(path.read_text())

def receipt(path):
    fields = {}
    for line in path.read_text().splitlines():
        key, value = line.split('=', 1)
        assert key not in fields, 'duplicate receipt field'
        fields[key] = value
    for key, value in dict(status='complete', exit_status='0', quiescent='1', rss_cap_enforced='1').items():
        assert fields.get(key) == value, (path, key, fields)
    assert int(fields['rss_limit_kib']) > 0
    return fields

def verify(parent, evidence, runtime, expected_sha, artifact_id):
    """Intake directory contains verified ZIP extraction plus original GitHub metadata."""
    from zipfile import ZipFile
    root = Path(evidence)
    run = read(root/'run.json')
    artifact = read(root/'artifact.json')
    assert run['head_sha'] == CONTROL and run['status'] == 'completed'
    assert run['conclusion'] == 'success', 'upstream qualification must succeed'
    assert artifact['id'] == artifact_id and artifact['workflow_run']['id'] == run['id']
    assert artifact['name'] == 'ce231-child-phase3-'+str(run['id'])
    assert not artifact['expired']
    assert artifact['digest'] == 'sha256:'+sha(root/'artifact.zip')
    # Verify retained evidence directly against the original archive, without trusting extraction.
    extracted = root/'extracted'
    with ZipFile(root/'artifact.zip') as archive:
        members = {}
        for info in archive.infolist():
            if info.is_dir():
                continue
            name = info.filename
            parts = Path(name).parts
            assert not name.startswith('/') and '\\' not in name and ':' not in name and '..' not in parts
            assert name.casefold() not in members
            members[name.casefold()] = name
        def bound(path):
            name = path.relative_to(extracted).as_posix()
            assert members[name.casefold()] == name
            assert sha(path) == hashlib.sha256(archive.read(name)).hexdigest()
        contract_path = extracted/'ce231-contract.json'
        phase = extracted/'ce231-phase3'
        qualification = phase/'qualification'
        required = [contract_path, phase/'terminal.json', phase/'owner.env',
                    qualification/'qualification.json', qualification/'native-hello-build.owner.env',
                    qualification/'native-hello-run.owner.env', qualification/'native-hello-run.stdout',
                    qualification/'native-hello-build.argv.json', qualification/'native-hello-run.argv.json',
                    qualification/'hello', extracted/'source/build/bootstrap/stage3/simple']
        for path in required:
            bound(path)
        contract, terminal, behavior = map(read, [contract_path, phase/'terminal.json', qualification/'qualification.json'])
        assert contract['source_revision'] == SOURCE
        assert contract['runtime_artifact_id'] == RUNTIME_ID
        assert contract['runtime_artifact_zip_sha256'] == RUNTIME_ZIP_SHA
        assert terminal['source'] == SOURCE and terminal['status'] == 'BUILT_UNQUALIFIED'
        assert terminal['inputs_unchanged'] is True
        assert terminal['producer_sha256'] == contract['phase2_producer_sha256']
        assert terminal['runtime_files'] == contract['runtime_files']
        assert terminal['product_sha256'] == expected_sha == sha(parent)
        assert sha(required[-1]) == expected_sha
        build_argv = read(qualification/'native-hello-build.argv.json')
        build_child = build_argv[build_argv.index('--')+1:]
        assert build_child[:2] == [contract['source_root']+'/build/bootstrap/stage3/simple', 'native-build']
        assert build_child[build_child.index('--runtime-path')+1] == contract['runtime_root']
        assert build_child[build_child.index('--backend')+1] == 'llvm'
        run_argv = read(qualification/'native-hello-run.argv.json')
        run_child = run_argv[run_argv.index('--')+1:]
        assert len(run_child) == 1 and run_child[0] == build_child[build_child.index('--output')+1]
        assert behavior['role'] == 'phase3' and behavior['status'] == 'BEHAVIOR_PASS'
        assert behavior['source'] == SOURCE and behavior['product_sha256'] == expected_sha
        assert behavior['claims']['native_hello'] is True
        assert sha(qualification/'hello') == behavior['claims']['native_hello_sha256']
        assert (qualification/'native-hello-run.stdout').read_bytes() == b'early-full-cli-ok\n42\n'
        build_owner = receipt(phase/'owner.env')
        assert int(build_owner['rss_limit_kib']) == contract['phase3_memory_kib']
        for name, cap in [('native-hello-build', 4194304), ('native-hello-run', 262144)]:
            assert int(receipt(qualification/(name+'.owner.env'))['rss_limit_kib']) == cap
        assert behavior['runtime_files'] == contract['runtime_files']
        for name, digest in contract['runtime_files'].items():
            assert not Path(name).is_absolute() and '..' not in Path(name).parts
            assert sha(Path(runtime)/name) == digest
        assert {'libsimple_native_all.a','libsimple_compiler_backfill.a'} <= set(contract['runtime_files'])
    return {'source': SOURCE, 'parent_run': run['id'], 'parent_artifact': artifact_id,
            'parent_sha256': expected_sha, 'runtime_files': contract['runtime_files'],
            'parent_hello_sha256': behavior['claims']['native_hello_sha256'],
            'scope': 'verified native behavior; no managed stage admission'}
