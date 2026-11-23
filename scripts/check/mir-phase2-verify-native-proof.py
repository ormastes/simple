"""Verify archived pre-link success while preserving its collector FAILURE."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct

PARENT = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
FIXTURE = '68bb1b5d22340f9f730d37e584033793a821f0ce'
OBJECT = '79f19dc06de194085eb0c5ad2cda594f8e8d36654d2364cb18fee0ab9ca26248'

def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def fields(path, separator):
    out = {}
    for line in path.read_text().splitlines():
        if separator in line and not line.startswith((' ', '#')):
            key, value = line.split(separator, 1)
            assert key not in out, 'duplicate receipt field: '+key
            out[key] = value.strip()
    return out

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('intake/regression'))
    parser.add_argument('--job', type=Path, default=Path('intake/regression-job.json'))
    parser.add_argument('--output', type=Path, default=Path('intake/native-proof.json'))
    args = parser.parse_args()
    root = args.root
    lane = root/'actual_attribute_store'
    job = json.loads(args.job.read_text())
    assert job['id'] == 137990648590 and job['run_id'] == 45259641764
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    failure = 'Retain actual selected-provider module and source records'
    failed = [step['name'] for step in job['steps'] if step['conclusion'] == 'failure']
    assert failed == [failure]
    index = next(i for i,step in enumerate(job['steps']) if step['name'] == failure)
    assert all(step['conclusion'] == 'success' for step in job['steps'][:index])
    producer = fields(root/'producer.sdn', ':')
    for key, value in {'producer_run':'45254614898', 'producer_artifact':'14858799081',
                       'producer_source':SOURCE, 'producer_sha256':PARENT,
                       'producer_bytes':'57470728', 'fixture_checkout':FIXTURE,
                       'expected_fixture_checkout':FIXTURE, 'identity_verified':'true',
                       'fixture_checkout_verified':'true', 'producer_phase':'1'}.items():
        assert producer[key] == value, key
    owner = fields(lane/'owner.env', '=')
    for key,value in {'status':'complete','exit_status':'0','quiescent':'1',
                      'rss_cap_enforced':'1','rss_limit_kib':'6291456'}.items():
        assert owner[key] == value, key
    assert (lane/'native-build.exit').read_text().strip() == '0'
    receipt = fields(lane/'receipt.sdn', ':')
    assert receipt['producer_sha256'] == PARENT and receipt['native_build_exit_status'] == '0'
    assert receipt['outcome'] == 'PROVIDER_METADATA_INCOMPLETE'
    assert (lane/'metadata.status').read_text().strip() == 'INCOMPLETE'
    providers = fields(lane/'selected-providers.sdn', ':')
    assert providers['selected_source_count'] == '14'
    assert providers['native_object_provider_records'] == '0'
    manifest = lane/'production-projection.sha256'
    assert sha(manifest) == 'adad0c438a863cf1f734ef2e132ead5f6d8f4c0c2e1725ed9e405beb2f02032e'
    rows = manifest.read_text().splitlines()
    assert len(rows) == 13
    for row in rows:
        digest, path = row.split(None, 1)
        assert path.startswith('src/') and '..' not in Path(path).parts
        assert sha(lane/'projection'/path) == digest
    assert sha(lane/'projection/src/app/actual_attribute_store.spl') == 'd8cc197e7d64801f54094263f07fb777b34b56fad6d4ddad6f89d4bbe1b1cdfe'
    program = lane/'program'
    assert program.stat().st_size == 405248 and sha(program) == OBJECT
    header = program.read_bytes()[:20]
    assert header[:6] == b'\x7fELF\x02\x01' and struct.unpack_from('<HH', header,16) == (1,62)
    log = (lane/'native-build.log').read_text()
    for phase in ['mir','native_compile']:
        assert re.search(r'phase='+phase+r' .*done=14 total=14 remaining=0 succeeded=14 cached=0 failed=0', log), phase
    assert 'enum match retained Result/Optional has no complete declaration ownership' not in log
    command = (lane/'command.txt').read_text()
    assert '--emit-object --backend llvm --target x86_64-unknown-linux-gnu' in command
    hir = lane/'hir-cache/2369087cbd5709d5ac97c025a5cbe09c6956fa388752ce315bd8d5f931860374.parser-v4.hir'
    lines = hir.read_text().splitlines()
    assert 'frontend-exe='+PARENT in lines[0]
    assert lines[7].endswith('/src/compiler/00.common/data/attribute_schema_v1.spl')
    at = lines.index('compiler.common.data.attribute_schema_v1.AttributeStoreV1::get')
    # Versioned codec: kind present/kind, type present, HirType present/kind present/Function.
    assert lines[at+1:at+7] == ['1','1','1','1','1','18']
    result = {'native_object_criterion':'PASS', 'overall_workflow':'FAILURE',
              'collector_outcome':'PROVIDER_METADATA_INCOMPLETE', 'admission':'none',
              'runtime_pairing':'unverified pre-link only', 'source':SOURCE,
              'fixture_source':FIXTURE, 'producer_sha256':PARENT, 'object_sha256':OBJECT,
              'mir_succeeded':14,'native_succeeded':14, 'provider_hir_sha256':sha(hir),
              'provider_signature':'actual owned getter now has a Function type',
              'owner':owner}
    args.output.write_text(json.dumps(result,indent=2))
    print('Archived native object criterion PASS; workflow FAILURE/metadata INCOMPLETE preserved')

if __name__ == '__main__':
    main()
