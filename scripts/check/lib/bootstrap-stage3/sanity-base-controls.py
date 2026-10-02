"""Authenticate archived controls without promoting a failed smoke aggregate.

Bootstrap evidence helper only; never executes a compiler. The canonical shell
writer validates all fresh native criteria before this helper assembles the
composed PASS record. Its consumer repeats the full validation. The archived
aggregate remains FAIL. Profile policy never comes from receipt declarations.
"""
import argparse
import hashlib
import json
import os
import pathlib

PROFILE = 'llvm-32867-qualification1-controls-v1'
CANDIDATE = '32867ba1f9120406373cee55eb243e420e21740576d39c30a0b062a611932e8c'
COLLECTOR = 'cfec29958e4e2b1ad07fed80326a0df9ce07f3cbf0f5aaefcf65fa5fa40b3b27'
ARCHIVE = {
    'sanity.env': 'bc3ff9492fb374d1c3683a5786b69c01d503fa911f77b15bc8641271082e9a6b',
    'qualification.receipt.env': '53399721e79c1932b7190e92641b677bbf3e78c7e40acc01fe63f1b407f9f950',
    'qualification.log': 'd640e3755fce774dac47d87b74456bcf0f4892a99074c5fc049f34406b44dc6e',
    'source-before.txt': '89b5db00f01895406fd21553b322c2ca02ac68c1698f8c3079172566e7ab3b6d',
    'current-consumer-before.env': 'b37ebf003ea77b06322b150b9424c0b2cd15d3db106505096a34c3df9e5f2ac8',
    'runtime-before.txt': '1e7d11ef841f75a6c40f92fb2804a8a8ac16293e7b7e087af8232704c1460590',
    'tools-before.txt': '35bc8a07ca4672ca4033b5a340a8564b28e129fffa119d9fc7e2468fc661eb0f',
}
OWNERS = {
    'run-qualification.shs': '426e06d1abd19fa0a7f7a13ed1ac132f96762c1081fc7d330fc6f8060bcfdc83',
    'canonical-sanity-functions.shs': 'eed81b4fdd700555b8112fd4960f1670157bb32a221dbff42843999281be6490',
    'candidate-frontend-adapter.shs': '8720464ae6aa36ffae74e4c99055fdd81b3cf3630bca0b644592a7fcc61d4df8',
    'reviewed-inputs.sha256': '127e87a27b18ef34e02adf4675a8b9135d179990a88c79e6d5f6617a75a51f31',
    'native-proof.sha256': '30bf3cce2f4b078b578c4780991a27a161e787bed56cf2e51f81ab47ce6e075b',
}
COMPOSED_SCHEMA = 'simple-bootstrap-sanity-control-composition-v1'
FRESH_WRITER = '6ef8cd107ac6cc2575778cc9ddda69de425860fb86ddba2938a8fc42071cf52a'

def verify_actual_writer(path=None):
    path = path or pathlib.Path(__file__).parent / 'sanity-control-functions.shs'
    require(digest(path) == FRESH_WRITER, 'changed actual fresh writer')

def verify_composition_fields(composed, fresh, fresh_digest, control_digest):
    require(composed.get('schema') == COMPOSED_SCHEMA, 'unknown composition schema')
    require(composed.get('profile') == PROFILE, 'unknown composition profile')
    require(composed.get('status') == 'pass', 'composition status')
    require(composed.get('candidate_sha256') == CANDIDATE, 'composition candidate')
    for key, name in [('base_sanity_sha256','sanity.env'),
                      ('base_job_sha256','qualification.receipt.env'),
                      ('base_log_sha256','qualification.log')]:
        require(composed.get(key) == ARCHIVE[name], 'composition base identity: ' + key)
    require(composed.get('fresh_sanity_sha256') == fresh_digest, 'fresh sanity digest')
    require(fresh.get('schema') == 'simple-bootstrap-sanity-evidence-v1', 'fresh schema')
    require(fresh.get('status') == 'pass', 'fresh aggregate status')
    require(fresh.get('base_control_profile') == PROFILE, 'fresh control provenance')
    require(fresh.get('base_control_writer_sha256') == FRESH_WRITER, 'fresh control writer')
    require(fresh.get('base_control_snapshot_sha256') == control_digest,
            'fresh control snapshot')
    require(composed.get('control_snapshot_sha256') == control_digest,
            'composition control snapshot')
    for key, value in [('candidate_sha256_before',CANDIDATE),('candidate_sha256_after',CANDIDATE),
                       ('frontend_smoke_status','0'),('frontend_smoke_bootstrap1_ran','true'),
                       ('frontend_smoke_bootstrap_mode_status','0'),
                       ('frontend_smoke_bootstrap0_raw_status','0'),
                       ('frontend_smoke_bootstrap1_raw_status','0')]:
        require(fresh.get(key) == value, 'fresh full criterion: ' + key)

def composition(profile, archive, owner, candidate, source, git, runtime, tool,
                fresh_path, fresh_display):
    verify_actual_writer()
    verified = verify(profile, archive, owner, candidate, source, git, runtime, tool)
    control_bytes = ''.join(key+'='+value+'\n' for key,value in sorted(verified.items())).encode()
    control_digest = hashlib.sha256(control_bytes).hexdigest()
    fresh = records(fresh_path)
    result = {'schema':COMPOSED_SCHEMA,'profile':PROFILE,'status':'pass',
        'candidate_sha256':CANDIDATE,'base_sanity_sha256':ARCHIVE['sanity.env'],
        'base_job_sha256':ARCHIVE['qualification.receipt.env'],
        'base_log_sha256':ARCHIVE['qualification.log'],
        'fresh_sanity_sha256':digest(fresh_path),'fresh_sanity_display':fresh_display,
        'control_snapshot_sha256':control_digest}
    verify_composition_fields(result, fresh, digest(fresh_path), control_digest)
    return result

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def digest(path):
    require(path.is_absolute(), 'proof authority must be absolute')
    for component in [path, *path.parents]:
        info = component.lstat()
        require(not component.is_symlink() and
                not (getattr(info, 'st_file_attributes', 0) & 0x400),
                'proof authority reparse point')
    require(path.is_file() and not path.is_symlink(), 'unsafe or missing proof file')
    return hashlib.sha256(path.read_bytes()).hexdigest()

def records(path):
    result = {}
    for line in path.read_text(encoding='utf-8').splitlines():
        require('=' in line, 'malformed record')
        key, value = line.split('=', 1)
        require(key not in result, 'duplicate record')
        result[key] = value
    return result

def controls(sanity, job):
    required = {'schema': 'simple-bootstrap-sanity-evidence-v1', 'status': 'fail',
        'candidate_sha256_before': CANDIDATE, 'candidate_sha256_after': CANDIDATE,
        'version_status': '0', 'version_output': 'simple-bootstrap 1.0.0-rc.1',
        'version_expected': '1.0.0-rc.1', 'version_expect_status': '0',
        'version_match_status': '0', 'unsupported_status': '1',
        'unsupported_match_status': '0', 'sha_stable_status': '0',
        'unsupported_output_sha256': '373ffddd775f9bc524eb271bab164edcd7a51209a53058465cd0538c50c8d806',
        'frontend_smoke_status': '124'}
    for key, value in required.items():
        require(sanity.get(key) == value, 'historical control: ' + key)
    required_job = {'schema': 'simple-bounded-process-log-v1', 'status': 'complete',
        'reason': 'child-exit', 'raw_status': '1', 'native_exit_status': '1',
        'process_group': 'windows-job', 'root_exit_policy': 'wait-job',
        'helper_sha256': COLLECTOR, 'job_remnants_terminated': 'no',
        'max_bytes': '134217728', 'timeout_seconds': '7200',
        'log_sha256': ARCHIVE['qualification.log'], 'bytes_captured': '12923'}
    for key, value in required_job.items():
        require(job.get(key) == value, 'historical job: ' + key)
    return {'profile': PROFILE, 'historical_aggregate_status': 'fail',
        'version_output': sanity['version_output'], 'version_status': '0',
        'unsupported_status': sanity['unsupported_status'],
        'unsupported_match_status': sanity['unsupported_match_status'],
        'unsupported_output_sha256': sanity['unsupported_output_sha256']}

def verify(profile, archive, owner, candidate, source, git, runtime, tool):
    require(profile == PROFILE, 'unknown control profile')
    require(digest(candidate) == CANDIDATE, 'changed candidate')
    for name, expected in ARCHIVE.items():
        require(digest(archive / name) == expected, 'archive identity: ' + name)
    for name, expected in OWNERS.items():
        require(digest(owner / name) == expected, 'control owner: ' + name)
    for actual, name in [(source, 'source-before.txt'), (git, 'current-consumer-before.env'),
                         (runtime, 'runtime-before.txt'), (tool, 'tools-before.txt')]:
        require(digest(actual) == ARCHIVE[name], 'current tuple: ' + name)
    return controls(records(archive / 'sanity.env'), records(archive / 'qualification.receipt.env'))

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--profile', required=True)
    for name in ['archive', 'owner', 'candidate', 'source', 'git', 'runtime', 'tool']:
        p.add_argument('--' + name, required=True, type=pathlib.Path)
    p.add_argument('--format', choices=['json','env'], default='json')
    p.add_argument('--fresh-sanity', type=pathlib.Path)
    p.add_argument('--fresh-display')
    p.add_argument('--verify-composed', type=pathlib.Path)
    p.add_argument('--write-composed', type=pathlib.Path)
    a = p.parse_args()
    args = (a.profile, a.archive, a.owner, a.candidate,a.source,a.git,a.runtime,a.tool)
    if a.fresh_sanity:
        require(bool(a.fresh_display), 'fresh display absent')
        output = composition(*args,a.fresh_sanity,a.fresh_display)
        if a.verify_composed:
            actual = records(a.verify_composed)
            require(actual == output, 'composition record mismatch')
        if a.write_composed:
            require(not a.verify_composed, 'write and verify are separate operations')
            require(a.write_composed.parent.absolute() == a.fresh_sanity.parent.absolute(),
                    'composition output must be in owned companion parent')
            digest(a.fresh_sanity)  # no-follow authority/ancestor gate before exclusive creation
            fd = os.open(a.write_composed, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as stream:
                for key,value in sorted(output.items()):
                    require('\n' not in value and '\r' not in value, 'multiline value')
                    stream.write(key+'='+value+'\n')
    else:
        require(not a.verify_composed and not a.fresh_display, 'incomplete composition')
        output = verify(*args)
    if a.format == 'env':
        for key,value in sorted(output.items()):
            require('\n' not in value and '\r' not in value, 'multiline value')
            print(key+'='+value)
    else:
        print(json.dumps(output, sort_keys=True))

if __name__ == '__main__':
    main()
