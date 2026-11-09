"""Guard only the workflows observed in the Nov 9 Node20 annotations.

Requires PyYAML and authenticated gh. Reads official action metadata over the
GitHub API; --base additionally verifies all other workflow behavior is intact.
"""
import argparse
import base64
import copy
import json
from pathlib import Path
import subprocess
import yaml

ROOT = Path(__file__).resolve().parents[2]
FILES = ['build-binaries.yml', 'phase-ladder.yml', 'phase-ladder-rung.yml']
VERSIONS = {'checkout': 'v5', 'cache': 'v5', 'download-artifact': 'v7', 'upload-artifact': 'v6'}
RUNNERS = {'ubuntu-24.04', 'macos-15', 'macos-15-intel', 'windows-2025'}


def validate(workflow, metadata):
    count = 0
    for job in workflow['jobs'].values():
        runner = job.get('runs-on')
        if runner is None:  # reusable workflow invocation
            continue
        if runner == '${{ matrix.os }}':
            assert all(row['os'] in RUNNERS for row in job['strategy']['matrix']['include'])
        else:
            assert isinstance(runner, str) and runner in RUNNERS, f'runner requires Node24 qualification: {runner}'
        for step in job.get('steps', []):
            uses = step.get('uses', '')
            for action, version in VERSIONS.items():
                if not uses.startswith('actions/' + action + '@'):
                    continue
                assert uses == f'actions/{action}@{version}', uses
                assert metadata[action]['runs']['using'] == 'node24'
                assert set(step.get('with', {})) <= set(metadata[action].get('inputs', {})), uses
                if action == 'download-artifact' and 'name' in step.get('with', {}):
                    assert not step.get('continue-on-error', False), 'required named artifact must fail'
                count += 1
    return count


def rejects(workflow, metadata):
    try:
        validate(workflow, metadata)
    except AssertionError:
        return
    raise AssertionError('negative control was accepted')


parser = argparse.ArgumentParser()
parser.add_argument('--base', help='revision before the three workflow edits')
args = parser.parse_args()
metadata = {}
for action, version in VERSIONS.items():
    payload = subprocess.check_output(['gh', 'api', f'repos/actions/{action}/contents/action.yml?ref={version}'])
    metadata[action] = yaml.safe_load(base64.b64decode(json.loads(payload)['content']))
    print(f'official actions/{action}@{version}: {metadata[action]["runs"]["using"]}')
# Official action implementation preserves a failed lookup for a named artifact.
payload = subprocess.check_output(['gh', 'api', 'repos/actions/download-artifact/contents/src/download-artifact.ts?ref=v7'])
source = base64.b64decode(json.loads(payload)['content']).decode()
assert 'throw new Error(`Artifact' in source and "not found`" in source
count = 0
for filename in FILES:
    path = ROOT / '.github/workflows' / filename
    workflow = yaml.safe_load(path.read_text())
    count += validate(workflow, metadata)
    if args.base:
        original = subprocess.check_output(['git', 'show', f'{args.base}:.github/workflows/{filename}'], cwd=ROOT).decode()
        for action, version in VERSIONS.items():
            original = original.replace(f'actions/{action}@v4', f'actions/{action}@{version}')
        original = original.replace('          if-no-artifact-found: warn\n', '')
        assert yaml.safe_load(original) == workflow, f'unrelated workflow behavior changed: {filename}'
    print(f'{filename}: PASS')
probe = {'jobs': {'test': {'runs-on': 'ubuntu-24.04', 'steps': [
    {'uses': 'actions/download-artifact@v7', 'with': {'name': 'required'}}]}}}
validate(probe, metadata)
for key, value in [('uses', 'actions/download-artifact@v4'), ('continue-on-error', True)]:
    negative = copy.deepcopy(probe)
    negative['jobs']['test']['steps'][0][key] = value
    rejects(negative, metadata)
negative = copy.deepcopy(probe)
negative['jobs']['test']['steps'][0]['with']['if-no-artifact-found'] = 'warn'
rejects(negative, metadata)
negative = copy.deepcopy(probe)
negative['jobs']['test']['runs-on'] = ['self-hosted']
rejects(negative, metadata)
print(f'PASS {count} official Node24 action uses; input/version/runner/required-artifact negative controls')
