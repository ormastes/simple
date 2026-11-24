"""Download exact eligible full-CLI artifact once, without executing any product."""
import argparse,json,subprocess,hashlib
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--kind',choices=['early','phase3'],required=True);p.add_argument('--run',type=int,required=True)
p.add_argument('--artifact',type=int,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
def api(route):return json.loads(subprocess.check_output(['gh','api','repos/ormastes/simple/'+route]))
r=api(f'actions/runs/{a.run}');artifact=api(f'actions/artifacts/{a.artifact}')
control={'early':'d18104ea541e35a2fdcbe3561461605c0e6d38ac','phase3':'4251185d95178ced5f102075c332096e18b74c91'}[a.kind]
assert r['head_sha']==control and r['status']=='completed' and r['conclusion']=='success'
assert artifact['workflow_run']['id']==r['id'] and not artifact['expired']
prefix='ce231-child-early-phase4-' if a.kind=='early' else 'provisional-ce231-phase4-from-phase3-'
assert artifact['name']==prefix+str(r['id'])
for name,value in [('run.json',r),('artifact.json',artifact)]:
    (a.output/name).write_text(json.dumps(value,indent=2))
archive=a.output/'artifact.zip'
with archive.open('xb') as stream:
    subprocess.run(['gh','api',f'repos/ormastes/simple/actions/artifacts/{a.artifact}/zip'],stdout=stream,check=True,timeout=900)
with archive.open('rb') as stream:assert artifact['digest']=='sha256:'+hashlib.file_digest(stream,'sha256').hexdigest()
print('Verified artifact retained; product not executed.')
