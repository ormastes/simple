"""Retain one reviewed native server identity; protocol acceptance belongs to SSpec."""
import argparse,hashlib,json,subprocess,zipfile,stat,struct
from pathlib import Path,PurePosixPath
p=argparse.ArgumentParser(description=__doc__)
for name in ['run','artifact','member','sha256','source-revision']:p.add_argument('--'+name,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert a.source_revision=='ce231b5b898d797c98d44a9b59a4859a7d792a7b'
a.output.mkdir(parents=True,exist_ok=False)
def api(route):return json.loads(subprocess.check_output(['gh','api','repos/ormastes/simple/'+route]))
def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
run=api('actions/runs/'+a.run);artifact=api('actions/artifacts/'+a.artifact)
assert run['status']=='completed' and artifact['workflow_run']['id']==int(a.run) and not artifact['expired']
assert run['head_sha']==a.source_revision, 'different controller/source requires a separately reviewed hash-bound source receipt adapter'
assert artifact['workflow_run']['head_sha']==a.source_revision
# A retained actual binary may exist despite a later failing job; do not require prior protocol PASS.
for name,value in [('run.json',run),('artifact.json',artifact)]:(a.output/name).write_text(json.dumps(value,indent=2))
archive=a.output/'artifact.zip'
with archive.open('xb') as f:subprocess.run(['gh','api',f'repos/ormastes/simple/actions/artifacts/{a.artifact}/zip'],stdout=f,check=True,timeout=900)
assert artifact['digest']=='sha256:'+sha(archive)
with zipfile.ZipFile(archive) as z:
    matches=[x for x in z.infolist() if x.filename==a.member];assert len(matches)==1
    info=matches[0];path=PurePosixPath(a.member)
    assert not path.is_absolute() and '..' not in path.parts and ':' not in a.member and '\\' not in a.member
    assert not stat.S_ISLNK(info.external_attr>>16) and 64<=info.file_size<1024**3
    target=a.output/'simple_mcp_server'
    import shutil
    with z.open(info) as src,target.open('xb') as dst:shutil.copyfileobj(src,dst)
assert sha(target)==a.sha256
with target.open('rb') as f:header=f.read(64)
assert header[:6]==b'\x7fELF\x02\x01' and struct.unpack_from('<H',header,18)[0]==62
assert struct.unpack_from('<H',header,16)[0] in (2,3)
target.chmod(0o755)
(a.output/'identity.json').write_text(json.dumps({'source_revision':a.source_revision,'sha256':a.sha256,'artifact_member':a.member,
    'source_binding':'exact GitHub run and artifact source head; no protocol acceptance inferred',
    'artifact_id':int(a.artifact),'run_id':int(a.run)},indent=2))
