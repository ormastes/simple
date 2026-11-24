"""Download a completed, exact-controller parent once; verify without starting Phase4."""
import argparse, hashlib, json, os, shutil, stat, subprocess, zipfile
from pathlib import Path, PurePosixPath
from parent_gate import CONTROL, SOURCE, RUNTIME_ID, RUNTIME_ZIP_SHA, verify, sha

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source',type=Path,required=True)
p.add_argument('--intake',type=Path,required=True)
p.add_argument('--parent-run',type=int,required=True)
p.add_argument('--parent-artifact-id',type=int,required=True)
p.add_argument('--parent-sha256',required=True)
a=p.parse_args()
source=a.source.resolve(); intake=a.intake.resolve()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==SOURCE
intake.mkdir(parents=True,exist_ok=False)
def api(route):
    return json.loads(subprocess.check_output(['gh','api','repos/ormastes/simple/'+route]))
def save(name,value):
    (intake/name).write_text(json.dumps(value,indent=2))
def download(artifact,path):
    assert not artifact['expired']
    with path.open('xb') as f:
        subprocess.run(['gh','api',f"repos/ormastes/simple/actions/artifacts/{artifact['id']}/zip"],stdout=f,check=True)
    assert artifact['digest']=='sha256:'+sha(path)
def extract_selected(archive,destination,selected):
    with zipfile.ZipFile(archive) as z:
        seen=set()
        for info in z.infolist():
            name=info.filename; path=PurePosixPath(name)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in name and ':' not in name
            assert path.as_posix().rstrip('/')==name.rstrip('/')
            assert not stat.S_ISLNK(info.external_attr>>16)
            assert name.casefold() not in seen; seen.add(name.casefold())
            if info.is_dir() or not selected(name):continue
            assert info.file_size<1024**3, 'unexpected individual evidence size'
            target=destination.joinpath(*path.parts);target.parent.mkdir(parents=True,exist_ok=True)
            with z.open(info) as src,target.open('xb') as dst:shutil.copyfileobj(src,dst)
run=api(f'actions/runs/{a.parent_run}')
assert run['head_sha']==CONTROL and run['status']=='completed' and run['conclusion']=='success'
artifact=api(f'actions/artifacts/{a.parent_artifact_id}')
assert artifact['workflow_run']['id']==a.parent_run
assert artifact['name']==f'ce231-child-phase3-{a.parent_run}'
save('run.json',run);save('artifact.json',artifact)
download(artifact,intake/'artifact.zip')
required={'ce231-contract.json','ce231-phase3/terminal.json','ce231-phase3/owner.env','source/build/bootstrap/stage3/simple'}
extract_selected(intake/'artifact.zip',intake/'extracted',lambda n:n in required or n.startswith('ce231-phase3/qualification/'))
ra=api(f'actions/artifacts/{RUNTIME_ID}')
assert ra['workflow_run']['id']==45286831153 and ra['digest']=='sha256:'+RUNTIME_ZIP_SHA
save('runtime-artifact.json',ra);download(ra,intake/'runtime.zip')
extract_selected(intake/'runtime.zip',intake/'runtime-extracted',lambda n:n.endswith('manifest.json') or '/runtime/' in n or n.startswith('runtime/'))
manifests=[]
for path in (intake/'runtime-extracted').rglob('manifest.json'):
    value=json.loads(path.read_text())
    if value.get('source_revision')==SOURCE and value.get('status')=='BUILT_UNQUALIFIED':manifests.append((path,value))
assert len(manifests)==1
manifest_path,manifest=manifests[0]
root=source/'build/phase4-from-ce231-phase3'
(root/'parent').mkdir(parents=True,exist_ok=False);(root/'runtime').mkdir(exist_ok=False)
parent=root/'parent/simple'
shutil.copyfile(intake/'extracted/source/build/bootstrap/stage3/simple',parent);parent.chmod(0o755)
for name,record in manifest['files'].items():
    path=PurePosixPath(name)
    assert not path.is_absolute() and '..' not in path.parts and ':' not in name and '\\' not in name
    src=manifest_path.parent/'runtime'/name
    assert sha(src)==record['sha256']
    dst=root/'runtime'/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
proof=verify(parent,intake,root/'runtime',a.parent_sha256,a.parent_artifact_id)
save('verified-parent.json',proof)
print('Parent native behavior verified; Phase4 was NOT started.')
