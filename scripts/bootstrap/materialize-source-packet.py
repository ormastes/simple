"""Materialize an exclusively owned candidate using a pinned reusable archive.

Invoke with --config and --config-sha256. This is source readiness only, never
native qualification. Configuration and helper bytes are checked before use.
"""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, tarfile, time
import types, sys

if sys.flags.optimize:
    raise RuntimeError('materializer requires assertions enabled')
parser = argparse.ArgumentParser()
parser.add_argument('--config', required=True)
parser.add_argument('--config-sha256', required=True)
args = parser.parse_args()
config_path = pathlib.Path(args.config).resolve(strict=True)
config_bytes = config_path.read_bytes()
if hashlib.sha256(config_bytes).hexdigest() != args.config_sha256:
    raise RuntimeError('materialization config hash mismatch')
config = json.loads(config_bytes)
if config.get('schema') != 'bootstrap-materialization-request-v1':
    raise RuntimeError('unsupported materialization request')
packet = config_path.parent
root = pathlib.Path(config['source_root'])
repo = pathlib.Path(config['repository'])
revision = config['source_head']
archive_base = config['archive_source_head']
archive_path = pathlib.Path(config['archive_path'])
helper_path = pathlib.Path(__file__).with_name('materialization-path-boundary.py')
helper_bytes = helper_path.read_bytes()
if hashlib.sha256(helper_bytes).hexdigest() != config['boundary_helper_sha256']:
    raise RuntimeError('boundary helper hash mismatch')
# Execute exactly the verified bytes, avoiding a second unchecked import read.
boundary_module = types.ModuleType('materialization_boundary')
exec(compile(helper_bytes, str(helper_path), 'exec'), boundary_module.__dict__)
started = time.time()

def git(*args, cwd=repo):
    return subprocess.check_output(['git', '-C', str(cwd), *args])

def record(name, data):
    path = packet / name
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n', encoding='utf8')
    os.replace(temporary, path)

def progress(phase, count=0):
    record('progress.json', dict(pid=os.getpid(), phase=phase, count=count,
        elapsed_seconds=round(time.time()-started, 1), source_head=revision))

def sha256(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

assert root.exists() and git('rev-parse', 'HEAD', cwd=root).decode().strip() == revision, 'approved isolated candidate differs'
assert git('rev-parse', revision).decode().strip() == revision
assert git('rev-parse', '--show-object-format').decode().strip() == 'sha1'
boundary = boundary_module.MaterializationBoundary(root)
progress('create-worktree')
assert not git('diff', '--cached', '--name-only', cwd=root).strip(), 'candidate index differs'
git('read-tree', 'HEAD', cwd=root)
assert archive_path.is_file()
assert sha256(archive_path) == config['archive_sha256'], 'archive hash mismatch'
assert not git('diff','--name-only','--diff-filter=D',archive_base,revision).strip()
progress('reuse-full-base-archive')
entries = {}
for row in git('ls-tree', '-r', '-z', revision).split(b'\0'):
    if not row: continue
    meta, name = row.split(b'\t', 1)
    mode, kind, oid = meta.decode().split()
    entries[name.decode()] = dict(mode=mode, kind=kind, oid=oid)
regular = []
aliases = []
progress('extract')
with tarfile.open(archive_path, 'r|') as archive:
    for member in archive:
        relative = pathlib.PurePosixPath(member.name)
        path = root / member.name
        assert boundary.contains(path) and '.git' not in relative.parts
        if member.isdir():
            path.mkdir(parents=True, exist_ok=True)
        elif member.isfile():
            assert entries[member.name]['kind'] == 'blob' and entries[member.name]['mode'] != '120000'
            path.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(member) as source, path.open('xb') as output:
                shutil.copyfileobj(source, output, 1024*1024)
            regular.append(member.name)
            if len(regular) % 5000 == 0: progress('extract', len(regular))
        elif member.issym():
            assert entries[member.name]['mode'] == '120000'
            target_bytes = member.linkname.encode()
            actual_oid = hashlib.sha1(b'blob '+str(len(target_bytes)).encode()+b'\0'+target_bytes).hexdigest()
            assert actual_oid == entries[member.name]['oid'], 'alias blob mismatch: '+member.name
            aliases.append((member.name, member.linkname))
        else:
            raise RuntimeError('unsupported archive member: '+member.name)
        archive.members.clear()
expected_regular = {name for name,e in entries.items() if e['kind']=='blob' and e['mode']!='120000'}
assert not (set(regular)-expected_regular), 'unlisted archive regular file'
missing = sorted(expected_regular-set(regular))
record('archive-exact-inventory.json',dict(missing_regular=missing,extra_regular=[]))
progress('restore-omitted-git-blobs')
restored = []
for name in missing:
    path=root/name
    assert not path.exists() and boundary.contains(path)
    payload=git('cat-file','blob',entries[name]['oid'])
    assert hashlib.sha1(b'blob '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==entries[name]['oid']
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as output: output.write(payload)
    restored.append(dict(path=name,git_blob=entries[name]['oid'],bytes=len(payload)))
record('restored-archive-omissions.json',restored)
regular=sorted(expected_regular)
aliases=[]
for name,e in entries.items():
    if e['mode']=='120000':
        payload=git('cat-file','blob',e['oid'])
        assert hashlib.sha1(b'blob '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==e['oid']
        aliases.append((name,payload.decode()))
restored = json.loads((packet/'restored-archive-omissions.json').read_text())
folded = {}
for name in regular:
    key=name.casefold()
    assert key not in folded or entries[folded[key]]['oid']==entries[name]['oid'], 'unrepresentable Windows case collision: '+name
    folded[key]=name
progress('authenticate-physical-blobs')
manifest = packet / 'physical-git-blobs-final.tsv'
mismatches = []
with manifest.open('x', encoding='utf8', newline='\n') as output:
    for index, name in enumerate(sorted(regular), 1):
        path = root / name
        digest = hashlib.sha1(b'blob '+str(path.stat().st_size).encode()+b'\0')
        with path.open('rb') as stream:
            for chunk in iter(lambda: stream.read(1024*1024), b''): digest.update(chunk)
        if digest.hexdigest() != entries[name]['oid']: mismatches.append(dict(path=name,actual_git_blob=digest.hexdigest(),expected_git_blob=entries[name]['oid']))
        output.write(entries[name]['oid']+'\t'+name+'\n')
        if index % 5000 == 0: progress('authenticate-physical-blobs', index)
record('physical-blob-mismatches.json',mismatches)
progress('repair-archive-transforms',len(mismatches))
for item in mismatches:
    name=item['path']; path=root/name
    assert boundary.contains(path)
    preserved=packet/'archive-transformed-originals'/name
    preserved.parent.mkdir(parents=True,exist_ok=True)
    with path.open('rb') as source,preserved.open('xb') as output: shutil.copyfileobj(source,output)
    payload=git('cat-file','blob',item['expected_git_blob'])
    assert hashlib.sha1(b'blob '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==item['expected_git_blob']
    before=path.read_bytes()
    item['crlf_only']=before.replace(b'\r\n',b'\n')==payload.replace(b'\r\n',b'\n')
    with path.open('wb') as output: output.write(payload)
    actual=path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(actual)).encode()+b'\0'+actual).hexdigest()==item['expected_git_blob']
record('physical-blob-transform-repairs.json',mismatches)
progress('aliases')
report = []
for name, target in aliases:
    link = root / name
    destination = (link.parent / target).resolve()
    assert boundary.contains(destination), 'external alias: '+name
    assert not link.exists() and not link.is_symlink()
    link.parent.mkdir(parents=True, exist_ok=True)
    if destination.is_dir():
        assert all(not any(c in str(value) for c in '&|<>^%!"') for value in (link,destination))
        subprocess.run(['cmd.exe','/d','/c','mklink','/J',str(link),str(destination)], check=True, stdout=subprocess.DEVNULL)
        assert link.resolve() == destination
        representation = 'directory-junction'
        content_sha256 = None
    elif destination.is_file():
        with destination.open('rb') as source, link.open('xb') as output: shutil.copyfileobj(source,output)
        content_sha256 = sha256(link)
        assert content_sha256 == sha256(destination)
        representation = 'file-copy'
    else:
        assert not name.startswith(('src/','test/')), 'unresolved build alias: '+name
        link.write_text(target, encoding='utf8', newline='')
        representation = 'unresolved-nonbuild-link-text'
        content_sha256 = sha256(link)
    report.append(dict(path=name,target=target,representation=representation,content_sha256=content_sha256))
required = ['src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h',
    'tools/counterpart/sdk/c/simple_counterpart_abi.h','src/app/t32_cli/mod.spl',
    'src/runtime/runtime_native.c','src/runtime/runtime.h','src/app/cli/interpreter_main.spl',
    'src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl',
    'scripts/bootstrap/bootstrap-logged-process.shs','config/var.sdn']
for name in required: assert (root/name).is_file(), 'missing required physical input: '+name
assert (root/'scripts/resource').is_dir(), 'missing resource helper closure'
assert git('rev-parse','HEAD',cwd=root).decode().strip() == revision
assert not git('diff','--cached','--name-only',cwd=root).strip(), 'unexpected index changes'
receipt = dict(schema='bootstrap-source-materialization-v2',source_root=str(root),source_head=revision,
    archive_source_head=archive_base,archive_path=str(archive_path),archive_sha256=sha256(archive_path),archive_omissions_restored=restored,archive_transform_repairs=mismatches,tracked_regular_blob_count=len(regular),
    physical_git_blob_manifest=str(manifest),physical_git_blob_manifest_sha256=sha256(manifest),
    authenticated_regular_blobs=len(regular),aliases=report,required_physical_inputs=required,
    physical_build_inputs_ready=True,diagnostic_source_ready=True,frozen=True,native_verified=False,
    production_qualified=False,admitted=False,elapsed_seconds=round(time.time()-started,1))
receipt.update(materialization_request_sha256=args.config_sha256,
    boundary_helper_sha256=config['boundary_helper_sha256'],
    materializer_sha256=sha256(pathlib.Path(__file__)))
boundary.verify_root()
record('source-ready.json',receipt)
progress('complete',len(regular))
print(json.dumps(dict(source_root=str(root),source_head=revision,regular_files=len(regular),aliases=len(report),ready=True)))
