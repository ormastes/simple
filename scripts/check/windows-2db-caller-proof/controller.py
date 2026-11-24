"""Actual merged compiler, original filename, one linked focused worker fixture."""
import hashlib, importlib.util, json, os, pathlib, sys, traceback
P = pathlib.Path
HERE = P(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('intake', HERE/'proof.py')
n = importlib.util.module_from_spec(spec); spec.loader.exec_module(n)


def ledgers(cache, fixture, root):
    inventories = []; objects = []; found = False
    relative = str(fixture.relative_to(n.ROOT)).replace('\\','/')
    snapshots = []; source_inventories = []
    for scv in (n.ROOT/'build/scv', n.ROOT/'.simple/scv'):
        if not scv.exists(): continue
        snapshots.extend(p for p in scv.rglob(fixture.name) if '/snapshots/' in p.as_posix() and p.as_posix().endswith('/'+relative))
        source_inventories.extend(p for p in scv.rglob('*inventory*') if p.is_file())
    assert snapshots and all(p.read_bytes()==fixture.read_bytes() for p in snapshots)
    needle=(relative+'|'+n.sha(fixture)+'|').encode()
    matching=[p for p in source_inventories if needle in p.read_bytes()]
    assert matching, 'raw fixture must be bound by actual SCV source inventory'
    for inventory in cache.rglob('inventory'):
        rows = inventory.read_text(encoding='utf-8').splitlines()
        if len(rows) < 2 or not list(inventory.parent.glob('*.claim')):
            continue
        excluded = set((inventory.parent/'excluded').read_text().splitlines()) if (inventory.parent/'excluded').exists() else set()
        records = []
        for key in (x for x in rows[1:] if x and x not in excluded):
            stem = hashlib.sha256(key.encode()).hexdigest()
            terminal = inventory.parent/(stem+'.terminal')
            claim = inventory.parent/(stem+'.claim')
            fields = terminal.read_text().splitlines(); claimed = claim.read_text().splitlines()
            assert len(fields) == 5 and fields[0] == 'PASS' and fields[2] == key
            assert fields[1:4] == claimed[:3]
            assert fields[4] in ('CACHE_STORED','UNCACHED')
            done = inventory.parent/(hashlib.sha256(fields[1].encode()).hexdigest()+'.done')
            assert done.read_bytes() == fields[1].encode()
            if key.replace('\\','/').endswith('/'+str(fixture.relative_to(n.ROOT)).replace('\\','/')):
                found = True
            records.append({'key':key,'terminal_sha256':n.sha(terminal),'owner':fields[1],'done_sha256':n.sha(done)})
        assert records
        inventories.append({'path':str(inventory),'sha256':n.sha(inventory),'records':records})
    for receipt in cache.rglob('*.receipt'):
        try: row = n.fields(receipt)
        except (ValueError, UnicodeError): continue
        if row.get('status') != 'PASS' or not row.get('module') or not row.get('object'): continue
        assert any(str(receipt.parent/'inventory') == q['path'] and any(r['key']==row['module'] for r in q['records']) for q in inventories)
        terminal = receipt.parent/(hashlib.sha256(row['module'].encode()).hexdigest()+'.terminal')
        fields = terminal.read_text().splitlines()
        assert len(fields)==5 and fields[0] == 'PASS' and fields[2] == row['module'] and fields[4] in ('CACHE_STORED','UNCACHED')
        assert fields[3] == (receipt.parent/'inventory').read_text().splitlines()[0]
        assert receipt.name == hashlib.sha256(row['module'].encode()).hexdigest()+'.receipt'
        raw = row['object'].replace('\\','/')
        if len(raw)>3 and raw[0]=='/' and raw[2]=='/': raw=raw[1].upper()+':'+raw[2:]
        obj = P(raw)
        assert obj.resolve().is_relative_to(root.resolve())
        assert obj.is_file() and obj.stat().st_size>20 and obj.read_bytes()[:2] == b'\x64\x86'
        objects.append({'module':row['module'],'path':str(obj),'sha256':n.sha(obj),'receipt_sha256':n.sha(receipt)})
    assert len(inventories)>=2 and found and objects
    n.save('worker-evidence.json',{'status':'SEALED_WORKER_PASS','inventories':inventories,'objects':objects,'fixture_sha256':n.sha(fixture),
        'snapshots':{str(p):n.sha(p) for p in snapshots},'source_inventories':{str(p):n.sha(p) for p in matching},
        'cache_key_scope':'claim/terminal equality; composite cache key is not raw source SHA'})


def main():
    assert sys.platform == 'win32'
    compiler, bundle = n.intake(); tools = n.toolchain(); llvm = n.provider()
    assert compiler.name == 'simple_stage2.exe' and n.sha(compiler) == n.BINDING['compiler_sha256']
    assert (n.ROOT/'src/runtime/runtime.c').is_file()
    env = {k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
    env.update(PATH=';'.join([str(llvm),str(tools),str(n.BASH.parent.parent/'usr/bin'),str(n.BASH.parent.parent/'mingw64/bin'),env['PATH']]),
        CC=str(tools/'clang.exe'),CXX=str(tools/'clang++.exe'),SIMPLE_MINGW_ROOT=n.posix(tools.parent),SIMPLE_WINDOWS_ABI='gnu',
        SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_RUNTIME_PATH=str(bundle),SIMPLE_PROJECT_ROOT=str(n.ROOT),SIMPLE_LIB=str(n.ROOT/'src'),
        SIMPLE_BINARY=str(compiler),SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_BOOTSTRAP_STAGE3='1',SIMPLE_MIR_SHARDING='1',
        SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_FILE_WORKER_BATCH='4',SIMPLE_PARSE_SHARDING='1',
        SIMPLE_FRONTEND_CACHE='1',SIMPLE_HIR_CACHE='1',SIMPLE_NATIVE_ARENA_DECLS='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_KEEP_TEMP='1',
        SIMPLE_BUILD_MEMORY_RESERVE_BYTES=str(2*1024**3))
    imports = n.command([tools/'llvm-readobj.exe','--coff-imports',compiler],capture_output=True,text=True).stdout
    if 'libLLVM-23.dll' in imports:
        n.command([n.BASH,n.ROOT/'scripts/setup/bundle-llvm-runtime-dlls.shs',n.posix(compiler),n.posix(llvm)],env=env)
    identities = {str(p.relative_to(n.OUT)):n.sha(p) for base in (compiler.parent,bundle,tools,llvm) for p in base.rglob('*') if p.is_file()}
    tracked = n.command(['git','ls-files','-z'],capture_output=True).stdout.decode().split('\0')
    sources = {p:n.sha(n.ROOT/p) for p in tracked if p and (n.ROOT/p).is_file()}
    n.save('source-files.json',sources); n.save('inputs.json',{'source':n.SOURCE,'compiler_sha256':n.sha(compiler),'files':identities,'binding':n.BINDING,'control':os.environ['GITHUB_SHA']})
    fixture = n.ROOT/'test/fixtures/windows_2db_full_caller/main.spl'
    assert not fixture.parent.exists(); fixture.parent.mkdir(parents=True)
    fixture.write_bytes(b'fn main() -> i64:\n    print "windows-full-caller-ok"\n    return 0\n')
    n.command(['git','add','--',fixture.relative_to(n.ROOT)])
    staged=n.command(['git','diff','--cached','--name-only'],capture_output=True,text=True).stdout.splitlines()
    assert staged == [fixture.relative_to(n.ROOT).as_posix()]
    fixture_hash=n.sha(fixture); n.save('fixture.json',{'path':str(fixture.relative_to(n.ROOT)),'sha256':fixture_hash,'body':fixture.read_text(),'project_root':str(n.ROOT),'selection':'explicit MIR-sharded dynload entry; production focused Stage3 route'})
    cache=n.OUT/'cache'; product=n.OUT/'linked/worker.exe'; product.parent.mkdir()
    for leaf in ('tmp','storage'): (n.OUT/leaf).mkdir()
    env.update(SIMPLE_CACHE=str(cache),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache),SIMPLE_FRONTEND_CACHE_DIR=str(cache/'frontend'),SIMPLE_HIR_CACHE_DIR=str(cache/'hir'),
        SIMPLE_USER_STORAGE_ROOT=str(n.OUT/'storage'),TMP=str(n.OUT/'tmp'),TEMP=str(n.OUT/'tmp'),TMPDIR=n.posix(n.OUT/'tmp'))
    cap=n.budget()
    for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):env[key]=str(cap)
    launcher=n.OUT/'compile.sh'
    launcher.write_bytes(b'set -eu\nSTAGE3_POLICY_SDN="$1"; export STAGE3_POLICY_SDN; shift\n. "$1"; shift\nstage3_apply_native_host_link_policy x86_64-pc-windows-gnu file mingw dynlib\nexport SIMPLE_MIR_SHARDING=1\nexec "$@"\n')
    argv=[str(n.BASH),n.posix(launcher),n.posix(n.ROOT/'scripts/bootstrap/stage3-native-host-link-policy.sdn'),n.posix(n.ROOT/'scripts/bootstrap/stage3-native-host-link-policy.shs'),
        n.posix(compiler),'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu','--runtime-bundle','core-c-bootstrap','--runtime-path',n.posix(bundle),
        '--threads','1','--source',str(fixture.parent.relative_to(n.ROOT)).replace('\\','/'),'--entry-closure','--entry',str(fixture.relative_to(n.ROOT)).replace('\\','/'),
        '--mode','dynload','--cache-dir',n.posix(cache),'--output',n.posix(product)]
    try:
        n.owned('compile',argv,cap,600,env)
        log=(n.OUT/'compile.stdout').read_text(encoding='utf-8')
        assert '[stage3-route] per-file worker pool + per-module link' in log and 'running compiler path unavailable' not in log
        ledgers(cache,fixture,n.OUT)
        pe=n.command([tools/'llvm-readobj.exe','--file-headers','--coff-imports',product],capture_output=True,text=True).stdout
        (n.OUT/'product.imports').write_text(pe); assert 'COFF-x86-64' in pe
        digest=n.sha(product)
        n.owned('execute',[str(product)],262144,30,env)
        assert (n.OUT/'execute.stdout').read_bytes().replace(b'\r\n',b'\n') == b'windows-full-caller-ok\n'
        assert n.sha(product)==digest
        result={'status':'ORIGINAL_NAME_FULL_CALLER_LINKED_PASS','source':n.SOURCE,'compiler_sha256':n.sha(compiler),'compiler_name':compiler.name,'product_sha256':digest,'fixture_sha256':fixture_hash,
            'scope':'actual merged compiler focused worker, linked PE and native execution; not Phase3 generation or formal admission'}
    finally:
        unchanged=all(n.sha(n.ROOT/p)==h for p,h in sources.items()) and all(n.sha(n.OUT/p)==h for p,h in identities.items()) and n.sha(fixture)==fixture_hash
        assert n.command(['git','diff','--cached','--name-only'],capture_output=True,text=True).stdout.splitlines()==staged
        n.save('immutable-inputs.json',{'unchanged':unchanged}); assert unchanged
    n.save('terminal.json',result)


if __name__=='__main__':
    try: main()
    except BaseException as error:
        n.save('failure.json',{'error':str(error),'traceback':traceback.format_exc()}); raise
