"""One bounded native renamed-image regression; not a rebuilt compiler proof."""
import importlib.util, json, os, pathlib, sys, traceback
P=pathlib.Path
HERE=P(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('intake',HERE/'proof.py')
n=importlib.util.module_from_spec(spec);spec.loader.exec_module(n)
n.OUT=n.ROOT/'build/windows-self-image-proof';n.OUT.mkdir(parents=True,exist_ok=True)
SOURCE='7caac0600ded6dfae8882ce3eaf0a0038288e92f'
BASE='002e381e56259b60f7da059f52dd469e5bd60b11'

def main():
    assert sys.platform=='win32'
    path='src/app/cli/native_build_main.spl'
    original=n.command(['git','show',BASE+':'+path],capture_output=True,text=True,encoding='utf-8').stdout
    current=(n.ROOT/path).read_text(encoding='utf-8')
    added=('    # Windows worker identity is the kernel image, not a particular basename,\n'
           '    # argv[0], or a configured compiler. Renamed native producers are valid.\n'
           '    if host_os() == "windows":\n'
           '        return cli_kernel_executable_path()\n')
    assert current==original.replace('fn self_exe() -> text:\n','fn self_exe() -> text:\n'+added)
    assert current.count(added)==1
    helper_paths=['src/app/io/cli_ops.spl','src/app/io/env_ops.spl',
                  'src/lib/nogc_sync_mut/io/windows_image_owner.spl',
                  'src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl']
    for helper in helper_paths:
        baseline=n.command(['git','show',n.SOURCE+':'+helper],capture_output=True,text=True,encoding='utf-8').stdout
        assert (n.ROOT/helper).read_text(encoding='utf-8')==baseline,(helper,'lookup owner changed')
    fixture=n.ROOT/'test/fixtures/bootstrap/windows_native_build_self_image.spl'
    source_files={p:n.sha(n.ROOT/p) for p in [path,*helper_paths,str(fixture.relative_to(n.ROOT))]}
    n.save('source-wiring.json',{'source':SOURCE,'base':BASE,'files':source_files,
           'claim':'Windows call site delegates to actual tested kernel owner; non-Windows body unchanged; full caller not rebuilt'})
    compiler,bundle=n.intake(SOURCE);tools=n.toolchain();llvm=n.provider()
    assert n.sha(compiler)=='f8be04ff2979d4b41cd038f8aa3601619891ec7cf74b55dbe73f06c84baa85f0'
    env=dict(os.environ)
    for key in list(env):
        if key.startswith('SIMPLE_'):del env[key]
    env.update(PATH=';'.join([str(llvm),str(tools),str(n.BASH.parent.parent/'usr/bin'),str(n.BASH.parent.parent/'mingw64/bin'),env['PATH']]),
       CC=str(tools/'clang.exe'),CXX=str(tools/'clang++.exe'),SIMPLE_MINGW_ROOT=n.posix(tools.parent),
       SIMPLE_WINDOWS_ABI='gnu',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_RUNTIME_PATH=str(bundle),
       SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_KEEP_TEMP='1',
       SIMPLE_PROJECT_ROOT=str(n.ROOT),SIMPLE_LIB=str(n.ROOT/'src'),
       SIMPLE_FRONTEND_CACHE_DIR=str(n.OUT/'cache/frontend'),SIMPLE_HIR_CACHE_DIR=str(n.OUT/'cache/hir'))
    imports=n.command([tools/'llvm-readobj.exe','--coff-imports',compiler],capture_output=True,text=True).stdout
    if 'libLLVM-23.dll' in imports:
        n.command([n.BASH,n.ROOT/'scripts/setup/bundle-llvm-runtime-dlls.shs',n.posix(compiler),n.posix(llvm)],env=env)
    identities={str(p.relative_to(n.OUT)):n.sha(p) for base in (n.OUT/'compiler',bundle) for p in base.rglob('*') if p.is_file()}
    identities.update({str(p.relative_to(n.OUT)):n.sha(p) for base in (tools,llvm) for p in base.glob('*.dll')})
    identities[str((tools/'clang.exe').relative_to(n.OUT))]=n.sha(tools/'clang.exe')
    n.save('inputs.json',{'source':SOURCE,'compiler_source':n.SOURCE,'compiler_sha256':n.sha(compiler),'files':identities,'binding':n.BINDING,'control':os.environ['GITHUB_SHA']})
    product=n.OUT/'renamed producer/simple_stage2.exe';product.parent.mkdir()
    cap=n.budget()
    n.owned('compile',[str(compiler),'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu',
        '--runtime-bundle','core-c-bootstrap','--runtime-path',str(bundle),'--threads','1',
        '--source','src/compiler','--source','src/app','--source','src/lib','--entry-closure',
        '--mode','one-binary','--entry',str(fixture.relative_to(n.ROOT)).replace('\\','/'),
        '--cache-dir',str(n.OUT/'cache'),'--output',str(product)],cap,900,env)
    assert product.is_file()
    pe=n.command([tools/'llvm-readobj.exe','--coff-imports',product],capture_output=True,text=True).stdout
    (n.OUT/'fixture.imports').write_text(pe,encoding='utf-8')
    assert 'COFF-x86-64' in pe and 'Symbol: GetModuleFileNameW (' in pe
    digest=n.sha(product)
    runner=n.OUT/'run-renamed.py'
    runner.write_text("import subprocess,sys\np=subprocess.run(['C:/stale/simple.exe',sys.argv[2]],executable=sys.argv[1],timeout=30)\nraise SystemExit(p.returncode)\n",encoding='utf-8')
    run_env=dict(env);run_env.update(SIMPLE_BINARY='C:/stale/simple.exe',SIMPLE_BIN='C:/stale/another-simple.exe')
    n.owned('renamed',[sys.executable,str(runner),str(product),digest],262144,45,run_env)
    output=(n.OUT/'renamed.stdout').read_bytes().replace(b'\r\n',b'\n').decode('utf-8')
    lines=output.splitlines()
    assert len(lines)==2 and lines[0]=='windows-native-build-self-image assertions=7',output
    assert lines[1].startswith('kernel-image=')
    actual=P(lines[1].split('=',1)[1])
    assert os.path.samefile(actual,product) and n.sha(actual)==digest
    assert all(n.sha(n.OUT/p)==h for p,h in identities.items())
    assert all(n.sha(n.ROOT/p)==h for p,h in source_files.items())
    n.save('terminal.json',{'status':'NATIVE_RENAMED_IMAGE_PASS','assertions':7,'source':SOURCE,
        'compiler_source':n.SOURCE,'compiler_sha256':n.sha(compiler),'fixture_sha256':digest,
        'image':str(actual),'scope':'actual canonical kernel lookup and source wiring; not rebuilt native_build_main or Phase3 qualification'})

if __name__=='__main__':
    try:main()
    except BaseException as error:
        n.save('failure.json',{'error':str(error),'traceback':traceback.format_exc()});raise
