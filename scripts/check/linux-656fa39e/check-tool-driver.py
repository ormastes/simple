"""Actual Linux LLVM symlink/argv[0] proof, no compiler workload."""
import importlib.util,json,pathlib,shutil,subprocess,sys
p=pathlib.Path(__file__).with_name('control.py')
s=importlib.util.spec_from_file_location('control',p);c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
out=pathlib.Path('tool-driver-evidence');out.mkdir(exist_ok=False)
assert sys.platform=='linux'
invoked=pathlib.Path(shutil.which('ld.lld')).absolute();resolved=invoked.resolve()
assert invoked!=resolved and resolved.name.startswith('lld'),(invoked,resolved)
old=subprocess.run([str(resolved),'--version'],capture_output=True,text=True,timeout=30)
c.save(out/'baseline.json',{'argv':[str(resolved),'--version'],'exit':old.returncode,'stdout':old.stdout,'stderr':old.stderr})
assert old.returncode!=0 and 'generic driver' in old.stderr
c.tools_snapshot(out)
records=json.loads((out/'tool-invocations.json').read_text())
assert records['ld.lld']=={'invoked':str(invoked),'resolved':str(resolved),'sha256':c.sha(resolved)}
assert 'LLD' in (out/'ld.lld.version').read_text()
c.save(out/'terminal.json',{'status':'PASS','scope':'actual Linux symlink and production tools_snapshot; no native build'})
