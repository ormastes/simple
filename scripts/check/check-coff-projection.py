"""Verify actual GNU tool selection and COFF projection on retained objects."""
import argparse
import hashlib
import json
import pathlib
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--retained', type=pathlib.Path, required=True)
p.add_argument('--cc', required=True)
p.add_argument('--out', type=pathlib.Path, required=True)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=False)
owner = pathlib.Path('src/compiler_rust/compiler/src/pipeline/native_project/coff_partial_link.rs').resolve()
projection = owner.with_name('coff_weak_projection.rs')
def run(argv, label, success=True):
    r = subprocess.run([str(x) for x in argv], capture_output=True, timeout=60)
    (a.out/(label+'.stdout')).write_bytes(r.stdout)
    (a.out/(label+'.stderr')).write_bytes(r.stderr)
    assert (r.returncode == 0) == success, (label, r.returncode, r.stderr.decode(errors='replace'))
    return r.stdout.decode()
harness = a.out/'selector.rs'
harness.write_text('#[path='+json.dumps(str(owner))+'] mod owner;\n#[path='+json.dumps(str(projection))+'] mod projection;\nfn main() { let args: Vec<String> = std::env::args().collect(); if args.len() > 1 { projection::project(std::path::Path::new(&args[1]), &args[2..].iter().cloned().collect()).expect("COFF weak projection"); return; } for kind in ["objcopy", "nm"] { println!("{}", owner::gnu_tool(&[&format!("x86_64-w64-mingw32-{kind}"), kind], kind).expect("real GNU tool")); } }\n', encoding='utf-8')
run(['rustc', '--edition=2021', harness, '-o', a.out/'selector'], 'build-selector')
tools = run([a.out/'selector'], 'selected-tools').splitlines()
objcopy, nm = tools
assert 'GNU objcopy ' in run([objcopy, '--version'], 'objcopy-version')
assert 'GNU nm ' in run([nm, '--version'], 'nm-version')
# The compatibility alias is the real earlier-on-PATH tool, not a mocked banner.
alias = run(['x86_64-w64-mingw32-objcopy', '--version'], 'alias-version')
assert alias.startswith('llvm-objcopy, compatible with GNU objcopy')
localize = a.out/'localize.syms'
weaken = a.out/'weaken.syms'
localize.write_text('dependency\n', encoding='utf-8')
weaken.write_text('fixture_root\n', encoding='utf-8')
source = a.retained/'closure.o'
args = ['--localize-symbols='+str(localize), '--weaken-symbols='+str(weaken), '--remove-section=.ctors']
run(['x86_64-w64-mingw32-objcopy', *args, source, a.out/'rejected.o'], 'old-alias', False)
projected = a.out/'projected.o'
run([objcopy, args[0], args[2], source, projected], 'localization')
run([a.out/'selector', projected, 'fixture_root'], 'weak-projection')
symbols = run([nm, '-g', projected], 'global-symbols')
assert 'dependency' not in symbols
assert any(' w fixture_root' in row or ' W fixture_root' in row for row in symbols.splitlines()), symbols
run([a.cc, '-fuse-ld=lld', '--rtlib=compiler-rt', '--unwindlib=libunwind', a.retained/'main.o', projected, '-o', a.out/'projected.exe'], 'final-pe')
internal = a.out/'internal.o'
internal.write_bytes(source.read_bytes())
run([a.out/'selector', internal, 'dependency'], 'internal-weak-projection')
run([a.cc, '-fuse-ld=lld', '--rtlib=compiler-rt', '--unwindlib=libunwind', a.retained/'main.o', internal, '-o', a.out/'internal-fallback.exe'], 'internal-fallback-pe')
for symbol, expected, obj in [('fixture_root', 99, projected), ('dependency', 100, internal)]:
    provider = a.out/(symbol+'-owner.c')
    provider.write_text('extern int fixture_root(void); int '+symbol+'(void) { return 99; } int main(void) { return fixture_root() == '+str(expected)+' ? 0 : 1; }\n',encoding='utf-8')
    run([a.cc, '-fuse-ld=lld', '--rtlib=compiler-rt', '--unwindlib=libunwind', provider, obj, '-o', a.out/(symbol+'-override.exe')], symbol+'-override-pe')
inputs = [owner, projection, source, a.retained/'main.o']
(a.out/'result.json').write_text(json.dumps(dict(checks=['actual GNU owner bypasses LLVM alias','old alias refuses projection','private dependency localized','root weak','pinned Clang LLD final PE','internal fallback PE','public and internal strong-owner PE'], inputs={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in inputs}, qualification='retained COFF projection and PE link; execution requires Windows job'),indent=2),encoding='utf-8')
