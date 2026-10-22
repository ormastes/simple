#!/usr/bin/env python3
"""Small real-tool counterexamples; NOT an implementation of Simple's cache."""
from __future__ import annotations
import json, os, pathlib, shutil, subprocess, sys, tempfile
from typing import Callable

OUT = pathlib.Path(__file__).resolve().parent
CLANG = shutil.which('clang')
CMAKE = shutil.which('cmake')
NINJA = shutil.which('ninja')
if not all((CLANG, CMAKE, NINJA)):
    raise SystemExit('Requires clang, cmake, ninja and Python 3; no packages are installed.')
results: list[dict] = []
commands: list[dict] = []
root: pathlib.Path

def cmd(args: list[str], *, stdin: str | None = None, cwd: pathlib.Path | None = None):
    p = subprocess.run(args, input=stdin, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, cwd=cwd or root, timeout=45)
    commands.append({'argv': args, 'returncode': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr})
    return p

def put(name: str, text: str) -> pathlib.Path:
    p = root / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
    return p

def pp(text: str, *flags: str) -> str:
    p = cmd([CLANG, '-E', '-P', '-x', 'c', *flags, '-'], stdin=text)
    assert p.returncode == 0, p.stderr
    return p.stdout.strip()

def case(id: str, title: str, fn: Callable[[], str]):
    start = len(commands)
    try:
        detail = fn(); status = 'PASS'
    except Exception as e:
        detail = f'{type(e).__name__}: {e}'; status = 'FAIL'
    results.append({'id': id, 'title': title, 'status': status, 'detail': detail,
                    'commands': commands[start:]})

with tempfile.TemporaryDirectory(prefix='simple-header-probes-') as tmp:
    root = pathlib.Path(tmp)
    versions = {name: cmd([exe, '--version']).stdout.strip() for name, exe in
                [('clang', CLANG), ('cmake', CMAKE), ('ninja', NINJA)]}
    commands.clear()

    def macro_states():
        text = '#define STR1(x) #x\n#define STR(x) STR1(x)\n#ifdef MODE\nint defined_flag=1;\nconst char *replacement=STR(MODE);\n#else\nint defined_flag=0;\n#endif\n'
        outs = [pp(text, *f) for f in [(), ('-DMODE=0',), ('-DMODE=',), ('-DMODE',)]]
        assert len(set(outs)) == 4
        return 'Undefined, defined-as-0, defined-empty, and -DMODE (1) produced four distinct results.'
    case('P01', 'Macro definition states are distinct', macro_states)

    def negative_macro():
        a, b = pp('int FIELD_NAME;\n'), pp('int FIELD_NAME;\n', '-DFIELD_NAME=renamed')
        assert a == 'int FIELD_NAME;' and b == 'int renamed;'
        return 'An ordinary identifier with no original expansion becomes a macro use after a new definition.'
    case('P02', 'Previously unexpanded identifier changes', negative_macro)

    def flag_order():
        t = '#ifdef MODE\nint enabled=1;\n#else\nint enabled=0;\n#endif\n'
        a, b = pp(t, '-DMODE=1', '-UMODE'), pp(t, '-UMODE', '-DMODE=1')
        assert a != b and 'enabled=0' in a and 'enabled=1' in b
        return 'Reversing -D/-U changed preprocessing; argv ordering cannot be sorted away.'
    case('P03', 'Ordered command-line macro actions', flag_order)

    def negative_include():
        inc = root / 'optional'; inc.mkdir()
        src = put('optional.c', '#if __has_include("optional.h")\n#include "optional.h"\n#else\nint selected=0;\n#endif\n')
        before = cmd([CLANG, '-E', '-P', '-I', str(inc), str(src)])
        dep = cmd([CLANG, '-M', '-I', str(inc), str(src)])
        put('optional/optional.h', 'int selected=1;\n')
        after = cmd([CLANG, '-E', '-P', '-I', str(inc), str(src)])
        assert all(p.returncode == 0 for p in (before, dep, after))
        assert 'selected=0' in before.stdout and 'selected=1' in after.stdout
        assert 'optional.h' not in dep.stdout
        return 'An absent header did not appear in the ordinary dependency list; creating it changed output.'
    case('P04', 'Negative include dependency', negative_include)

    def search_order():
        put('inc_a/pick.h', 'int chosen=1;\n'); put('inc_b/pick.h', 'int chosen=2;\n')
        t = '#include <pick.h>\n'
        a = pp(t, '-I'+str(root/'inc_a'), '-I'+str(root/'inc_b'))
        b = pp(t, '-I'+str(root/'inc_b'), '-I'+str(root/'inc_a'))
        assert a != b
        return 'The same include spelling selected different content when include search order changed.'
    case('P05', 'Include-search order is semantic', search_order)

    def xmacro():
        put('rows.inc', 'ROW(alpha, 1)\nROW(beta, 2)\n')
        t = '#define ROW(n,v) int n=v;\n#include "rows.inc"\n#undef ROW\n#define ROW(n,v) int get_##n(void){return v;}\n#include "rows.inc"\n'
        out = pp(t, '-I'+str(root))
        assert 'int alpha=1;' in out and 'int get_alpha(void){return 1;}' in out
        return 'One header was intentionally processed twice under different function-like macro definitions.'
    case('P06', 'Repeated X-macro include', xmacro)

    def packing():
        put('layout.h', 'struct S { char c; int value; };\n')
        for pack, expect in [(False,8),(True,5)]:
            t = ('#pragma pack(push,1)\n' if pack else '') + '#include "layout.h"\n'
            t += ('#pragma pack(pop)\n' if pack else '') + f'_Static_assert(sizeof(struct S)=={expect}, "size");\n'
            p=cmd([CLANG, '-fsyntax-only', '-x', 'c', '-I'+str(root), '-'], stdin=t)
            assert p.returncode == 0, p.stderr
        return 'On this x86_64 toolchain, identical header bytes yielded size 8 or 5 under different pragma state.'
    case('P07', 'Non-macro pragma state changes layout', packing)

    def semantic_context():
        put('context.h', 'struct Cell { element_t value; };\n')
        for ty, size in [('char',1),('long long',8)]:
            t = f'typedef {ty} element_t;\n#include "context.h"\n_Static_assert(sizeof(struct Cell)=={size}, "size");\n'
            p=cmd([CLANG, '-fsyntax-only', '-x', 'c', '-I'+str(root), '-'], stdin=t)
            assert p.returncode == 0, p.stderr
        return 'The unchanged header and macro configuration still depended on a preceding typedef; header AST reuse needs semantic context.'
    case('P08', 'Textual header semantic context', semantic_context)

    def counter():
        put('counter.h', 'int header_counter=__COUNTER__;\n')
        a=pp('#include "counter.h"\n', '-I'+str(root))
        b=pp('int prior=__COUNTER__;\n#include "counter.h"\n', '-I'+str(root))
        assert 'header_counter=0' in a and 'header_counter=1' in b
        return '__COUNTER__ reflected incoming preprocessing state, not just macro replacement text.'
    case('P09', 'Stateful builtin counter', counter)

    def pch_mismatch():
        hdr=put('pch/config.h', 'static const int mode_value=MODE;\n')
        artifact=root/'pch/config.pch'
        a=cmd([CLANG,'-x','c-header','-DMODE=1',str(hdr),'-o',str(artifact)])
        assert a.returncode==0, a.stderr
        src=put('pch/use.c','int get_mode(void) { return mode_value; }\n')
        good=cmd([CLANG,'-fsyntax-only','-DMODE=1','-include-pch',str(artifact),str(src)])
        bad=cmd([CLANG,'-fsyntax-only','-DMODE=2','-include-pch',str(artifact),str(src)])
        assert good.returncode==0 and bad.returncode!=0
        assert 'MODE' in bad.stderr
        return 'Clang accepted matching PCH macro settings and rejected MODE=2 against a MODE=1 PCH.'
    case('P10', 'Native PCH mismatch validation', pch_mismatch)

    def cmake_launcher():
        src=root/'cmproj'; bld=root/'cmbuild'; src.mkdir(); bld.mkdir()
        put('cmproj/main.c', '#include "generated.h"\nint main(void) { return PROJECT_VALUE == 7 && GENERATED_VALUE == 2 ? 0 : 1; }\n')
        put('cmproj/header.in', '#define GENERATED_VALUE 2\n')
        policy=put('cmproj/header-policy.sdn', '# opaque fixture, not parsed\nrevision: 1\n')
        launch=put('cmproj/launcher.py', '''import json, pathlib, subprocess, sys\np=pathlib.Path(__file__).with_name("launcher.log")\nwith p.open("a") as f: f.write(json.dumps(sys.argv[1:])+"\\n")\nsys.exit(subprocess.call(sys.argv[1:]))\n''')
        put('cmproj/CMakeLists.txt', '''cmake_minimum_required(VERSION 3.20)\nproject(SimpleLauncherProbe LANGUAGES C)\noption(POLICY_DEP "Depend on policy" OFF)\nadd_custom_command(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/generated.h"\n COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_SOURCE_DIR}/header.in" "${CMAKE_CURRENT_BINARY_DIR}/generated.h"\n DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/header.in" VERBATIM)\nadd_executable(probe main.c "${CMAKE_CURRENT_BINARY_DIR}/generated.h")\ntarget_include_directories(probe PRIVATE "${CMAKE_CURRENT_BINARY_DIR}")\ntarget_compile_definitions(probe PRIVATE PROJECT_VALUE=7)\nif(POLICY_DEP)\n set_property(SOURCE main.c APPEND PROPERTY OBJECT_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/header-policy.sdn")\nendif()\n''')
        q=bld/'.cmake/api/v1/query'; q.mkdir(parents=True); (q/'codemodel-v2').touch()
        launch_arg=f'{sys.executable};{launch}'
        p=cmd([CMAKE,'-S',str(src),'-B',str(bld),'-G','Ninja',f'-DCMAKE_C_COMPILER={CLANG}',f'-DCMAKE_C_COMPILER_LAUNCHER={launch_arg}','-DCMAKE_EXPORT_COMPILE_COMMANDS=ON'])
        assert p.returncode==0,p.stderr
        p=cmd([CMAKE,'--build',str(bld)]); assert p.returncode==0,p.stderr
        assert cmd([str(bld/'probe')]).returncode==0
        log=src/'launcher.log'
        def count(): return len(log.read_text().splitlines())
        initial=count(); assert initial>=1
        p=cmd([CMAKE,'--build',str(bld)]); assert p.returncode==0 and count()==initial
        policy.write_text('# changed policy\nrevision: 2\n')
        p=cmd([CMAKE,'--build',str(bld)]); assert p.returncode==0 and count()==initial
        reply=list((bld/'.cmake/api/v1/reply').glob('target-probe-*.json')); assert reply
        obj=json.loads(reply[0].read_text())
        defs=[d['define'] for g in obj.get('compileGroups',[]) for d in g.get('defines',[])]
        assert 'PROJECT_VALUE=7' in defs
        assert (bld/'compile_commands.json').exists()
        return 'Launcher and File API worked; Ninja did not invoke the launcher on an unchanged build or an undeclared policy-only edit.'
    case('P11', 'CMake launcher integration and policy skip hole', cmake_launcher)

    def policy_dep():
        src=root/'cmproj'; bld=root/'cmbuild'
        log=src/'launcher.log'
        p=cmd([CMAKE,'-S',str(src),'-B',str(bld),'-DPOLICY_DEP=ON']); assert p.returncode==0
        p=cmd([CMAKE,'--build',str(bld)]); assert p.returncode==0
        initial=len(log.read_text().splitlines())
        policy=src/'header-policy.sdn'; policy.write_text('# explicitly declared policy dependency\nrevision: 3\n')
        p=cmd([CMAKE,'--build',str(bld)]); assert p.returncode==0
        assert len(log.read_text().splitlines())>initial
        return 'Adding the registry with OBJECT_DEPENDS made the policy edit trigger another compilation through the launcher.'
    case('P12', 'Explicit policy dependency closes launcher skip hole', policy_dep)

    report={'scope':'Counterexample probes only; no Simple cache/provider implementation was tested.',
            'versions':versions,'results':results}
    serialized=json.dumps(report,indent=2).replace(str(root),'<WORK>')
    (OUT/'probe_results.json').write_text(serialized)
    rows=['# Local counterexample probe results','',report['scope'],'',
          'Executed in this conversation on 2026-09-25. This is not a performance benchmark or a cache soundness proof.','',
          '## Toolchain','']
    for name, version in versions.items(): rows += [f'### {name}','```text',version,'```','']
    rows+=['## Results','','| ID | Probe | Outcome | Observation |','|---|---|---|---|']
    for r in results: rows.append(f"| {r['id']} | {r['title']} | {r['status']} | {r['detail']} |")
    rows+=['','## Reproduce','','Run `python3 evidence/run_probes.py` with clang, CMake, and Ninja on PATH. The script uses a temporary directory, removes generated binaries, and writes its own results beside itself. The fixed layout checks are specific to the observed x86_64 ABI.','',
           'The machine-readable log is `probe_results.json`; full fixture source is in `run_probes.py`. The policy file in the launcher fixture is intentionally opaque text, not a validation of the proposed SDN schema.','']
    (OUT/'probe_results.md').write_text('\n'.join(rows))
print('\n'.join(f"{r['id']} {r['status']}: {r['title']}" for r in results))
raise SystemExit(0 if all(r['status']=='PASS' for r in results) else 1)
