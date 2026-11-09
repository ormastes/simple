"""Check actual bootstrap warning owners without building or using the seed product.

Runs existing owner unit tests on the host and checks Unix callbacks on Linux and
Darwin. Cargo uses the unchanged in-tree vendored libc; no network is needed.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
out = root / 'build/rust-warning-check'
(out / 'src').mkdir(parents=True, exist_ok=True)
quote = lambda path: json.dumps(str(path).replace('\\', '/'))
(out / 'Cargo.toml').write_text(
    '[package]\nname="bootstrap-warning-owner-check"\nversion="0.0.0"\nedition="2021"\n'
    '[workspace]\n[dependencies]\nlibc={path='
    + quote(root / 'src/compiler_rust/vendor/libc') + '}\n')
compiler = root / 'src/compiler_rust/compiler/src'
modules = []
for name, relative in [('sampler', 'interpreter/sampler.rs'),
                       ('perf_counters', 'perf_counters.rs'),
                       ('mem_guard', 'interpreter_extern/mem_guard.rs')]:
    modules.append(f'#[path = {quote(compiler / relative)}] mod {name};')
# Terminal's larger module depends on interpreter values. Compile its actual
# standalone handler and the exact installation assignment with libc instead.
terminal = (compiler / 'interpreter_extern/terminal.rs').read_text()
start = terminal.index('const RT_SIGNAL_MAX:')
end = terminal.index('/// `rt_signal_install', start)
modules.append(terminal[start:end].replace('#[cfg(unix)]\n', ''))
assignments = [line.strip() for line in terminal.splitlines() if 'sa.sa_sigaction =' in line]
if len(assignments) != 1:
    raise RuntimeError('terminal signal assignment owner changed; review fixture')
modules.append('''
#[test] fn terminal_callable_address_roundtrip() {
    let address = rt_signal_handler as *const () as usize;
    let callable: extern "C" fn(libc::c_int) = unsafe { std::mem::transmute(address) };
    callable(7);
    assert!(RT_SIGNAL_FLAGS[7].swap(false, std::sync::atomic::Ordering::SeqCst));
    callable(-1); callable(32);
}
#[cfg(unix)] fn terminal_assignment_typechecks() {
    let mut sa: libc::sigaction = unsafe { std::mem::zeroed() };
''' + assignments[0] + '''
    assert_eq!(sa.sa_sigaction, rt_signal_handler as *const () as usize);
}
''')
(out / 'src/lib.rs').write_text('\n'.join(modules))
env = os.environ.copy()
env['RUSTFLAGS'] = env.get('RUSTFLAGS', '') + ' -Dfunction_casts_as_integer'
commands = [('host-tests', ['test', '--', '--test-threads=1'])]
commands += [(target, ['check', '--target', target]) for target in
             ('x86_64-unknown-linux-gnu', 'aarch64-apple-darwin')]
for label, arguments in commands:
    mode, *rest = arguments
    command = ['cargo', mode, '--offline', '--manifest-path', str(out / 'Cargo.toml'), *rest]
    log = out / (label + '.log')
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    print(f'{label}: {"PASS" if result.returncode == 0 else "FAIL"}; {log}')
    if result.returncode:
        sys.exit(result.returncode)
