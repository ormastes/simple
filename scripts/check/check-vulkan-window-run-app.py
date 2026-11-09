"""Exercise the actual Vulkan window callback adapter with hidden native winit.

Windows only. No Vulkan device, surface, FFI substitute or visible UI is used.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib

parser = argparse.ArgumentParser()
parser.add_argument('--vendor-dir', type=Path, help='unchanged Cargo vendor directory; defaults to repo vendor')
parser.add_argument('--base', help='optional revision for original callback/converter equivalence')
parser.add_argument('--tokens-only', action='store_true', help='check callback tokens without running a native window')
args = parser.parse_args()
if args.tokens_only and not args.base:
    parser.error('--tokens-only requires --base')
if sys.platform != 'win32' and not args.tokens_only:
    raise SystemExit('This hidden native-loop regression requires Windows.')
root = Path(__file__).resolve().parents[2]
source_path = 'src/compiler_rust/runtime/src/vulkan/window.rs'
source = (root / source_path).read_text()
winit = root / 'src/compiler_rust/vendor/winit'


def between(text, start, end):
    return text.split(start, 1)[1].split(end, 1)[0]


out = root / 'build/winit-window-check'
(out / 'src').mkdir(parents=True, exist_ok=True)
(out / '.cargo').mkdir(exist_ok=True)
quote = lambda path: json.dumps(str(path).replace('\\', '/'))
(out / '.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendored-sources"\n[source.vendored-sources]\ndirectory=' + quote((args.vendor_dir or root / 'src/compiler_rust/vendor').resolve()) + '\n')
if args.base:
    old = subprocess.check_output(['git', 'show', f'{args.base}:{source_path}'], cwd=root).decode()
    token_dir = out / 'callback-tokens'
    (token_dir / 'src').mkdir(parents=True, exist_ok=True)
    (token_dir / 'Cargo.toml').write_text('[package]\nname="winit-callback-tokens"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\nproc-macro2="1"\n')
    (token_dir / 'src/main.rs').write_bytes((root / 'scripts/check/fixtures/winit-callback-tokens.rs').read_bytes())
    (token_dir / 'before.rs').write_text(old)
    log = token_dir / 'token-check.log'
    with log.open('w') as stream:
        result = subprocess.run(['cargo', 'run', '--offline', '--', 'before.rs', str(root / source_path)],
                                cwd=token_dir, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
    print(f'{"PASS" if result.returncode == 0 else "FAIL"} complete callback token check: {log}')
    if result.returncode:
        sys.exit(result.returncode)
    assert between(old, '    fn convert_window_event(', '    /// Create a window (sends request') == between(source, '    fn convert_window_event(', '    /// Create a window (sends request')
if args.tokens_only:
    sys.exit(0)
assert tomllib.loads((winit / 'Cargo.toml').read_text())['package']['version'] == '0.30.12'
assert 'let _ = event_loop.run_app(&mut WindowEventHandler(' in source
(out / 'Cargo.toml').write_text('[package]\nname="winit-window-owner-check"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\nwinit={path=' + quote(winit) + ',default-features=false,features=["rwh_06","x11"]}\n')
adapter = 'struct WindowEventHandler<' + between(source, 'struct WindowEventHandler<', '/// Window handle type')
events = '/// Window handle type' + between(source, '/// Window handle type', '/// Fullscreen mode')
converter = '    fn convert_window_event(' + between(source, '    fn convert_window_event(', '    /// Create a window (sends request')
(out / 'src/owner.rs').write_text(adapter + events + converter)
(out / 'src/main.rs').write_bytes((root / 'scripts/check/fixtures/winit-window-run-app.rs').read_bytes())
env = os.environ.copy()
env['RUSTFLAGS'] = env.get('RUSTFLAGS', '') + ' -Ddeprecated'
log = out / 'owner-check.log'
with log.open('w') as stream:
    result = subprocess.run(['cargo', 'run', '--offline', '--manifest-path', 'Cargo.toml'], cwd=out,
                            env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
print(f'{"PASS" if result.returncode == 0 else "FAIL"} hidden native-window adapter; evidence: {log}')
sys.exit(result.returncode)
