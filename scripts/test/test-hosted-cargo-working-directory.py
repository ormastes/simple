#!/usr/bin/env python3
"""Exercise the production hosted archive command with real, dependency-free Cargo."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def run(args, **kwargs):
    return subprocess.run(args, text=True, capture_output=True, timeout=60, **kwargs)


def main():
    if sys.platform != 'linux':
        print('UNSUPPORTED: hosted Cargo archive regression requires Linux')
        return 77
    root = Path(__file__).resolve().parents[2]
    source = (root / 'src/compiler_rust/compiler/src/pipeline/native_project/config.rs').read_text()
    start = source.index('fn build_bootstrap_hosted_native_all_archive(')
    end = source.index('\nfn runtime_path_has_abi_complete_simple_core', start)
    function = source[start:end]
    with tempfile.TemporaryDirectory(prefix='hosted-cargo-cwd-') as directory:
        work = Path(directory)
        repo = work / 'repo'
        manifest_dir = repo / 'src/compiler_rust'
        (repo / 'src/runtime').mkdir(parents=True)
        (manifest_dir / '.cargo').mkdir(parents=True)
        (manifest_dir / 'src').mkdir()
        (manifest_dir / 'Cargo.toml').write_text(
            '[package]\nname="simple-native-all"\nversion="0.0.0"\nedition="2021"\n'
            '[lib]\ncrate-type=["staticlib"]\n[workspace]\n')
        (manifest_dir / 'src/lib.rs').write_text('pub fn local_fixture() {}\n')
        (manifest_dir / 'build.rs').write_text(
            'fn main() { assert_eq!(std::env::var("HOSTED_CONFIG_PROBE").as_deref(), Ok("nested")); }\n')
        config = manifest_dir / '.cargo/config.toml'
        config.write_text('[env]\nHOSTED_CONFIG_PROBE={value="nested",force=true}\n')
        harness = work / 'owner.rs'
        harness.write_text('use std::path::{Path, PathBuf};\n'
            'fn find_core_c_runtime_source_root() -> Option<PathBuf> {\n'
            'Some(PathBuf::from(std::env::var_os("PROBE_REPO")?).join("src/runtime")) }\n'
            + function + '\nfn main() {\n'
            'let out = PathBuf::from(std::env::var_os("PROBE_OUT").unwrap());\n'
            'let result = build_bootstrap_hosted_native_all_archive("libsimple_native_all.a", &out);\n'
            'if result.is_none() { std::process::exit(1); }\n}\n')
        env = dict(os.environ, PROBE_REPO=str(repo), CARGO_HOME=str(work / 'cargo-home'),
                   CARGO_NET_OFFLINE='true')
        env.pop('HOSTED_CONFIG_PROBE', None)
        binary = work / 'owner'
        compiled = run(['rustc', str(harness), '-o', str(binary)], env=env)
        assert compiled.returncode == 0, compiled.stderr
        # Prove this fixture detects the previous command, without changing repository source.
        baseline = work / 'baseline.rs'
        baseline.write_text(harness.read_text().replace('.current_dir(manifest.parent()?)', ''))
        baseline_binary = work / 'baseline'
        compiled = run(['rustc', str(baseline), '-o', str(baseline_binary)], env=env)
        assert compiled.returncode == 0, compiled.stderr
        env['PROBE_OUT'] = str(work / 'baseline-output')
        old = run([str(baseline_binary)], cwd=repo, env=env)
        assert old.returncode == 1 and 'assertion' in old.stderr, old.stderr
        # Invoke from the outer repository, exactly where --manifest-path alone fails.
        env['PROBE_OUT'] = str(work / 'positive')
        positive = run([str(binary)], cwd=repo, env=env)
        assert positive.returncode == 0, positive.stderr
        assert (work / 'positive/hosted_native_all/release/libsimple_native_all.a').is_file()
        env['PROBE_OUT'] = 'relative-output'
        relative = run([str(binary)], cwd=repo, env=env)
        assert relative.returncode == 0, relative.stderr
        assert (repo / 'relative-output/hosted_native_all/release/libsimple_native_all.a').is_file()
        assert not (manifest_dir / 'relative-output').exists()
        # A genuine config/build failure must still propagate as None, never success.
        config.write_text('[env]\nHOSTED_CONFIG_PROBE={value="wrong",force=true}\n')
        env['PROBE_OUT'] = str(work / 'negative')
        negative = run([str(binary)], cwd=repo, env=env)
        assert negative.returncode == 1, negative.stderr
        assert 'assertion' in negative.stderr, negative.stderr
        assert not (work / 'negative/hosted_native_all/release/libsimple_native_all.a').exists()
    print('PASS hosted Cargo: nested config loaded from outer cwd; build failure retained')


if __name__ == '__main__':
    sys.exit(main())
