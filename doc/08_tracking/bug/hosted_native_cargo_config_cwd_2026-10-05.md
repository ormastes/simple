# Hosted native archive Cargo configuration discovery

The bootstrap `build_bootstrap_hosted_native_all_archive` owner passed an
absolute Cargo manifest but inherited the compiler process working directory.
Cargo discovers `.cargo/config.toml` from its working directory, so launching
from the repository root omitted `src/compiler_rust/.cargo/config.toml`.
The repair sets the child working directory to the manifest directory. Build
arguments, dependencies, archive validation and failure-to-None behavior remain
unchanged. Relative target directories are first resolved against the parent
process working directory without requiring the output to exist. Review caught
and reproduced the otherwise introduced bug: Cargo succeeded under the nested
directory while the parent looked for the archive under the outer directory.

The original frozen-repository offline metadata comparison is retained at
`/var/tmp/item5-hosted-cargo-cwd-20261005`: `result.txt` records root cwd exit101
and manifest-directory cwd exit0; `root.err` retains the missing crates.io
`diff` diagnostic. This isolates configuration discovery without treating the
later hosted runtime fallback as successful qualification.

Actual focused regression passed on Linux using:

```sh
python3 scripts/test/test-hosted-cargo-working-directory.py
```

The test extracts and compiles the actual production function with a source-root
fixture, then invokes real offline Cargo on a dependency-free local staticlib.
The original command fails its build-script assertion because nested config is
missing; the repaired command creates the requested archive from an outer cwd;
a caller-relative output remains under the outer directory, and a deliberately
incorrect configuration still returns failure and produces no archive. The
regression is Linux-only (other hosts exit77 unsupported), using the actual
Linux archive filename. All outputs and Cargo storage are private temporary directories. No
seed rebuild, dependency changes, full hosted runtime build or Phase2/application
qualification is claimed.
