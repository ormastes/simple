# Windows SOSIX environment/cwd text admission rejects HIR worker startup

Canonical ID: `windows_sosix_utf8_environment_admission_2026_10_21`.
Status: scoped source repair; focused native verification recorded below;
canonical candidate rebuild and full bootstrap qualification remain pending.

The campaign source `10dc6c28447466fd6738e759e32d9737d360e138` compiled
1437 modules with zero failures, then its new Stage2 frontend sanity rejected
candidate SHA256
`c72ab722ea1ae171079f1b577302fabf041f10b616c791b6c2c72fa618999240`.
The worker printed `SOSIX ordinary UTF-8 host text provider unavailable: windows`
and aborted with Windows status `-1073740791` before claiming or sealing a
module. `driver_hir_cache.spl` reads shard environment variables through
`sosix_env_get_nullable`; that legacy adapter panics on the unconditional
Windows rejection in `sosix_require_posix_text_provider`. The runtime abort
accounts for the observed crash; no independent serialization defect is proved.

The repair adds a separate environment/cwd provider admission. It leaves the
generic POSIX-only admission used by other operations unchanged. C environment
lookup, mutation and removal now use explicit Windows W APIs with strict
UTF-8/UTF-16 conversion, retaining absent versus explicitly empty values. CRT
mutation remains synchronized, with the Win32 empty value restored after CRT's
empty-assignment deletion semantics. C cwd uses `GetCurrentDirectoryW` and
strict conversion rather than `GetCurrentDirectoryA` or a fabricated dot path.
The existing Rust environment owner already uses Unicode `std::env`; Rust cwd
now rejects a non-Unicode OS path instead of `to_string_lossy` replacement.
No charset is inferred, unavailable provider is substituted, or global Windows
platform gate relaxed.

The legacy nullable provider ABI still conflates an unset variable, allocation
failure, and invalid OS Unicode as NIL. The SOSIX nullable environment facade
cannot distinguish those outcomes; cwd reports its corresponding NIL as an I/O
failure. Raw Rust pointer-to-string helpers retain their existing lossy input
behavior. The checked SOSIX facade strictly validates UTF-8 and embedded NUL
before calling them; this repair does not claim that every raw legacy ABI input
is strict or that nullable lookup exposes a complete error taxonomy.

## Focused native evidence

Private branch `work/phase3-windows-utf8-provider-20261021`, worktree
`D:/dev/simple-phase3-windows-utf8-20261021`, based on
`5600e4de65b8e6fd2862c30f4a82a02d0b084c3a`.
All following artifacts are under its private `build/windows-utf8/` directory.
The campaign candidate, producer, runtime authority and writable caches were
preserved. Source commits precede consumption of their diagnostic artifacts.
The positive producer SHA256 was
`53c3b6783a25170093e74c4c96be316289d34b8a93c9e13795d2610f31cdcea0`.

- `negative-isolated.sh` copied the exact rejected candidate and recorded both
  matching hashes in `rejected-candidate-sha256.txt`. With a tiny committed Git
  project and no stdlib junction, actual `native-build` exited 1 with the same
  unsupported-provider message, worker abort, zero claimed/sealed modules and
  HIR aggregate failure. Retained `negative-tiny/negative-candidate.log` and
  private queue/cache. Earlier attempts blocked on missing tiny Git HEAD and
  then an unrelated full-stdlib workaround annotation; those are preserved
  separately and are not counted as reproduction evidence.
- `native-mixed.sh` used the campaign's frozen Rust producer and authority,
  canonical Windows MSVC setup, explicit tiny project stdlib junction pointing
  only to this private worktree, and the updated C supplement. It compiled
  48 modules, zero failures, linked 3299 KB, and exited zero with
  `PASS Windows SOSIX UTF-8 environment/cwd: 16 checks`. It covers checked
  missing/empty/Unicode key/value lifecycle, invalid keys, Unicode cwd, and the
  actual `SIMPLE_HIR_SHARD=0/1` startup value. Retained
  `tiny/mixed-build.log`, `tiny/run.stdout`, `tiny/run.stderr`, and objects
  `tiny/native-objects-Fw1YyD`.
- `raw.sh` compiled the direct C ABI fixture as one module, linked 279 KB, and
  exited zero with `PASS raw C Windows UTF-8 environment/cwd: 12 checks`.
  It independently covers C missing/empty/Unicode lifecycle and Unicode cwd.
  Retained `tiny/raw-build.log`, `tiny/raw-run.stdout`, `tiny/raw-run.stderr`,
  and objects `tiny/native-objects-6N2xve`. The initial C-only library-closure
  attempt was blocked by the existing Rust-only `rt_env_temp` dependency;
  that unrelated link failure remains in `tiny/junction-build.log`.
- `rust.sh` ran the actual native runtime integration target, with
  `--no-default-features --features hosted-webgpu-provider,native-all-provider
  --target x86_64-pc-windows-msvc --test windows_utf8_environment --
  --nocapture --test-threads=1`: one test passed. It checks Unicode environment
  lifecycle, Unicode cwd, and an actual filesystem directory containing an
  unpaired UTF-16 surrogate; `rt_env_cwd` returns NIL for that directory rather
  than replacing the invalid code unit. Retained `rust.log`. Cargo used two
  jobs and the same agent's private shell-provider target cache, with source
  fingerprints rebuilt; no campaign Cargo cache or producer was changed.

Both positive native commands use `--backend llvm --runtime-bundle
core-c-bootstrap --source src --entry-closure --threads 1 --mode one-binary
--target x86_64-pc-windows-msvc`, distinct private `--cache-dir` paths, and
`--runtime-path` pointing to the campaign's immutable Stage2 runtime authority.
The mixed entry is `src/bootstrap_main.spl` with `SIMPLE_BOOTSTRAP=1` and
`SIMPLE_NATIVE_BUILD_RUST=1`; the C entry is `src/raw.spl`. Execution cwd is the
private `tiny/환경-é` directory. These are bootstrap-focused native probes,
not a product-suite or self-hosted full-CLI qualification.
The unchanged rejected compiler cannot execute the repaired source internally;
a new full HIR worker admission remains a canonical rebuild criterion.

The final committed implementation ratchet against base `5600e4de65b8` passed:
10 selftests, 2623 versus 2623 single-lane names, zero new exceptions. Retained
`ratchet.log`. The working direct-environment source guard and diff whitespace
check passed. Existing frozen baseline drift remains informational, unchanged.

Provider token/cost accounting: unavailable, not guessed.
