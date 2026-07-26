# Bug: bootstrap low-memory positional bridge is blocked by split pure-binary capabilities

Date: 2026-07-26  
Status: **BLOCKED — cycle 2 did not reach the requested bridge entry; source reverted**
Scope: current-main compiler promotion only; normal compilation must remain unchanged

## Intended behavior

The historical positional bootstrap path needs an explicit opt-in that makes
`CompileOptions.low_memory` true while building the current compiler:

```text
SIMPLE_BOOTSTRAP=1
SIMPLE_BOOTSTRAP_STAGE4=1
SIMPLE_BOOTSTRAP_LOW_MEMORY=1
```

The default remains false. The opt-in must never affect ordinary compilation,
non-Stage4 bootstrap work, or VHDL source retention. A focused live gate must
show the driver entering the post-phase-2 source-reclaim path and must execute
against a pure-built runtime capsule that exports the registry-checked
`rt_string_free`. Rust-seed fallback is forbidden.

## Exact circularity

No currently available **eligible** pure-built macOS/arm64 binary has both
capabilities needed by the live gate.

| Observed binary | SHA-256 | Eligibility | Current compiler imports | Native `rt_string_free` |
|---|---|---|---|---|
| `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple` | `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc` | **Forbidden seed**: its image contains `Rust-built` / `bootstrap seed only` classifiers | Compatible enough to load and diagnose the current probe/driver graph, but this diagnostic is not acceptance evidence | Absent from `nm` |
| `/Users/ormastes/simple/bin/release/macos-arm64/simple` | `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767` | **Eligible pure-built capsule** | Historical interpreter cannot resolve the current compiler imports | Present in `nm` |

Both files are regular, non-symlink Mach-O arm64 executables and report
`Simple v1.0.0-beta`, but that version string is insufficient provenance.
The forbidden classifier embedded in `f2c…` overrides its release-looking path
and version output. It must not compile, run, or attest any bridge artifact.
`277f…` is the only currently eligible pure-built capsule in this comparison.

The `277f…` capsule returns only:

```text
[STDERR] Error running test/02_integration/compiler/bootstrap_low_memory_phase2_reclaim_probe.spl
```

For diagnosis only, the forbidden `f2c…` seed reaches current source analysis,
then reports unresolved current-graph names including
`bootstrap_low_memory_requested`, `driver_core_compile_options_default`,
`CompileMode`, `compiler_driver_create`, `compiler_driver_run_compile`,
`compile_result_is_success`, and `compile_result_errors`. It cannot be used
for the final live call or any preparatory build. Its seed identity already
disqualifies it; its missing `rt_string_free` is an additional incompatibility.

This is a real bootstrap circularity, not permission to substitute
`src/compiler_rust/target/bootstrap/simple` or the seed disguised at the
`f2c…` release path. The only eligible pure-built capsule has the fresh runtime
primitive but cannot consume the current compiler graph.

## Cycle-1 evidence

Worktree/base used:

```text
/Users/ormastes/simple/build/worktrees/phase2-bootstrap-bridge
17bb2fa87bacb3538fe70b2a54b3e80e8073736b
```

The bounded gate exited `1` before any inner-driver reclaim marker:

```text
bootstrap_low_memory_gate_status=fail
bootstrap_low_memory_gate_reason=phase2-reclaim-positive-trace-missing
bootstrap_low_memory_gate_probe_exit=1
```

Evidence paths:

- `build/bootstrap_low_memory_phase2_reclaim_gate/evidence.env`
- `build/bootstrap_low_memory_phase2_reclaim_gate/exact-command.sh.txt`
- `build/bootstrap_low_memory_phase2_reclaim_gate/probe.stdout`
- `build/bootstrap_low_memory_phase2_reclaim_gate/probe.stderr`

Recorded unverified source hashes from that cycle:

- probe: `a103548e8ae6361f11d9ce13a217c56cf6050a6881b19c6bca3e7228b8fc2208`
- driver: `4a6325b9fea3213cd5a62bb3de268b745586f50529c29abffd49b7323141a276`
- bootstrap API: `53714a0086198317927cc7015ff0dbbd6151d0f442cd1c80bdc859a6f8d82104`
- bootstrap main: `232863c20fdedbc514bf90149b25bb8ee1d05d538f6f3d95996d2c4bfc8f08b4`

The source bridge, trace markers, probe, and wrapper remain working-tree-only.
They are not accepted implementation evidence and must not be folded into this
documentation commit.

## Cycle-2 evidence

Worktree/base used:

```text
/Users/ormastes/simple/build/worktrees/wm-bridge-micro-20260726
3b7a11b6cdf61ce2180886d6ae17fa0e1d9c8204
```

The sole eligible compiler was admitted before use:

```text
canonical_path=/Users/ormastes/simple/bin/release/macos-arm64/simple
sha256=277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767
file=Mach-O 64-bit executable arm64
regular_executable_non_symlink=pass
version_exit=0
version_stdout=Simple v1.0.0-beta
Rust-built=absent
bootstrap seed only=absent
seed compiler=absent
simple_seed=absent
rt_string_free_symbol=pass
```

One bounded attempt used one worker, an isolated cache, exact entry closure,
`SIMPLE_NO_STUB_FALLBACK=1`, and the pure `CompilerDriver` bridge entry. The
temporary entry contained no `rt_native_build` call:

```text
gtimeout -k 10s 600s env \
  SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_LIB=<worktree>/src \
  SIMPLE_NATIVE_FORCE_NO_STUBS=1 \
  /Users/ormastes/simple/bin/release/macos-arm64/simple native-build \
  --backend cranelift --threads 1 \
  --cache-dir <worktree>/build/wm_bridge_micro_20260726/bridge-cache \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/lib --entry-closure \
  --entry <worktree>/build/wm_bridge_micro_20260726/bridge_main.spl \
  --output <worktree>/build/wm_bridge_micro_20260726/bridge
```

The historical command dispatcher exited `1` immediately, produced no bridge,
and exposed only:

```text
[STDERR] Error running src/app/repl/main.spl
```

This is the first blocker. The requested `bridge_main.spl` was never entered,
so output admission, focused probe construction, and positive/negative controls
were correctly not attempted. Retained ignored evidence:

- `build/wm_bridge_micro_20260726/bridge-build.stdout`
  (`051bee39cd3034ae32a28d5aea8434bd2ef4ea97e5534b4c79c7aeb75b73ec4d`)
- `build/wm_bridge_micro_20260726/bridge-build.stderr`
  (`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`)
- temporary bridge source
  (`2ab24460e6a4962ea248eb67e55cf4ff63a6f30d7b75132c5278682fc2362b24`)
- temporary probe source
  (`16effe684f5b6df0be32d66836f1a3355b0c07d4cc254e969db19e055ca5c9c3`)

All three unverified product-source edits were reverted byte-for-byte. No
bridge, probe executable, Stage 4 build, fallback, delegate, or native runtime
claim survived this cycle. Exactly one bounded micro cycle remains.

## Next safe action

Use the one remaining bounded micro cycle to build only a focused
bridge/probe executable, not the full current compiler:

1. start from a clean linked worktree at the reviewed current-origin commit;
2. pin only the eligible `277f…` pure compiler and build a minimal
   historical-compatible bridge that stays within the imports and syntax that
   capsule can consume; never invoke `f2c…` as compiler, driver, delegate, or
   fallback;
3. prove the resulting bridge is non-seed before use: canonical regular-file
   path, exact SHA-256, bounded `--version`, rejection of `Rust-built`,
   `bootstrap seed only`, and other seed classifiers, plus `nm` proof of native
   `rt_string_free`;
4. use that admitted non-seed bridge to build only the focused current-graph
   probe with `SIMPLE_NO_STUB_FALLBACK=1`; record bridge/runtime paths and
   hashes, exact commands, bounded logs, output hash, and symbol proof;
5. execute the focused probe with all three bootstrap opt-in variables and
   require a positive
   `phase2:source_reclaim:done reclaimed=<n>` trace plus direct
   `rt_string_free` first-free `1` / alias-refusal `0`;
6. run the same focused executable with the opt-in absent and require
   low-memory false with no reclaim marker.

If `277f…` cannot produce a historical-compatible, classifier-clean bridge,
stop and retain this bug as the blocker. Do not use `f2c…` to escape that
failure. Only after the positive and negative micro controls pass may the
source bridge be committed and a separately authorized, bounded
current-compiler promotion be considered. Do not run full Stage4 to diagnose
this circularity.
