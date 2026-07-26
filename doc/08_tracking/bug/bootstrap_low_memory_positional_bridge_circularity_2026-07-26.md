# Bug: bootstrap low-memory positional bridge is blocked by split pure-binary capabilities

Date: 2026-07-26  
Status: **BLOCKED — source bridge unverified and intentionally uncommitted**  
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

## Next safe action

Use one of the two remaining bounded micro cycles to build only a focused
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
