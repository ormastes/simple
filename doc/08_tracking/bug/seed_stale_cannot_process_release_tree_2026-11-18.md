# Seed compiler (v1.0.0-rc.1, Oct 24) cannot process the current release/1.0.0 tree

Date: 2026-11-18
Host: Windows 11, x86_64-pc-windows-msvc
Lane: devhub/caret-suite build + verify on release/1.0.0 (work/devhub-caret-seed-20261118)
Seed: `src/compiler_rust/target/bootstrap/simple.exe` (Rust-built, 17.9 MB,
aggregate fingerprint `268d8e99aa48…`, frozen 2026-10-24)

## Observation

Requested lane work was "build devhub and caret suite with seed". The frozen
seed fails on current release/1.0.0 sources in TWO independent ways, depending
on mode — both fatal, neither suppressible:

1. `native-build` (any entry; verified with devhub, caret, cs entries):
   frontend hard error ×32:

   ```
   error: Common mistake detected: Use 'mod' instead of 'namespace'
     --> src/lib/common/io/read_only_file_view.spl   (18 hits)
     --> src/compiler/50.mir/loop_module_shape_owner_v1.spl
     --> src/compiler/80.driver/cache/route_capability_scope_v1.spl
     --> src/compiler/00.common/cache_contract/macro_reference_manifest_v1.spl
     --> ... (devhub's entry closure reaches file I/O, hence read_only_file_view)
   ```

   The current language allows `namespace` as a struct field name; the seed's
   "common mistake" heuristic still treats the bare identifier as the removed
   keyword. No env knob disables it (enumerated `SIMPLE_*` strings in the seed
   binary: only `SIMPLE_ALLOW_DEPRECATED`, `SIMPLE_ALLOW_UNRESOLVED_IMPORTS`,
   `SIMPLE_ALLOW_*_STUBS`, `SIMPLE_DIAG_*` — nothing for this lint).

2. `test --mode=interpreter` (verified with
   `test/01_unit/app/devhub/backend_resolve_spec.spl` on the release/1.0.0
   worktree):

   ```
   error: semantic: unknown extern function: GetProcessHeap
   ```

   The seed's extern registry predates the Windows Heap-API externs current
   `src/lib` code requires.

## Root cause

The seed is frozen (2026-10-24) and by design "bootstrap-only". The language
surface and the platform extern set have moved on. This is the documented
posture (`.claude/rules/bootstrap.md`): the seed exists to build generation 1;
normal tooling is the pure-Simple self-hosted binary. Attempting to run app
builds or suites through the seed is out of contract — the failures above are
the seed enforcing its own staleness, not tree regressions (the same sources
build and test green under the stage-2 self-hosted compiler, see the lane
evidence `.build/native/*.build3.log`).

## Decision (lane, 2026-11-18)

- No source churn to suit the seed (renaming `namespace` fields repo-wide
  would be a workaround normalizer, explicitly barred).
- devhub/caret/cs native builds + suite verification for this lane run on the
  stage-2 self-hosted compiler
  (`…/pinned-917cf33bdd6e/build/bootstrap/c41s2/stage2/x86_64-pc-windows-msvc/simple.exe`),
  per the default-tooling rule.
- This doc records the concrete blocker so "with seed" requests can be
  evaluated against evidence instead of retried.
