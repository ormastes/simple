# Coverage `<entry>` placeholder fix — A/B probe verification, 2026-08-08

Fix: `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`,
`register_definitions()`, `Node::Impl` branch — see
`doc/08_tracking/bug/coverage_entry_placeholder_two_root_causes_2026-08-08.md`
for the full root-cause writeup (two causes; B collapses into A).

## Build

`cargo build --release` from `src/compiler_rust/`, incremental (reused prior
`target/release` — not a `cargo clean`), 2m56s, no errors (12 pre-existing
warnings unrelated to this change, all present before the edit). Disk: 219G
free before, no ENOSPC risk (floor is 120G).

Binary under test: `src/compiler_rust/target/release/simple` (NOT deployed to
`bin/simple` — this session only builds/verifies, per instructions; the
deployed `bin/simple` is unchanged and remains the pre-fix Rust seed).

## A/B probe: `engine2d_baremetal_core_spec.spl`

Same command both sides:
```
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path>.sdn <binary> run \
  src/app/test_runner_new/test_runner_single.spl \
  test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl \
  --no-session-daemon --sequential
```

| | OLD (deployed `bin/simple`, pre-fix seed) | NEW (`target/release/simple`, this fix) |
|---|---|---|
| Spec result | 19/19 passed | 19/19 passed |
| `coverage:` banner | `6% (13/209 lines)` | `62% (131/209 lines)` |
| real-path (`engine2d_baremetal_core.spl`) rows in artifact | 17 | 171 |
| `<entry>` rows total | 161 | 7 |
| `<entry>` rows with line in 240-389 (the `impl Engine2DBaremetalCore:` block) | 73 | **0** |
| max real-path line number | 143 | 389 (file's last line) |

Artifacts: `/tmp/probe_ebc.sdn` (old), `/tmp/probe_ebc_new.sdn` /
`/tmp/probe_ebc_new2.sdn` (new — probed twice, once right after the first
build, once again after a full baseline/fix A/B rebuild cycle described
below; both new-binary runs agree exactly: 62% / 0 entry-rows-in-240-389 /
max-line-389).

The remaining 7 `<entry>` rows post-fix (`lines 12, 14, 28, 29, 31, 32, 33`)
are all low line numbers inside the spec file itself — consistent with root
cause 2 (entry-script top-level functions never get an owner registered),
documented but not fixed this pass.

## Regression check

`cargo test --release -p simple-compiler --lib` (filtered to
`interpreter_module`, then separately to `coverage overload module_global
impl_`) surfaced 54 failing tests, all in `mir::lower::tests::branch_coverage::*`
(mostly `gpu_errors` arg-validation cases) and one in
`pipeline::native_project::tests::test_build_import_map_anchors_split_trait_impl_vtable_to_type_definition`.

**These are pre-existing failures on `origin/main`, not a regression from this
fix.** Isolated by swapping `evaluation_helpers.rs` back to the exact
`origin/main` blob (all other files already matched `origin/main` — confirmed
via `git diff origin/main -- <file>` returning empty for every file outside
this one), rebuilding, and re-running two representative failing tests
(`mir::lower::tests::branch_coverage::gpu_errors::gpu_atomic_first_arg_err`,
`pipeline::native_project::tests::test_build_import_map_anchors_split_trait_impl_vtable_to_type_definition`):
both failed identically with the baseline file, confirming the fix is
unrelated. `evaluation_helpers.rs` (the only file this session edited) was
then restored from its saved blob (`c6d995191f38eee525a5f2c77fd561099fded64d`),
release-rebuilt again, and the A/B probe above (`/tmp/probe_ebc_new2.sdn`) was
re-run against that rebuild to reconfirm the fix survived the round-trip.

Full interpreter_module-scoped run: `523 passed; 54 failed` (all 54 in the
two pre-existing-failure groups above; zero failures in any
interpreter/module-evaluator/overload/coverage-owner test). Narrower
`interpreter_module`-substring filter alone: `45 passed; 0 failed`.

## What this does NOT verify

- Root cause 2 (entry-file top-level `<entry>` rows) is unchanged by this fix
  — expected and documented separately.
- `bin/simple` / `bin/release/**` were not touched. Deployment is out of
  scope for this session per task instructions.
- The 54 pre-existing MIR/native_project failures were not root-caused here —
  out of scope for this coverage-attribution task; noted only to establish
  they are not caused by this change.
