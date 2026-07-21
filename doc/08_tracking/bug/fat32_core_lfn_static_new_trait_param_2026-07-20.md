# Bug: static constructors with a trait-typed parameter always fail overload scoring (test-path interpreter)

Status: **RESOLVED**

**Date:** 2026-07-20
**Severity:** high (blocked 17 real FAT32 LFN tests; general interpreter bug, not FAT32-specific)
**Component:** src/compiler_rust/compiler/src/interpreter_method/special/objects.rs

## Symptom

`test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` scored **0 passed / 17
failed**, every case failing at compile/eval time with:

```
semantic: unknown static method new on class Fat32Core
```

`Fat32Core` genuinely declares `static fn new(device: BlockDevice) ->
Fat32Core` (src/lib/nogc_sync_mut/fs_driver/fat32_core.spl:104-134, and the
identical twin in nogc_async_mut). The spec calls it correctly:
`Fat32Core.new(dev)` where `dev` is a `Fat32LfnMockBlockDevice` that does
`impl BlockDevice for Fat32LfnMockBlockDevice`. So neither "class lacks new"
nor "spec uses wrong convention" applied — ground truth confirmed the class
and the call site were both correct.

## Root cause

`bin/simple test` (SSpec) routes through the Rust-seed tree-walking
interpreter's `evaluate_module` path — a **different evaluator** than `bin/simple
run`, which used a separate resolution mechanism unaffected by this bug (a
minimal `Fat32Core.new(dev)` probe passed fine under `run`, isolating the bug to
the test-path evaluator specifically).

In that evaluator, static constructor calls (`ClassName.new(...)` /
`ClassName(...)`) are scored by `constructor_overload_score` ->
`constructor_value_matches_type` -> `constructor_value_type_matches_name`
(src/compiler_rust/compiler/src/interpreter_method/special/objects.rs). For a
`Value::Object` argument, the old code was:

```rust
Value::Object { class, .. } => class == expected,
```

This requires the **argument's concrete class name to literally equal the
declared parameter type name** — it never checks whether the concrete class
implements the declared trait. Any static constructor with a trait-typed
parameter (e.g. `device: BlockDevice`) called with a concrete
trait-implementing value (e.g. `Fat32LfnMockBlockDevice`) scores `None` for
every candidate overload, so `handle_constructor_methods` finds no matching
candidate and reports the generic "unknown static method" error — identical to
the message for a genuinely-missing method.

This is confirmed as a **general interpreter bug, not a Fat32Core/collision
issue**: a minimal probe with a brand-new, non-colliding class
(`ProbeCoreUnique`, never referenced elsewhere in the repo) with `static fn
new(device: BlockDevice) -> ProbeCoreUnique` called with a `ProbeDev2`
implementing `BlockDevice` reproduced the exact same failure. Renaming away
the (also pre-existing, by-design) `nogc_async_mut` twin of `Fat32Core` did
**not** fix it either — it only changed the symptom to an unrelated "variable
Fat32Core not found" (a separate whole-workspace class-loading quirk, not
investigated further since it wasn't the blocker).

## Fix

`constructor_value_type_matches_name` now falls back to the interpreter's
existing `TRAIT_IMPLS` registry (keyed `(trait_name, impl_type)`,
populated during module evaluation for every `impl Trait for Type:` block)
when the direct class-name match fails:

```rust
Value::Object { class, .. } => {
    class == expected
        || TRAIT_IMPLS.with(|cell| cell.borrow().contains_key(&(expected.to_string(), class.clone())))
}
```

Scoped narrowly to this one function (used only by constructor-call overload
scoring), not `Value::matches_type` (used much more broadly for union-type
discrimination elsewhere) — keeps blast radius contained to constructor
argument matching.

## Verification

- New minimal probe (`ProbeCoreUnique.new(device: BlockDevice)` called with a
  `BlockDevice`-implementing concrete type, no name collision) failed before
  the fix and passes after, on a freshly rebuilt seed binary.
- `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl`: **0/17 -> 17/17**
  passing, all real LFN assertions executing (not skipped).
- Regression sweep on other FAT32/driver specs comparing the fixed binary
  against the original (pre-fix) binary as baseline:
  - `test/01_unit/lib/driver/fat32_file_io_spec.spl`: 12 passed / 2 failed on
    **both** binaries — pre-existing failures, unrelated to this fix (not
    triaged further here; out of scope for this lane).
  - `test/01_unit/lib/fs_driver/fat32_core_test.spl`: 0 passed / 5 failed on
    **both** binaries — pre-existing failures, unrelated to this fix.
  - `test/01_unit/os/services/fat32/fat32_spec.spl`: 3/3 passing (unaffected).
  - `test/01_unit/os/drivers/usb/usb_msc_spec.spl`: 10/10 passing (unaffected).
- New Rust regression test added:
  `interpreter_method::special::objects::tests::static_constructor_accepts_trait_typed_argument`.

## Related but distinct bug (do not conflate)

`doc/08_tracking/bug/interp_enum_match_class_name_collision_2026-07-06.md`
documents a *separate* root cause — an import-alias (`use ... as Fat32Core`)
colliding with the real `class Fat32Core` in the interpreter's non-module-
scoped global class registry — that produces the **identical** error string
`unknown static method new on class Fat32Core` for a different set of specs
(anything pulling the full `shell.spl` -> `vfs_boot_init.spl` graph, e.g.
`shell_wm_runtime_loop_spec.spl`). That collision was investigated and ruled
out as the cause here: `fat32_core_lfn_spec.spl` does not import
`vfs_boot_init.spl`, a from-scratch non-colliding probe class
(`ProbeCoreUnique`) reproduced this bug with zero name collisions, and
temporarily renaming away the `nogc_async_mut` Fat32Core twin did not fix the
original repro (it changed the symptom to an unrelated "variable Fat32Core not
found"). The two bugs remain independent and both still need their own fixes;
this doc's fix does not resolve the alias-collision case.

## Blast radius / follow-up

- `bin/simple` currently **is** the Rust seed in this checkout (both print the
  "bootstrap seed only" warning and report the same version), so this fix
  covers the actual test path today. If/when the pure-Simple self-hosted
  compiler (`src/compiler`) is redeployed as the default `bin/simple`, check
  whether its own interpreter/constructor-resolution logic has the equivalent
  gap and needs a mirrored fix.
- Any other static constructor anywhere in the codebase that takes a
  trait-typed parameter and is called with a concrete implementing value (not
  already boxed as a trait object) was silently broken under `bin/simple test`
  before this fix. This is likely why `fat32_file_io_spec.spl` and
  `fat32_core_test.spl` still show pre-existing failures above — not
  confirmed to be the same bug class, not triaged in this lane.

## Follow-up (2026-07-21): "mirrored gap" hypothesis checked and ruled out; 0/6 not reproduced

A later report described `fat32_core_lfn_spec.spl` as **0 passed / 6 failed**
on "the newer self-hosted binary" (vs. the 0/17 this doc fixed on the Rust
seed). Investigated in a fresh worktree at commit `26a5e7394074` (descendant of
this fix's relanded SHA `6b793e5d2b2`):

- **Re-verified the seed fix is solid.** Copied the Rust seed +
  `libsimple_native_all.a` from a sibling checkout; its
  `simple.inputs.sha256` stamp content-hash-matched this worktree's current
  `src/compiler_rust`/`src/runtime` sources exactly (no rebuild triggered),
  confirming the seed binary genuinely reflects this fix. Ran
  `fat32_core_lfn_spec.spl` twice: **17/17 passing, deterministic**, matching
  this doc's own Verification section. Static `it` count also 17
  (`grep -c '^\s*it '`), so the spec file itself is not the problem and the
  seed's discovery is not under-counting.
- **Checked the "mirrored gap" follow-up above directly — it does not apply.**
  Traced the pure-Simple compiler's own static-call resolution:
  `HirExprKind.StaticCall` → `35.semantics/resolve_strategies.spl`
  `resolve_static_method()` (line ~314) → `self.symbols.lookup_static_method
  (type_id, method)`. This resolves **by name + type only**; the `args`
  parameter is accepted but never inspected, so there is no argument-type-based
  overload scoring at all in this path (unlike the Rust seed's
  `constructor_overload_score` chain). `70.backend/backend/interpreter.spl`
  (lines ~507, ~551) just dispatches on the already-resolved `method_id` from
  `MethodResolution.StaticMethod`, again with no type re-check. **The
  trait-typed-constructor bug class this doc fixed cannot occur in the
  pure-Simple compiler** — there's no equivalent unguarded `class == expected`
  check to have a gap in. The follow-up bullet above is superseded by this
  finding; no mirror fix is needed there.
- **Could not reproduce 0/6 directly** — building a genuine pure-Simple
  self-hosted `bin/simple` (native-compiled, not the Rust seed) in this
  worktree to run the exact same test-path evaluator hit the tracked,
  `IN_PROGRESS` `bootstrap_stage2_empty_mir_bodies_2026-07-05` bug at Stage 4
  (full-CLi relink of `main.spl`): repeated `[stmt_get_tag] OOB idx=N
  arena_len=13` / `[flat-bridge] missing stmt tag idx=N` errors, the same
  symptom class that doc tracks, just hit on the much larger `main.spl` surface
  (thousands of functions) rather than the already-fixed 6-function
  `bootstrap_main.spl` case. Stage 2/3 (`bootstrap_main.spl`) build and pass
  bootstrap sanity fine; Stage 4 (full CLI) does not complete in either
  `llvm` or `cranelift` backend within this session.
- **Checked the main repo's actual deployed `bin/simple` directly** (not a
  worktree copy): `bin/simple --version` there *still* prints the "bootstrap
  seed only" warning (`src/compiler_rust/driver/src/seed_warning.rs` is the
  only source of that string — it is Rust-only, never emitted by pure-Simple
  code), confirming the environment is genuinely seed-pinned today, matching
  the Stage-4 finding above. That deployed binary's mtime (2026-07-19 14:21)
  also **predates** this fix's landing (2026-07-20 11:02), so it cannot speak
  to post-fix behavior either way.
  Running `bin/simple test test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl`
  through the normal wrapper (not a direct seed invocation) produced a THIRD,
  different shape of result: no per-example `✓`/`✗` lines at all, one generic
  `error: test-runner: spec failed`, and a summary block reading `Files: 1 /
  Passed: 0 / Failed: 2` — 2 does not match the file's 17 static `it` blocks
  under any itemized accounting. This is the pre-fix "unknown static method"
  bug (expected, given the binary's age) but surfaced through
  `test_runner_client.spl`'s daemon-unavailable fallback (`ensure_daemon()`
  fails -> spawns `bin/simple test --no-session-daemon <path>` as a
  subprocess via `process_run_bounded` and re-parses its captured
  out/err/code) rather than a clean single-process run. A **direct** seed
  invocation (bypassing that recursive wrapper entirely, as done above) gives
  a clean itemized 0/17 or 17/17; going *through* the wrapper's
  subprocess-capture path visibly distorts the reported count. This is an
  observed instance of exactly the discovery/pipe-capture-truncation count
  distortion class flagged as a candidate explanation for "0/6" — captured
  here on the pre-fix binary, but the same wrapper code path applies
  regardless of which binary/fix state it wraps.
- **Conclusion:** the FAT32 LFN driver logic is confirmed correct (17/17,
  deterministic, direct invocation of a fix-verified binary); sync/async
  `fat32_parsers.spl` are byte-identical (no divergence to fix); the
  pure-Simple compiler has no analog of the fixed bug. No binary or invocation
  path available in this session both (a) contains the 2026-07-20 fix and (b)
  goes through the standard `bin/simple test` wrapper, so "0/6" itself was not
  literally reproduced — but the wrapper's subprocess-capture layer was caught
  in the act of distorting a result count on this exact spec file, which is
  strong corroborating evidence that "0/6" is a wrapper/discovery artifact
  rather than a FAT32 regression. Re-run against a `bin/simple` confirmed to
  have cleared Stage 4 (`bootstrap_stage2_empty_mir_bodies` fixed) — ideally
  bypassing the daemon-fallback subprocess wrapper for the first diagnostic
  pass — before treating any FAT32-spec failure count as ground truth.
