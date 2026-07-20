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
