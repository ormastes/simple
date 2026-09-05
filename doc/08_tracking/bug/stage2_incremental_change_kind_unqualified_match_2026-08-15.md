# Stage 2 rejects unqualified incremental ChangeKind variants

**Status:** fixed and cleared by the next canonical Stage-2 transaction.
**Observed:** 2026-08-15.

After the recursive global-struct HIR fix, the canonical Rust-authority
transaction reached Stage 2 and failed normally with one source diagnostic:

```text
src/compiler/80.driver/driver_build/incremental.spl: hir: Unsupported feature:
`case Added:` is not a variant of the matched enum, so it is an irrefutable
BINDING that matches every remaining value and makes every later arm
unreachable.
```

The immutable wrapper evidence is
`build/native_probe/stage4-owner-20260815/canonical-after-recursive-struct-fix.{log,status,time}`;
the canonical transaction exited 1 and refused seed fallback. The active
`stage2-native-build.log` has since been overwritten by later retries.

Canonical transaction evidence is retained at
`build/native_probe/stage4-owner-20260815/canonical-after-recursive-struct-fix.log`:
exit 1, elapsed 15m30.95s, peak RSS 2,701,132 KiB. Its frozen inventory was
13,015 inputs and 12,409 Simple files (1,749 compiler, 7,820 library, 2,616
application). It produced no Stage-2 binary, Stage-3/Stage-4 candidate, hash,
smoke, deployment, or rollback evidence.

## Root cause

`BuildCache.detect_changes` matched `ChangeKind` with `case Added | Modified`.
Uppercase bare names which are not proven variants are bindings in the modern
HIR matcher. The first binding therefore matched every value and made the
remaining alternative and wildcard arm unreachable. Other uses in this file
already construct and compare the variants as `ChangeKind.Added` and
`ChangeKind.Modified`.

## Fix

Qualify both alternatives:

```simple
case ChangeKind.Added | ChangeKind.Modified:
```

This is a pure-Simple source correction. No Rust compiler change, fallback, or
diagnostic weakening is required. The exact integration reproducer is the
single Stage-2 compilation of
`src/compiler/80.driver/driver_build/incremental.spl` with the admitted Rust
authority and an isolated cache. The subsequent manifest-verified canonical
transaction compiled all 846 entry-closure modules and reached the final link;
this diagnostic did not recur. Its distinct successor is the `rt_file_sync`
provider gap recorded in
`stage2_bootstrap_rt_file_sync_provider_missing_2026-08-15.md`.

## Focused evidence

Evidence is retained under
`build/native_probe/stage2-incremental-change-kind-20260815/`.

- Seed `check` was unavailable because that command delegates to the required
  pure-Simple `bin/simple`, which has not yet been produced (`exit 127`).
- The direct Rust-seed native object probe used an isolated cache and the
  corrected file as its entry. It ran 64.42 seconds with 2,952,820 KiB peak
  RSS. The original unqualified-variant HIR diagnostic did not recur.
- The broader imported closure then stopped at a distinct, location-free
  semantic diagnostic, `invalid assignment: cannot assign field on non-object
  value`. Full stderr was preserved before fixing under
  `build/native_probe/stage2-field-assignment-20260815/mutation-probe.log`;
  the distinct Rust-interpreter owner is recorded in
  `rust_interpreter_nested_class_instance_field_assignment_2026-08-15.md`.

Two speculative duplicate records were reconciled into this canonical source-
fix record. The post-fix qualified source and a passing synthetic duplicate-
owner Rust test do not prove a whole-project enum-identity defect; no compiler
matcher weakening is part of this fix.

Provider token usage: unavailable. Comparable completed-bug average:
unavailable.
