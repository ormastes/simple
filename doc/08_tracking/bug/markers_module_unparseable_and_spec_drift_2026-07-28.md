# `os.kernel.log.markers` was unimportable; its spec had never run

- **Date:** 2026-07-28
- **Status:** FIXED 2026-11-06 (marker_wire_format_spec 8/8)
- **Module:** `src/os/kernel/log/markers.spl`
- **Spec:** `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` (mirror: `test/unit/...`)

## What was broken

Three stacked defects meant `markers.validate()` had never executed, and the
marker wire-format spec had never run a single example.

1. **The module could not be parsed at all.** `MarkerSpec` declared a field
   named `namespace`, which the "common mistake" detector rejects as a hard
   error (`Use 'mod' for modules instead of 'namespace'`) at every one of its
   24 occurrences. Any file doing `use os.kernel.log.markers.{...}` — including
   the spec — died before running. **Fixed:** field renamed `namespace` → `ns`.
   (The detector firing on a *struct field* rather than a declaration is
   arguably its own bug; renaming is the contained fix.)
2. **`validate()` called `spec.is_nil()`** on an `Option`. `is_nil` is not a
   language builtin and is unresolvable on any receiver. **Fixed:** `spec == nil`.
3. **`validate()` returned `Result.err(...)` / `Result.ok(())`.** `Result` is not
   a class in Simple; this raises `semantic: unknown class Result` at runtime.
   **Fixed:** `Err(...)` / `Ok(())`.

## Spec verdicts

| | before | after |
|---|---|---|
| whole spec | 0 examples run — module parse error | 8 examples, 4 failures |

`validate()` now genuinely runs and correctly rejects a level-prefixed marker.

## Left open (NOT fixed — need an owner who knows the wire truth)

- **`[BOOT]` vs `[boot]` case mismatch (2 failures).** `NS_BOOT` /
  `namespace_prefix(Boot)` produce `"[BOOT]"`; the spec asserts `find_spec`
  matches `"[boot] entry"` and that `marker_string` starts with `"[boot] "`.
  One side is wrong. Not changed here because the case is part of the serial
  wire format the QEMU boot-log parser reads, and flipping it blind could break
  real log parsing. Note that every *other* namespace constant in the file is
  lowercase (`[vfs]`, `[pack]`, `[launcher]`), which suggests `[BOOT]` is the
  outlier.
- **`NAMESPACE_BOOT` does not exist (2 failures).** The spec imports it and
  passes it to `marker_string`, but the module only has the enum
  `MarkerNamespace.Boot` and the private `NS_BOOT` text constant. The spec was
  written against an API shape that is not in the module.

## Note

`markers.spl` has no production callers — nothing outside the spec imports it,
which is unsurprising given it could not be imported. Whatever emits the real
kernel boot markers does not route through this registry.

## Resolution (2026-11-06)

The 2026-07-28 source fixes had been lost in a tree restore; re-applied in
`src/os/kernel/log/markers.spl`: field `namespace` -> `ns`, `validate()` uses
`Err(...)`/`Ok(())`, and nil handling uses `.?` (no `is_nil`). Open items:
- `NAMESPACE_BOOT` now defined (`= MarkerNamespace.Boot`).
- Case: wire truth is `[BOOT]` (every real kernel producer emits `[BOOT] ...`),
  so the spec's `[boot]` literals were stale and now say `[BOOT]`; module unchanged.

## Verification (2026-11-25)

Re-verified on `release/1.0.0` (worktree `wt-p3-markers`) that the two items
left open on 2026-07-28 are both resolved by commit `44bce8446db` and the spec
is green. No code change was required.

### Root cause of the remaining drift

The 2026-07-28 fix pass repaired parse/Option/Result defects but left the spec
and module disagreeing on the API shape (`NAMESPACE_BOOT` missing) and on the
boot namespace case (`[BOOT]` vs `[boot]`). The 2026-11-06 pass closed both:
`NAMESPACE_BOOT: MarkerNamespace = MarkerNamespace.Boot` was added, and the
case question was settled in favor of `[BOOT]` — not lowercase — because the
real kernel producers emit uppercase: `src/os/kernel/arch/x86_64/boot.spl` and
`src/os/kernel/arch/x86_32/boot.spl` emit `[BOOT] ...` via
`log_raw_println`/`serial_writeln` (e.g. `"[BOOT] Memory map: {entry_count}
entries"`). The spec's `[boot]` literals were the stale side. Note this
contradicts the "all other namespaces are lowercase, so `[BOOT]` is the
outlier" hypothesis from 2026-07-28: the registry's lowercase constants are
the outliers relative to real wire traffic, and flipping the module to
lowercase would have diverged it from the actual boot log.

### No-production-callers evidence

`rg -l 'log\.markers|log/markers' src test scripts tools doc` matches only:

- the four specs in `test/01_unit/os/kernel/logging/` that exercise the
  module (`marker_wire_format_spec.spl`, `marker_attrs_schema_validation_spec.spl`,
  `marker_namespace_api_prevention_spec.spl`,
  `marker_registry_attrs_enforcement_class_spec.spl`), and
- docs/bug-db entries.

Nothing under `src/` imports `os.kernel.log.markers`; the real boot markers
are emitted directly by the arch boot code above, so the case decision could
not break the QEMU boot-log parser. The `test/unit/...` mirror mentioned in
the 2026-07-28 header no longer exists.

### Before / after spec output

Before (as recorded 2026-07-28, seed binary): 0 examples run — module parse
error; after the partial fix, 8 examples with 4 failures (2x `[BOOT]` vs
`[boot]` case, 2x missing `NAMESPACE_BOOT`).

After (2026-11-25, self-hosted `bin/simple.exe`,
`SIMPLE_LIB=src bin/simple.exe test test/01_unit/os/kernel/logging/marker_wire_format_spec.spl --mode=interpreter`):

```
SPEC FILE VERDICT: test/01_unit/os/kernel/logging/marker_wire_format_spec.spl outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 blocked=0 dropped=0
Results: 8 total, 8 passed, 0 failed
```

Environment note: the Rust bootstrap seed (`bin/simple`, Oct 5) cannot parse
this branch's stdlib (`unit ByteSize: i64` in `src/lib/common/types.spl`
fails with `expected As, found Newline`); the tracked self-hosted
`bin/simple.exe` must be used instead.
