# `os.kernel.log.markers` was unimportable; its spec had never run

- **Date:** 2026-07-28
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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
