# Four database specs shadow StringInterner with incompatible field sets

- **Files**:
  - `test/integration/compiler/core_intensive_spec.spl:17` (fields `strings`, `reverse`, `next_id: i64`)
  - `test/integration/lib/database_core_spec.spl:30` (same wrong field set)
  - `test/unit/lib/database/database_core_spec.spl:51` (same wrong field set)
  - `test/unit/lib/database/database_spec.spl:15` (closer: `str_to_id`, `id_to_str`, but `next_id: i64` instead of `StringId`)
- **Real product code**: `src/lib/nogc_sync_mut/database/core.spl:52` — `class StringInterner`
  with fields `str_to_id: Dict<text, StringId>`, `id_to_str: Dict<StringId, text>`,
  `next_id: StringId` (a wrapper class, not a bare `i64`).
- **Found during**: continuation of the SHADOW-family spec vacuity sweep
  (worklist rows 10, 11, 91, 92 in `spec_shadow_reimplementation_worklist.tsv`).

## What's wrong

All four specs declare `# use std.database.core.{StringInterner, ...}` **only
in a comment**, then define a local `StringInterner` class instead of
importing the real one. Three of the four (`core_intensive_spec`,
`database_core_spec` ×2) use completely different field names
(`strings`/`reverse`) that don't exist on the real type at all — an
import-swap would not compile without a full rewrite of every
`StringInterner(...)` construction site (9-13 call sites per file) and every
field access. The fourth (`database_spec.spl`) is closer (same field names)
but still incompatible: `next_id` is typed `i64` locally vs. the real
`StringId` class, so even its constructors (`StringInterner(str_to_id: {},
id_to_str: {}, next_id: 0)`) would fail to typecheck against the real class
without wrapping every `next_id` in `StringId(value: ...)`.

None of the four specs can catch a real defect in
`src/lib/nogc_sync_mut/database/core.spl` — they only ever exercise their own
local reimplementation, which drifted from the real API (the real class also
carries `SdnDatabase`/`SdnTable`/WAL-related behavior not modeled locally at
all).

## Why not fixed in this pass

Same class of finding as `narrowing_spec`/`riscv_dual_arch_spec`/
`type_infer_correctness_spec`: 3 of 4 files need every constructor site and
field access rewritten against a differently-named field set (not a bounded
import swap), and the 4th needs every `next_id: <int>` call site changed to
`next_id: StringId(value: <int>)` plus verification that `Dict<StringId,
text>`/`Dict<text, StringId>` keying still behaves as the specs assume.

## Unblock condition

Rewrite each of the four specs against the real
`src/lib/nogc_sync_mut/database/core.spl` `StringInterner` (real field names,
`StringId`-typed `next_id`), re-run, and confirm the assertions still hold
against the real intern/lookup/`from_sdn` behavior — not just that
construction typechecks.
