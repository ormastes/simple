# BUG: std.common.serialization module has no .spl source — interpreter cannot load it

Status: Resolved 2026-05-30

**Date:** 2026-05-30
**Status:** Resolved 2026-05-30
**Severity:** Medium (blocks all interpreter-mode tests that import `std.common.serialization`)
**Affected test:** `test/01_unit/lib/common/serialization_extended_spec.spl`

## Problem

`src/lib/common/serialization/` contains only `.smf` binary stub files (179 bytes each —
clearly empty/placeholder stubs, not compiled artifacts from real source):

```
src/lib/common/serialization/deserialize.smf   179 bytes
src/lib/common/serialization/formats.smf       179 bytes
src/lib/common/serialization/serialize.smf     179 bytes
src/lib/common/serialization/types.smf         179 bytes
src/lib/common/serialization/utilities.smf     179 bytes
```

There is no `__init__.spl` or any `.spl` source file in this directory.
There is also no `__init__.smf` (only per-module stubs), so the module resolver
reports: `Module 'std.common' does not export 'serialization'`.

The test `use std.common.serialization` then calls functions including
`pretty_print`, `pretty_list`, `pretty_tuple`, `pretty_dict`, `detect_format`,
`is_valid_sdn`, `hex_to_digit`, `is_numeric_text`, `parse_int_safe`,
`char_to_digit_safe`, `tag_type`, `is_compressed`, `define_schema`,
`serialize_int_list`, `serialize_text_list`, `serialize_int_list_bytes`,
`serialize_text_list_bytes`, `to_sdn_list`, `to_sdn_tuple`, `to_sdn_dict`,
`unquote_string`, `unescape_string`, `char_code_safe`, and `type_list`.

None of these functions exist in any `.spl` file under `src/lib/`.

## Root cause

The serialization module was stubbed (`.smf` placeholders created) but the
`.spl` source was never authored. The `std.common.sdn` module does have `.spl`
source (`document.spl`, `parser.spl`, `value.spl`) and may overlap in
responsibility with what `serialization` was intended to provide.

## Impact

- **Direct:** `test/01_unit/lib/common/serialization_extended_spec.spl` cannot run in any mode.
- **Indirect:** Any other code that attempts `use std.common.serialization` will fail at import resolution.

## Proposed fix options

**Option A (preferred):** Author the serialization `.spl` source files in
`src/lib/common/serialization/`, adding an `__init__.spl` that re-exports
all sub-modules, and implement the required functions.

**Option B:** If the functionality overlaps with `std.common.sdn`, consider
whether `std.common.serialization` should be a thin wrapper or alias, and
implement accordingly.

**Option C (interim):** Skip the test with a documented reason until Option A
or B lands. Do NOT convert the skip to a NOTE — implement or remove.

## Workaround

None available for interpreter mode. The import fails before any test body executes.

## Resolution

Pure Simple source now exists at `src/lib/common/serialization/__init__.spl`.
The module entrypoint exports the functions exercised by
`test/01_unit/lib/common/serialization_extended_spec.spl`, so
`use std.common.serialization` resolves in interpreter mode without relying on
the placeholder `.smf` stubs.

Verification:

```bash
SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple test test/01_unit/lib/common/serialization_extended_spec.spl --mode=interpreter --clean --fail-fast
```

Result: pass, 153/153 examples.
