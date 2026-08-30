# Simple-core partial archive probe signals in managed `char_code_at`

## Status

Open and capped. The focused Rust test
`test_simple_core_source_tree_emits_partial_runtime_archive` exhausted its
three-cycle rerun budget. Do not infer a fix from current structural source
alone; require a fresh admitted rerun after the runtime-owner edits settle.

## Retained evidence

- `archive-parity-cycle2.log` first failed at link time on missing value helpers.
- `archive-parity-cycle3.log` linked and exited 14 at the boxed-float ABI check.
- `rt-value-float-cycle1.log` advanced to exit 77, the `text.bytes()` slot check.
- `downstream-signal-cycle2.log` printed `after77` and then terminated by signal
  (`code=None`) before `after78`.
- In that instrumented probe, the only operation between those markers was
  `rt_string_char_code_at(t, 2)`, where `t` came from
  `rt_string_new("abc", 3)`. This pins the immediate signal boundary to the
  first managed-string character lookup; it is not a raw C-string test.
- `downstream-signal-cycle3.log` also terminated by signal, but its diagnostic
  markers had been removed and therefore cannot narrow the interval further.

## Current source observations

`core_string.spl` now registers every allocated string and
`rt_string_char_code_at` resolves managed handles through
`registered_string_ptr` before reading the header. Its raw-C-string fallback is
used only when registry lookup fails. The runtime files also now use
module-qualified `_sffi_core_string_*` helpers, relevant because the retained
suite emitted many cross-module private-symbol collision warnings.

These changes make two mechanisms plausible: a pre-fix unvalidated header
dereference, or cross-module helper binding corrupting registry/header reads.
The logs do not distinguish them, and no retained stack/core file exists.
Therefore the precise corrupting instruction remains unproven.

## Required prevention evidence

After the concurrent simple-core edits stabilize, one fresh capped verification
must retain all of the following in a single run:

1. The probe prints markers immediately before and after managed ASCII and UTF-8
   `rt_string_char_code_at` calls.
2. A raw ASCII C-string pointer with heap-like low tag bits takes the fallback
   path without a header read.
3. The linked archive contains one canonical public character lookup and no
   unresolved or duplicate module-private `_sffi_*` helper owners.
4. The full value/memory probe exits zero; a structural source assertion alone
   is not sufficient admission evidence.

Retained logs are under `build/test-logs/simple-core-missing-six/`.
