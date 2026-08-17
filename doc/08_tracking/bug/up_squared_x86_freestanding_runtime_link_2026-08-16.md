# UP Squared minimal x86 freestanding runtime link failure

Status: OPEN
Owner: UP Squared Apollo Lake SimpleOS lane
Date: 2026-08-16

The provenance-admitted Stage 3 compiler lowers the partial UP2 entry closure,
but the dedicated minimal linker invocation omits the established x86
freestanding runtime bundle. Linker diagnostics include `rt_string_new_literal`,
`rt_for_iterable`, `rt_array_new`, `rt_enum_new`, `serial_println`, and
`rt_serial_readline`.

The fix must bind the canonical x86 C/ASM runtime providers used by existing
SimpleOS board builds. Do not add weak fabricated stubs or use the Rust seed.
After the third bounded cycle the lane stopped per the runaway guard.

Resume command after changing the provider contract:

```text
SIMPLE_BUILD_COMPILER=/home/yoon/simple/build/bootstrap-stage23-sync-final/stage3/x86_64-unknown-linux-gnu/simple sh scripts/os/build-simpleos-up-squared-apollo-lake.shs
```

