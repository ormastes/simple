# Import alias captures dependency internal name

**Status:** OPEN (unverified 2026-09-12)

Importing `read_file_text as rt_file_read_text` from `std.io_runtime` causes
the imported module's internal `file_read` path to resolve recursively through
the consumer alias. The observable result is a stack overflow at recursion
depth 1000, rather than a normal call to the raw provider.

Reproduction:

```simple
use std.io_runtime.{read_file_text as rt_file_read_text}

val source = rt_file_read_text("simple.sdn")
```

Observed with:

```text
bin/simple test test/01_unit/app/release/install_font_assets_spec.spl --mode=interpreter
stack overflow: recursion depth 1000 exceeded limit 1000 in function 'file_read'
```

Expected: an import alias affects only the importing module's binding. It must
not rewrite or capture identifiers resolved inside the dependency module.

Until resolver ownership is fixed and tested across interpreter/JIT/native,
callers use the canonical exported name directly. Raw SFFI exports must not be
restored as a workaround.

## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
