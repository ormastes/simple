# Phase 2 native `__simple_main` failure returns process zero

## Status

Open Phase 2 artifact defect; likely the existing native main-return lowering
class. Compiler files are left to their current owner.

## Evidence

The vector font producer declares `fn main() -> i64`, prints a failed receipt,
and explicitly returns `1` when the receipt lacks `status=pass`. The strict
Phase 2-built Mach-O prints:

```text
vector_font_simple_status=failed reason=selected-font-load
```

but the host process exit status is `0`. Receipt consumers therefore must
continue checking the explicit status field and must not treat process zero
alone as success.

## Required fix

Native lowering must propagate the scalar `i64` result from Simple `main`
through `__simple_main` to the platform process entry. Add a focused failing
main fixture that returns `1` after observable output and require process exit
1 on macOS, Linux, Windows, and BSD. Rebuild the Phase 2/3 artifact before
using exit status as admission evidence.
