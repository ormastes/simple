# Imported function calls skip the arity check (2026-11-07)

**Status:** open. **Found by:** stage2 run 15 (`compiler_cli_build`).

## Symptom

A call to an IMPORTED free function with too many arguments is accepted by
HIR lowering and silently miscompiled. A call to a same-module function with
the same shape is rejected
(`function 'note' accepts at most 1 argument(s), but 2 were provided`).

Repro (stage2 `bootstrap-opus-15`, cranelift, whole-program route):

```
# build/repro/arity_lib.spl
pub fn note(msg: text):
    print "note {msg}"

# build/repro/arity2.spl
use build.repro.arity_lib.{note}
fn main():
    val x = 3
    note(x, "two args")
```

`native-build` exits 0; the binary prints `note ` (the wrong argument, decoded
as text). In the compiler itself the same defect reached codegen as a
cranelift declaration clash: `driver_aot_native_output.spl` called
`log_error(log, msg)` against `driver_log_helpers.log_error(msg: text)`, and
the backend failed with "signature (i64, i64) -> i64 is incompatible with
previous declaration (i64) -> i64". Those two call sites are fixed in source;
the missing diagnostic is not.

## Expected

The same arity diagnostic as for a local callee, fail-closed at HIR lowering.
