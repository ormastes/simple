# `native-build` MIR lowering: instance methods unresolved on a `match`-bound class local — new blocker after the payload-binding fix

## Summary

Follow-up to
`doc/08_tracking/bug/native_build_filehandle_instance_method_unresolved_2026-08-09.md`,
whose `undefined variable: h`/`c`/`n` half is now RESOLVED (root cause was a
seed-interpreter bare-enum-to-Option coercion bug in
`src/compiler/20.hir/hir_lowering/expressions.spl`'s `lower_pattern`, fixed
by wrapping the `hir_payload` assignments in explicit `Some(...)`).

With that fix landed, the `rt_io_file_roundtrip` native-build repro (same
recipe as the resolved doc, ~18 minutes to a definitive result) gets past
every pattern-binding error and now fails later, on instance-method calls
against the (now correctly bound) `FileHandle` locals:

```
[ERROR] MIR error: MIR lowering error: unresolved method call: write_text (x3)
[ERROR] MIR error: MIR lowering error: unresolved method call: close (x7)
[ERROR] MIR error: MIR lowering error: unresolved method call: read_text (x2)
[ERROR] MIR error: MIR lowering error: unresolved method call: size (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: read_all (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: write_all (x1)
[ERROR] MIR error: MIR lowering error: unresolved method call: merge (x3)
error: MIR lowering error: unresolved method call: write_text
```

Zero `undefined variable` errors remain in the log — confirming the sibling
fix holds at full scale, not just in the minimal repro.

## Minimal, fast (~seconds) repro (no stdlib import needed)

```
class FileHandle:
    fd: i64
    static fn open(path: text) -> Result<FileHandle, text>:
        Ok(FileHandle(fd: 1))
    fn write_text(s: text) -> Result<i64, text>:
        Ok(0)
    fn close() -> Result<i64, text>:
        Ok(0)

fn main() -> i64:
    val h = match FileHandle.open("x"):
        case Ok(hh): hh
        case Err(e):
            print("open failed")
            return 1
    match h.write_text("hi"):
        case Ok(_): pass
        case Err(e):
            print("write failed")
            return 1
    match h.close():
        case Ok(_): pass
        case Err(e):
            print("close failed")
            return 1
    print("ok")
    return 0
```

Run via:
```
env SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret \
    bin/release/x86_64-unknown-linux-gnu/simple \
    run src/app/cli/native_build_worker.spl \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry <path>/main.spl \
    --cache-dir <scratch>/cache -o <scratch>/out.o --emit-object
```
Bare field access (`hh.fd`, no method calls) on the SAME match-bound local
compiles clean (`EXIT=0`) — isolating the gap to instance-method dispatch
specifically, not the binding itself (which is now proven fixed).

## Likely mechanism (not root-caused this session — filed for follow-up)

`method_calls_literals.spl`'s `Unresolved` resolution arm (doc comment "Bug
#138/#156 keystone") already documents that native-build never runs the HIR
type-inference pass (30.types), so `receiver.type_` is nil for ordinary
locals, and instance-method dispatch falls back to `struct_value_syms`
(populated at construction/copy sites) to recover the receiver's struct
NAME. Candidate next step: trace whether `struct_value_syms` gets populated
for the specific provenance path a `case Ok(hh): hh` binding produces (the
`bound_payload` local written by `switch_operators_calls.spl`'s enum-match
lowering, ~line 2273-2282) — the payload-binding fix above changed what
value `bound_payload` resolves to (previously it never existed at all,
`undefined variable`), so this is genuinely new ground, not a re-test of
the old "Likely mechanism" theory from the resolved doc (which was about
`Ok(h)` provenance not being threaded into `struct_value_syms`, a
still-plausible but unverified hypothesis for THIS failure).

## Why this matters for the `rt_io_file_*` AOT stub question

Still genuinely UNDETERMINED under true AOT/LLVM codegen — the build now
fails one layer later (at instance-method dispatch) instead of at
pattern-binding, but still never reaches codegen for this fixture.

## Next steps

1. Root-cause why `struct_value_syms` (or whatever mechanism
   `Unresolved`-arm instance dispatch relies on) doesn't resolve `h`'s
   struct name for a `case Ok(h): h`-bound local, using the minimal repro
   above (seconds, not 18 minutes) to iterate quickly.
2. Once fixed, re-run the fence script's `RUN_AOT_LEG=1` leg (or the exact
   repro above) to get the actual stub/no-stub verdict for `rt_io_file_*`.

## Evidence

Full 18-minute closure-source native-build run of
`rt_io_file_roundtrip/main.spl` (real `src/compiler`+`src/app`+`src/lib`),
captured this session; error tally above is a direct grep of that log. Not
attached (large trace log) — reproducible via the recipe above (full repro)
or the minimal fixture (fast iteration).
