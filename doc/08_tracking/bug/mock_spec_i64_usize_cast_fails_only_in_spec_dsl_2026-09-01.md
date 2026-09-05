# `mock_spec.spl`: `i64 as usize` cast fails inside a spec `it` block but works in compiled `fn main()`

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/testing/mock_spec.spl`, 55/56 passing — 1 failure).

## Symptom

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/testing/mock_spec.spl
```

```
Call Inspection
    ✗ retrieves specific call by index
      semantic: type mismatch: cannot cast i64 to usize
```

`test/01_unit/lib/std/testing/mock_spec.spl:115-119`:
```
fn get_call(index: i32) -> Option<CallRecord>:
    if index >= 0 and index < self.calls.len() as i32:
        Some(self.calls[index as usize])
    else:
        nil
```
called as `mfn.get_call(0)` at line 276, inside `describe "Mock Function
Tracking": ... it "retrieves specific call by index": ...`.

## Minimal repro — isolates the defect to the spec-DSL execution context

The identical class + method, called the identical way, from a plain
`fn main()` (compiled/interpreted directly, no spec runner), **succeeds**:

```simple
class MockFunction:
    calls: [text]
    static fn new() -> MockFunction:
        MockFunction(calls: [])
    me record_call(v: text):
        self.calls.append(v)
    fn get_call(index: i32) -> Option<text>:
        if index >= 0 and index < self.calls.len() as i32:
            Some(self.calls[index as usize])
        else:
            nil

fn main():
    val mfn = MockFunction.new()
    mfn.record_call("GET")
    match mfn.get_call(0):
        Some(x): println(x)
        nil: println("none")
```
prints `GET` cleanly via `bin/simple run`.

The SAME class/method wrapped in `describe "Mock": it "...": ... match
mfn.get_call(0): Some(call): expect call.args[0] == "GET" ...` and run via
`bin/simple test` fails with `semantic: type mismatch: cannot cast i64 to
usize` on the `index as usize` cast, even though `index` is a declared `i32`
parameter and the literal argument is `0`.

This points to the spec-runner/interpreter passing/boxing the integer
literal argument differently (as a wider/dynamic `i64` that doesn't
narrow to the declared `i32` parameter type) than the JIT-compiled `fn
main()` path does, which then breaks the `as usize` cast specifically in
interpreted spec-DSL execution.

## Why not fixed here

This is an interpreter/spec-runner argument-type-coercion discrepancy
between execution engines (see `.claude/rules/testing.md` "`run` and `test`
are DIFFERENT ENGINES"), not a bug in the test's own logic — the exact same
code is correct and works standalone. Fixing it requires compiler-internals
work in the interpreter's call-argument coercion path, which is out of scope
for a stdlib-spec triage pass.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/testing/mock_spec.spl
```
