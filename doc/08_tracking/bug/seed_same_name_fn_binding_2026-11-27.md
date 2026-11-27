# Seed binds a call to the wrong same-named function (2026-11-27)

Status: open. Found while wiring the phase-3 Hello matrix twin to the
BuildRunner lane twin (PR #12220). Reproduced on the Rust seed
`C:/dev/wt/bound3x-target/release/simple.exe` (sha256
`9c509c621f2cc69fbeb1e4c5df8db6b2e0620ea3c9f6ef9cfc4ef671e37c117f`), Windows.
Both forms run silently: no error, wrong body or nil.

## Form 1 - explicit import loses to a local definition of another arity

`build/repro/rp/alpha.spl`:

```simple
pub fn same_name(a: text, b: text) -> text:
    "alpha:" + a + b
```

`build/repro/rp/beta.spl`:

```simple
use build.repro.rp.alpha.{same_name}
pub fn same_name(n: i64) -> text:
    "beta:{n}"
pub fn call_alpha() -> text:
    same_name("x", "y")
```

`build/repro/main1.spl`:

```simple
use build.repro.rp.beta.{same_name, call_alpha}
fn main():
    print(same_name(7))
    print(call_alpha())
```

`simple run build/repro/main1.spl` prints `beta:7` then `beta:4804457911617`:
the two-`text` call is bound to the local `(i64)` body and runs with a text
handle reinterpreted as an integer. Expected: `alpha:xy` (the explicitly
imported, arg-type-matching definition) or a compile error. The only signal is
the generic `compiler_cross_module_private_symbol_collision` warning, which
claims call sites "resolve by the caller's import path, else by exact arg-type
match" — neither happened.

## Form 2 - a local helper named `context` evaluates to nil in a spec

```simple
use std.spec
struct Box:
    v: i64
fn context(v: i64) -> Box:
    Box(v: v)
describe "local fn named context":
    it "returns the struct":
        val b = context(5)
        expect(b.v).to_equal(5)
```

`simple test <file>` fails with `undefined field 'v': cannot access field on
value of type 'nil'`. The same helper in a plain `simple run` program prints
`v=5`, so the call is bound to the spec DSL's `context` instead of the
module-local function, and the type mismatch is not reported.

## Expected

A module-local or explicitly imported function must win over any other
same-named symbol; when the chosen definition does not accept the argument
types, compilation must fail. Never a silent nil or reinterpreted argument.

## Workaround in tree

PR #12220 renamed its entry to `matrix_buildrunner_run_lane` and the spec helper
to `spec_matrix_ctx`; both are tagged here so they can be reverted once fixed.
