# Bug: `EnumName.assoc_fn()` is never called on the JIT — returns a bogus value, no error

- **Date:** 2026-07-28
- **Status:** open
- **Severity:** critical (silent wrong values codebase-wide on the default engine; engines disagree)
- **Found by:** lane S3 while diagnosing "SdnValue insert does not persist"; reproduced independently by the coordinator

## The defect

Calling an associated function on an **enum** silently yields a value that
matches no `case` arm. It does not need to exist:

```
enum E1:
    A
    B

fn main():
    val x = E1.totally_undefined()
    print "got: {x}"
```

| engine | result |
|---|---|
| default (JIT) | `got: <enum@0x40038068740>` — **no error, exit 0** |
| `SIMPLE_EXECUTION_MODE=interpreter` | `error: semantic: unknown variant or method 'totally_undefined' on enum E1` |

The interpreter is correct. The JIT accepts a call to a method that was never
defined anywhere and fabricates an enum-shaped value for it.

**Class statics and free functions are unaffected** — in the same file,
`Box.make()` runs and a free `fn` runs. The hijack is specific to `EnumName.`
receivers.

## Escalation: a *defined* associated function is equally broken

The original writeup used an undefined method, which invited the reading that
this is only a missing-diagnostic bug. It is not. A properly declared
`static fn` is never called either:

```
enum E1:
    A
    B

    static fn make() -> E1:
        E1.B

fn main():
    val x = E1.make()
    match x:
        case E1.A: print "got A"
        case E1.B: print "got B"
        case _:    print "got NOTHING"
```

| engine | result |
|---|---|
| default (JIT) | `got NOTHING` — falls to the wildcard |
| interpreter | `got B` |

So every enum associated constructor in the tree returns a value matching no
arm under the JIT. Reproduced by the coordinator.

## Likely cause

`hir/lower/module_lowering/module_pass.rs` (~L402) registers every
`EnumName.method` as a **global**; the JIT's `ctx.func_ids` lookup in
`codegen/instr/calls.rs` (~L3172) then falls through silently instead of
erroring.

## Blast radius

Every enum associated constructor is suspect on the default engine. Any spec
that builds values through one — `SdnValue.int(...)`, `SdnValue.string(...)`,
`SdnValue.empty_dict()` — may be **passing vacuously**, because the
constructed value matches no arm and the code under test never actually runs.
This needs a sweep; the count is not yet known.

## How it surfaced

`SdnValue.empty_dict()` is not a dict at all, so both `insert` and `get` fall
through to `case _`. The SDN module itself is correct: on an inline
`SdnValue.Dict({})` under the JIT, insert→get is green.

## Second, separate defect (interpreter)

The interpreter deep-copies the enum payload at the `case Dict(d)` binding —
**including a class payload** — so the payload write lands on a dead copy.
`insert` returns true and `_sdn_dict_put` runs, yet `len()` stays 0.

Consequences, all measured:
- `fn insert(mut self, ...)` with `self = SdnValue.Dict(tmp)` does **not**
  propagate. Extract-mutate-write-back is not a workaround here.
- The usual reference-wrapper escape hatch does not exist either, because the
  class payload is copied too.
- Only a write-back performed in the **caller's own frame** sticks.

## Reproduce

```
bin/simple run build/sdnins_probe/probe10.spl                          # decisive, 12 lines, no imports
bin/simple run build/sdnins_probe/probe8.spl                           # class static works, enum static does not
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/sdnins_probe/probe1.spl   # case E: dead-copy write
```

## Not fixed

Two fix attempts (enum-body `static` parsing; HIR static-member routing) were
built, tested, disproven, and fully reverted. `src/compiler_rust/` is
unmodified by this lane and the bootstrap binary was rebuilt from reverted
sources so it matches HEAD.

## Next step

1. Make the JIT's `func_ids` miss an **error** rather than a silent
   fall-through — that alone converts this from a wrong answer into a
   diagnostic.
2. Sweep for specs that construct values via an enum associated function and
   re-check them; assume vacuous until re-verified.
3. Fix the interpreter's `case` binding so an enum payload is not deep-copied,
   or document that payload mutation must be written back by the caller.


## Re-measurement 2026-08-17 (P0-core silent-wrong triage lane) — NOT REPRODUCED

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed). Probes run under both
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit`.

A declared enum associated function was called under a REAL JIT run:

```
enum E:
    A
    B
    static fn pick() -> i64:
        7
```

`E.pick()` returns `7` on both the interpreter and the JIT. The doc's claim is
that the JIT never invokes the function and returns a bogus value with no error.

**Guard against a false green, stated because it nearly happened here.** An
earlier version of this probe also constructed a lambda, and the JIT printed
`JIT compilation failed, falling back to interpreter: ... creates a
lambda/closure ... deferring to interpreter` — i.e. the whole module silently
ran on the interpreter and the "JIT" arm proved nothing. The measurement above
was re-run with the lambda removed and produced no fallback line, so the JIT
genuinely compiled it. Any future re-check of this doc must confirm the absence
of that fallback message before believing a JIT result.

**Scope of this close.** Rust-seed JIT only. The native/AOT lane and the
pure-Simple lanes were not measured.

## Update 2026-08-17 — DOES NOT REPRODUCE on the JIT; closing the JIT claim

Both this doc and its sibling (`enum_associated_fn_never_called_on_jit_2026-07-28`
/ `enum_impl_static_fn_scoping_2026-07-29`) assert that a declared enum
associated fn yields a silent wrong value under the JIT. **That is no longer
true.** These two rows collapse into one finding.

Gate spec both docs name, run on the deployed seed:

```
test/shared/control_flow/static_fn_spec.spl
SPEC FILE VERDICT: declared>=26 executed=26 passed=26 failed=0 dropped=0
Results: 26 total, 26 passed, 0 failed
```

executed=26, so the run is non-vacuous, not a silent exit-0.

Direct probe — the bodies genuinely execute and the values are correct:

```simple
enum Col: Red; Blue
impl Col:
    fn make() -> Col: print("BODY RAN"); Col.Blue
    fn tag() -> i64:  print("TAG BODY RAN"); 7
```

JIT: `BODY RAN` / `is_blue=true` / `TAG BODY RAN` / `t=7`.

**Measurement trap worth recording:** an earlier pass of this probe printed
`c => <enum@0x4da548111a0>` and was very nearly filed as "returns a bogus
value". That string is just `to_text()`'s formatting of an enum value — the
value itself is correct, as `c == Col.Blue` -> `true` shows. Asserting on a
`to_text()` rendering rather than on the value is how a correct enum gets
reported as garbage.

**Remaining live defect, out of scope for this batch:** the *interpreter* still
rejects the same program outright —
`error: semantic: unknown variant or method 'make' on enum Col`, exit 1. That is
a real gap, but it is **loud** (non-zero exit, explicit diagnostic), not a
silently-wrong result, and it lives in
`src/compiler/10.frontend/core/interpreter/**`, which is claimed by another lane.
Not fixed here; flagged for that lane.

**Action:** JIT claim -> FIXED (does not reproduce). Interpreter gap re-filed as
the surviving issue.
