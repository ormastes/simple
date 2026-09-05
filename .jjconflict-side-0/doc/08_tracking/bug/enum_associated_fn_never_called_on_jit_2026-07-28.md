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
