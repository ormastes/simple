# JIT does not enforce `val` block scope; the interpreter does

**Status:** OPEN (P1)
**Filed:** 2026-08-17
**Component:** JIT scope handling
**Class:** engine divergence — the same source is an error in one engine and silently succeeds in the other

## Symptom

A `val` declared inside an `if` body and read in a *sibling* `if` body:

```
if i + 2 < clean_len:
    val idx3 = ...
if i + 3 < clean_len:
    ... idx3 ...        # out of scope
```

| engine | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `rc=1`, ``error: semantic: variable `idx3` not found`` — correct |
| `SIMPLE_EXECUTION_MODE=jit` | `rc=0`, computes the right answer — the binding leaks |

Measured on the stale seed **and** on a fresh `cargo` build (08:33), identically.

## Why this is worse than a scoping nit

1. **The default engine is JIT**, so a bare `bin/simple run` silently accepts
   out-of-scope code. The defect only appears when something forces the
   interpreter — a spec body, or an explicitly pinned arm.
2. It **hides real defects**. This is exactly how the PASETO P1 stayed alive:
   `_p4_b64u_decode` read an out-of-scope `idx3`, the JIT leaked the binding and
   computed correctly in some paths, and the failure surfaced only as corrupt
   decode output elsewhere. See
   `doc/08_tracking/bug/paseto_v4_tampered_token_signature_accepted_2026-07-20.md`
   and commit `5294ff50d07`.
3. It **manufactured a phantom compiler bug**. The fixer of that row observed a
   `val` leaking "in one shape but not in two sibling ifs inside a while body"
   and filed it as a possible scoping bug of unknown mechanism. It is not shape —
   it is **engine**. One probe ran under a bare `run` (JIT) and the other under
   the interpreter. An adversarial verifier's contradicting "scope leak" demo was
   almost certainly the same confusion.

## Reproduction

Extract any function with the sibling-`if` shape into a standalone file and run
both pinned arms, reading rc into a variable on the line AFTER the command:

```
SIMPLE_EXECUTION_MODE=interpret bin/simple run /tmp/probe.spl   # rc=1, error
SIMPLE_EXECUTION_MODE=jit       bin/simple run /tmp/probe.spl   # rc=0, succeeds
```

## Which engine is correct

The **interpreter**. A `val` is block-scoped; a sibling block must not see it.
The JIT is the defect here — the opposite direction from the alias/class
divergence recorded in
`engine_divergence_guard_hardcodes_stale_seed_2026-08-17.md`, where the JIT is
right and the interpreter is wrong. The two engines disagree in *both*
directions, on different features.

## Fix direction

The JIT's scope handling should drop bindings at block exit, and an out-of-scope
read should be the same hard semantic error the interpreter raises. Until then,
**no `bin/simple run` result proves a program is scope-clean** — only a pinned
interpreter arm does.

## Not verified

- Whether `var` leaks the same way, or only `val`.
- Whether the leak extends beyond sibling `if`s (loops, nested functions, match
  arms).
- Whether native/AOT behaves like the JIT or the interpreter — a third engine,
  untested.

## Re-check 2026-09-13

- Status: CLOSED (2026-09-13) — not reproducible with the described sibling-`if` shape on `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple` (symlinked from the shared main worktree), sha256 `3d120a6f9ab5`, `Simple Language v1.0.0-rc.1`.

Built a standalone probe matching the described shape exactly (a `val`
declared inside one `if` body, read in a sibling `if` body):

```simple
fn f(i: i64, clean_len: i64) -> i64:
    if i + 2 < clean_len:
        val idx3 = i + 100
    if i + 3 < clean_len:
        return idx3
    return -1
```

```
SIMPLE_EXECUTION_MODE=interpret bin/simple run <probe>   -> rc=1, "error: semantic: variable `idx3` not found"
SIMPLE_EXECUTION_MODE=jit       bin/simple run <probe>   -> rc=1, same error
```

Under JIT, Cranelift codegen itself now fails to compile the out-of-scope
reference (`GlobalLoad: unresolved identifier 'idx3'`) and the runtime falls
back to the interpreter, which then raises the correct semantic error — so
the end-to-end observable behavior (rc=1, hard error, no silent leak) now
matches between engines for this shape, even though the mechanism is a
codegen failure + fallback rather than genuine block-scope enforcement in
the JIT itself. Not verified: whether a shape that does NOT trip a codegen
failure (e.g. one where Cranelift can still assign the out-of-scope slot a
register without erroring) still leaks silently — the "Not verified" bullets
in the original report (loops, nested functions, match arms, `var`) remain
unchecked. Given the specific filed repro no longer manifests the silent
`rc=0` symptom, closing this instance; a narrower shape that still leaks
would need its own report.
