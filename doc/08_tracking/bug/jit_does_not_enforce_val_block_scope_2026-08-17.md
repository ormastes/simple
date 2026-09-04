# JIT does not enforce `val` block scope; the interpreter does

**Status:** RESOLVED 2026-09-02 — the leak is gone; both engines now reject.

Differential probe (a `val` bound in one `if` body, read in a SIBLING `if`
body, on aarch64-apple-darwin):

| binary | result |
|---|---|
| deployed seed of 2026-07-25 (pre-fix) | `rc=0`, prints **7** — the binding leaked, reproducing this record exactly |
| seed built from `origin/main` `1b76db1d6c3` | `rc=1`, ``error: semantic: variable `idx3` not found`` |

The fresh seed's Cranelift path is the thing that now refuses it — it reports
`GlobalLoad: unresolved identifier 'idx3'` from codegen before the semantic
error surfaces — so this is not merely the interpreter arm being consulted.
That said, the verifying host's local build cannot complete a JIT module at
all (unresolved `rt_struct_alloc` drops every module to the interpreter), so
what is proven is that the JIT no longer SILENTLY ACCEPTS the out-of-scope
read; a full JIT-executed run of the same probe was not obtainable here.
Guarded by `scripts/check/check-named-ctor-and-val-scope.shs`, which FAILs
naming `val_leaked_across_sibling_if(printed 7)` on the old binary and PASSes
on the fixed one.

**Previous status:** OPEN (P1)
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
