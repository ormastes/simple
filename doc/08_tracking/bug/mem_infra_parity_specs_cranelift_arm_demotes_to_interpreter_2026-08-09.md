# mem_infra guard/harden parity specs: the "cranelift" arm silently runs on the INTERPRETER

- **Status:** OPEN
- **Found:** 2026-08-09
- **Severity:** high — two capability-matrix safety claims (`guard`, `harden`)
  are unverified on the compiled lane, and both specs are currently RED for a
  reason their own failure message does not name.
- **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed,
  29,577,536 bytes, mtime 2026-08-09 04:50)

## Affected

- `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl` — RED,
  `4 total, 3 passed, 1 failed`; failing example
  *"does NOT trap a use-after-free on cranelift, which claims guard: false"*.
- `test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl` — RED,
  `5 total, 4 passed, 1 failed`; failing example
  *"detects write-after-free on cranelift, which claims harden: true"*.

Both are listed in `scripts/check/engine_claiming_specs_baseline.txt`.

## Summary

Both specs try to reach a compiled lane the sanctioned way in spirit — they
spawn a real fixture program (one with `fn main`) out of process under
`SIMPLE_EXECUTION_MODE=jit`, instead of asserting in the spec body. That part
is right, and it is why they were plausible retrofit candidates.

The problem is that **the fixture they spawn de-JITs**. Both fixtures are
extern-bearing, and a program that calls an extern the compiled lane cannot
link falls back to the tree-walking interpreter for the whole module. So the
arm labelled "cranelift" measures the interpreter, and the two specs are
asserting interpreter behaviour against a matrix row that describes cranelift.

This is the exact failure class
`scripts/check/check-engine-claiming-specs-use-probe.shs` exists to catch, one
level further out: the spec did move the work out of process, but never checked
that the child actually arrived at the engine it named.

## Evidence

### 1. Direct proof of demotion — the error comes from the interpreter

`SIMPLE_EXECUTION_MODE=jit` on the harden fixture, stderr:

```
$ SIMPLE_MEM_HARDEN=1 SIMPLE_EXECUTION_MODE=jit \
    bin/simple run test/fixture/mem_infra/harden_tamper_probe.spl
ERROR simple_compiler::interpreter_sffi: 806: rt_interp_call error:
  SemanticWithContext(... "unknown extern function: rt_mem_harden_check_native" ...)
harden_tamper_probe: t0=0
... t1=0  t2=0  t3=0
```

`simple_compiler::interpreter_sffi` is the **interpreter's** extern dispatcher.
Its appearance under `SIMPLE_EXECUTION_MODE=jit` is conclusive: the JIT arm ran
the interpreter.

### 2. The symbol split that makes the demotion fatal rather than silent

- `rt_mem_harden_check_native` is defined **only in C**:
  `src/runtime/runtime_memory.c:240`. It is reachable only from a lane that
  links that archive.
- The interpreter SFFI table registers only the other spelling:
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:350`
  `insert_simple!("rt_mem_harden_check", memory::rt_mem_harden_check);`

So once the fixture demotes, the `_native` call is unresolvable and every
`t<N>` reads 0 — which is **bit-identical to the spec's own knob-off sabotage
control**. The sabotage control therefore cannot distinguish "harden is off"
from "we are on the wrong engine and the symbol vanished". The control is
vacuous in exactly the situation it was written to rule out.

### 3. The guard spec fails the mirror-image way

```
$ SIMPLE_MEM_GUARD_RATE=1 SIMPLE_EXECUTION_MODE=jit \
    bin/simple run test/fixture/mem_infra/guard_uaf_probe.spl
uaf_probe: start          <- no "uaf_probe: survived"
```

The UAF is **trapped** under the arm labelled cranelift. The guard-page
allocator exists only in the interpreter
(`src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs`), so a trap
here is positive proof the interpreter ran. The spec asserts
`survived_uaf("jit", true) == true` on the strength of the matrix row
`guard: cranelift = false`, and goes RED — not because the matrix row is
wrong, but because the measurement never reached cranelift.

Knob-off runs survive on both engines, so the trap is caused by the guard being
switched on; that half of the control is sound.

### 4. This is a regression in engine reach, not a stale claim

`harden_backend_parity_spec.spl`'s header records a hand measurement from
2026-08-02: *"cranelift — true. ... the tamper count tracks exactly
(0,1,2,3). Reached as `rt_mem_harden_check_native`."* That measurement is only
possible if the fixture genuinely ran on the compiled lane at the time. Today
the same fixture, same knob, reports 0,0,0,0 from the interpreter. Something
between 2026-08-02 and 2026-08-09 moved these fixtures onto the de-JIT path.

## Why the obvious fix does not work

Adding a behavioural engine canary to the fixture itself — the
`Dict<text, f64>` miss canary used by
`test/01_unit/compiler/dict_get_miss_returns_nil_jit_probe.spl`, which reads
`true` on the interpreter and `false` under the JIT — was tried and **changes
the failure mode**: introducing a `Dict` into `harden_tamper_probe.spl` turns
the previously warn-and-continue unknown-extern into a hard abort:

```
error: semantic: unknown extern function: rt_mem_harden_check_native
```

so the fixture produces no measurement at all. The canary has to live in its
own minimal file (consistent with the standing rule that one unsupported
operation demotes the whole program), which then proves only that the *harness*
can reach the JIT — not that *this* fixture did.

## What a real fix requires

1. Make the compiled lane resolve the harden check under a single spelling, or
   register `rt_mem_harden_check_native` in the interpreter SFFI table so the
   two lanes stop diverging on the symbol name. (Related, still open:
   `doc/08_tracking/bug/mem_infra_harden_check_symbol_divergence_2026-08-02.md`.)
2. Give each fixture a fail-closed engine attestation that does not perturb the
   measurement, so "we did not reach the named engine" reports as its own
   distinct verdict instead of masquerading as "the feature is off".
3. Only then re-assert the `guard` / `harden` cranelift matrix rows. Until (1)
   and (2) land, those two rows are **unverified on the compiled lane**, and
   the specs should stay RED rather than be re-pointed at the interpreter.

## Do not "fix" by weakening

The failing assertions are correct about what they demand. Flipping the matrix
rows to match the interpreter, or relaxing the arm to accept 0,0,0,0, would
convert a true negative into a permanent false green — the same defect class
the parity specs were written to eliminate.

## Related

- `scripts/check/check-engine-claiming-specs-use-probe.shs` — the ratchet guard
- `src/lib/nogc_sync_mut/spec/engine_probe.spl` — the sanctioned mechanism
- `doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md`
- `doc/08_tracking/bug/mem_infra_harden_check_symbol_divergence_2026-08-02.md`
- `doc/07_guide/infra/testing/spec_engine_reach.md`
