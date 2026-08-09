<!-- RESOLUTION APPENDED 2026-08-09; original report retained below. -->
# mem_infra parity specs: the "cranelift" arm never measured cranelift

- **Filed:** 2026-08-09
- **Status:** PARTIALLY FIXED — the registration defect is fixed and both specs
  are GREEN for real reasons; the natively-linked-backend coverage gap is
  SCOPED OUT and recorded below.
- **Files:**
  - `test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl` (was 4/5 RED, now 5/5 GREEN)
  - `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl` (was 3/4 RED, now 4/4 GREEN)
  - `test/fixture/mem_infra/harden_tamper_probe.spl`
  - `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:351`
  - `src/lib/common/mem_infra/config.spl:66-89`

## Summary

Both specs spawn an out-of-process fixture under `SIMPLE_EXECUTION_MODE=jit` and
label that arm "cranelift". Two independent defects made that arm dishonest.

### Defect A — unregistered extern silently yields 0 (FIXED)

`test/fixture/mem_infra/harden_tamper_probe.spl` declares
`extern fn rt_mem_harden_check_native() -> i64`. That symbol exists in
`src/runtime/runtime_memory.c:240`, but the SFFI dispatch table in
`interpreter_extern/mod.rs` registered only `rt_mem_harden_check`.

Measured before the fix (`bin/simple run`, `SIMPLE_MEM_HARDEN=1`, jit):

```
ERROR simple_compiler::interpreter_sffi: rt_interp_call error:
  "unknown extern function: rt_mem_harden_check_native" (E1002)
harden_tamper_probe: t0=0
harden_tamper_probe: t1=0
harden_tamper_probe: t2=0
harden_tamper_probe: t3=0
```

The call is logged and then yields 0 without aborting. `0,0,0,0` is
**bit-identical** to the spec's own knob-off sabotage control, so that control
was vacuous exactly when it mattered: a completely dead check passed it.

**Root cause was NOT a silent de-JIT demotion.** The module is JIT-compiled; the
error arrives from the `rt_interp_call` trampoline, i.e. from compiled code. The
JIT resolves externs through the same Rust table the tree-walk interpreter uses
— it does not dlsym the process — so this was a plain registration-list
omission, not a codegen gap.

**Fix:** register the C spelling as an alias of the same handler
(`interpreter_extern/mod.rs`, one `insert_simple!` line + rationale comment).
This also resolves
`mem_infra_harden_check_symbol_divergence_2026-08-02.md` for every lane that
consults that table.

Measured after the fix (rebuilt seed, `cargo build --release`):

| lane | `SIMPLE_MEM_HARDEN=1` | knob unset |
|------|----------------------|------------|
| jit  | `t0=0 t1=1 t2=2 t3=3` | `t0=0 t1=0 t2=0 t3=0` |

The two directions are now distinguishable, so the sabotage control is real.

### Defect B — the JIT arm was asserting a false premise (FIXED, by correcting the oracle)

The guard spec asserted `survived_uaf("jit", true) == true` ("the guard knob is
inert on cranelift"). Measured: the child dies on **SIGSEGV** (exit 139) — the
guard page is present. This was not a weak oracle, it was a *wrong* one, derived
from the same false premise as Defect A: that a jit-mode `bin/simple run`
resolves `rt_alloc` to the C runtime. It does not; it binds
`interpreter_extern/mem_guard.rs`, guard pages included.

Both specs' docstrings, the fixture header, and the `config.spl` matrix comment
asserted that false premise in prose. All four are corrected in place. The guard
spec's JIT arm now asserts what is true and says what it covers: it pins the
allocator the in-process JIT lane genuinely binds (knob-off survives, knob-on
traps — sabotage control intact), and explicitly disclaims being evidence about
the `cranelift` matrix row. That row is retained as a static assertion.

## Scoped out: no automated coverage of the natively-LINKED backends

Neither spec can reach the lane the `cranelift`/`llvm` matrix rows actually
describe — a finished `native-build` artifact, whose `rt_alloc` comes from
`runtime_native.c` (plain `malloc`, no quarantine, no guard pages) and which
does not link `runtime_memory.o` at all.

- **Why out of scope here:** it needs a full `native-build` per arm (minutes,
  not seconds) plus a link-failure oracle (`undefined symbol:
  rt_mem_harden_check_native`) distinct from the runtime oracles these specs
  use. Both rows were measured by hand on 2026-08-02 and recorded in
  `mem_infra_guard_row_false_on_native_backends_2026-07-31.md`; the matrix rows
  themselves are correct.
- **Unblock condition:** a slow-lane spec (`--only-slow`) that drives
  `native-build` for each backend and asserts (a) the UAF probe survives at
  `SIMPLE_MEM_GUARD_RATE=1`, and (b) the harden probe fails to LINK. Until then
  the native rows rest on a hand transcript, and a regression in the native
  allocator lane would not turn any spec red.

## Residual defect (open, unrelated to both specs)

With the alias registered, `rt_mem_harden_check_native` resolves under
`SIMPLE_EXECUTION_MODE=jit` but still fails under
`SIMPLE_EXECUTION_MODE=interpreter`:

```
a=0                                                   # rt_mem_harden_check     - resolves
error: semantic: unknown extern function: rt_mem_harden_check_native
```

Both spellings are in the one `EXTERN_DISPATCH` map and the map is consulted
first in `interpreter_extern/mod.rs:2637`, so the tree-walk interpreter must be
resolving externs through a *different* path than `rt_interp_call`. That path
was not located. It does not affect either parity spec (the interpreter arms use
`harden_poison_workload.spl`, which uses the registered `rt_mem_harden_check`
spelling), so it is filed here rather than fixed. Next step: instrument the
interpreter's extern call site and find which resolver rejects a name the shared
map contains.

## Evidence

Verified with a freshly built seed (`src/compiler_rust/target/release/simple`,
passed via `SIMPLE_TEST_BINARY`; `bin/release/**` deliberately not clobbered —
it is shared with concurrent sessions and is a seed, per
`.claude/rules/bootstrap.md`):

```
SPEC FILE VERDICT: harden_backend_parity_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
SPEC FILE VERDICT: guard_backend_parity_spec.spl  declared>=4 executed=4 passed=4 failed=0 dropped=0
```

Against the pre-existing deployed binary both are RED (4/5 and 3/4), so the
green depends on the registration fix, not on the assertion edits alone.


---

# Original report (retained verbatim)

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
