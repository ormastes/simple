# `rt_mem_harden_check` silently returns 0 under cranelift — the check symbol diverges per backend

- **Filed:** 2026-08-02
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  registered as an alias of `rt_mem_harden_check` in
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, so both spellings
  resolve on the JIT lane and neither silently returns 0. The premise that the
  divergence was interpreter-vs-C-linkage was also wrong: the JIT resolves
  externs through the same Rust table, so this was a registration omission.
  One residual remains — the `_native` spelling is still rejected under
  `SIMPLE_EXECUTION_MODE=interpreter`. Both are written up in
  `mem_infra_parity_specs_cranelift_arm_demotes_to_interpreter_2026-08-09.md`.
- **Severity:** high (silent false-negative in a safety-detection API)
- **Evidence tier:** Rust seed (`bin/simple`; bootstrap-identity probe = 0). Anything
  only the self-hosted binary can settle is DEFERRED.

## Summary

The harden write-after-free detector is exposed under **two different names**,
and neither backend accepts the other's spelling:

| backend | working extern | behaviour of the OTHER spelling |
|---------|----------------|---------------------------------|
| interpreter | `rt_mem_harden_check` | `rt_mem_harden_check_native` → hard error: `semantic: unknown extern function` |
| cranelift | `rt_mem_harden_check_native` | `rt_mem_harden_check` → **silently returns 0, forever** |
| llvm (native-build) | *neither* | link error: `undefined symbol: rt_mem_harden_check_native` |

The cranelift row is the dangerous one. `rt_mem_harden_check` is the name the
interpreter registers (`interpreter_extern/mod.rs:311`) and the name every
existing `.spl` caller and doc uses. Under cranelift that symbol does not
resolve — the Rust function is a *local* symbol (`t`), not an exported one, and
the C runtime only exports `rt_mem_harden_check_native` — and an unresolved
extern under the JIT returns 0 instead of failing.

**0 is exactly the value that means "no corruption detected."** So a caller who
enables `SIMPLE_MEM_HARDEN=1`, commits a write-after-free, and calls the
documented API gets a clean bill of health on cranelift.

## Reproduction

`nm` on the seed binary shows the asymmetry directly:

```
$ nm bin/release/x86_64-unknown-linux-gnu/simple | grep harden
00000000021d2700 T rt_mem_harden_check_native
0000000001446b70 t simple_compiler::interpreter::interpreter_extern::memory::rt_mem_harden_check
```

One global `T`, one local `t`. There is no global `rt_mem_harden_check`.

Behavioural probe (both externs declared in one file, run under cranelift with
`SIMPLE_MEM_HARDEN=1`, after a real write-after-free):

```
check_plain=0        <- rt_mem_harden_check()        WRONG, tampering happened
check_native=1       <- rt_mem_harden_check_native() correct
```

With `SIMPLE_MEM_HARDEN` unset both report 0, so `check_plain` is
indistinguishable from a working check that found nothing.

That the cranelift quarantine itself is real (i.e. this is purely a naming
defect, not a missing capability) is established by
`test/fixture/mem_infra/harden_tamper_probe.spl`: three blocks freed, then
tampered one at a time, gives `t0=0 t1=1 t2=2 t3=3` under
`rt_mem_harden_check_native` and a flat `0,0,0,0` with the knob off.

## Why the shipped fixture missed it

`test/fixture/mem_infra/harden_poison_workload.spl` uses the interpreter
spelling. Under cranelift it therefore printed `tampered_check=0` after a
genuine write-after-free. That was originally read as "harden does not work on
cranelift", and nearly caused the `harden` capability row to be marked false on
a backend where the protection is in fact fully functional — the mirror of the
false-positive this whole lane exists to remove.

## Recommended fix

Export a C alias in `src/runtime/runtime_memory.c` so the documented spelling
resolves on every backend that has the quarantine:

```c
int64_t rt_mem_harden_check(void) { return rt_mem_harden_check_native(); }
```

Cranelift then resolves the canonical name, the interpreter is unaffected (it
dispatches through its own table, and its Rust symbol is local), and native
builds keep failing **closed** at link time because `runtime_memory.o` is not in
the `simple-core` runtime lane at all.

Not done in this change because the shared working tree could not be rebuilt:
`src/compiler_rust/compiler` does not currently compile there (another lane has
in-flight edits referencing `hir/lower/option_pattern_shape_diag.rs` and
`pattern_case_naming.rs`, neither of which exists), so the alias could not be
verified end-to-end. It must not be landed unverified — a second unverified
capability claim is the exact failure mode being corrected.

## Related

- `src/lib/common/mem_infra/config.spl` — the `harden` capability row, corrected
  on 2026-08-02 to `interpreter: true, cranelift: true, llvm: false`
- `test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl` — the parity spec
- `doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md`
  — the sibling `guard` row correction

## Secondary finding: the JIT still silent-nils an unresolved extern

The root enabler is that an unregistered/unresolvable `@extern fn` returns 0/nil
under the JIT rather than erroring. The interpreter fails loudly for the same
program (`semantic: unknown extern function`) and the native linker fails loudly
too (`undefined symbol`), so cranelift is the only backend that turns a missing
symbol into a plausible-looking value. Any extern whose "nothing wrong" answer is
0, false, or empty is silently unsafe on cranelift for this reason.
