# riscv64 in-guest: MIR lowering rejects `main` with a raw-0 HirType kind

- Status: **OPEN** — the current blocker for goal item 1 row 2, and a NEW one.
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
  row 2 (`buildrun`)
- Measured under real OpenSBI v1.4 `-bios fw_payload` (never `-kernel`, never
  `isa-debug-exit`), nonce `41d7bd8ce8c848bd`, gate selftest OK (23 fixtures).

## Symptom, measured

```
[buildrun] phase=hir-ok
[buildrun] FAIL mir lowering error: E-MIR-TYPE-ZeroKind: lower_type received a
  well-formed HirType whose `kind` field is raw 0 (never written) while
  lowering 'main' -- fix the PRODUCER that left kind unset, not lower_type
```

## Why this is genuinely NEW, not the old blocker resurfacing

The previous blocker
(`riscv64_freestanding_toplevel_decl_walk_names_both_functions_add_2026-09-01.md`)
was that `main` never existed at all: the top-level walk converted declaration 0
twice, so `parsed.functions` held only `add`, `lookup_or_invalid("main")`
answered `-1`, and the run stage reported "module has no main function". That is
fixed and verified. `main` now exists, lowers to HIR, and is being lowered to
MIR — the error message names it. This is the **first time `main` has been
observed downstream on this row.**

## Lead, NOT yet measured

The program's `main` is declared `fn main():` — no return type. The suspicion is
that the producer of the implicit unit/void return `HirType` leaves `kind` at
its zero value on the freestanding path, and that `add` is unaffected because it
declares `-> i64` explicitly. **This is a hypothesis and must be measured before
being acted on**; the previous blocker on this row cost three sessions precisely
because four successive plausible hypotheses were assumed rather than probed.
The productive technique there, after external probes kept refuting each theory,
was instrumenting the suspect function's own branch decisions into an in-memory
trace and printing it from the entry — the same approach applies here to
whichever producer builds that HirType.

The diagnostic itself is well-behaved and fails closed with an accurate message
naming the function; it is not the defect.

## Round 1 MEASURED (2026-09-01, nonce 2ca90c8db5c2a8ff, real OpenSBI v1.4 fw_payload)

Probe in the image verified before reading the transcript
(`grep -aF "PROBE calls=" build/os/riscv64_interp/buildrun/kernel.elf` -> YES).

```
[buildrun] phase=hir-ok
[buildrun] FAIL mir lowering error: E-MIR-TYPE-ZeroKind: ... while lowering 'main'
  [PROBE calls=5 disc=0 discStr=3560734392 discInt=2375492728
   discUnit=406810393 strHit=Y intHit=Y kindnil=N]
```

### What this REFUTES

1. **The `fn main():` implicit-return lead in this record is REFUTED.**
   `calls=5` is the 5th `lower_type` entry of the run. `add(a: i64, b: i64) -> i64`
   accounts for calls 1-3 (two params, one return) and `main`'s Unit return type
   for call 4 — all four returned normally. The failing type is reached from
   INSIDE `main`'s body, not from its signature.

2. **"while lowering 'main'" never meant `main` in the first place.** `fn_ctx` is
   `self.current_function_names[len-1]`, and `current_function_names` is set once
   in `lower_module` to the WHOLE module's function-name list
   (`module_lowering.spl:1164`) — it is not a stack. It always renders the last
   function in the module. The diagnostic's function attribution is not evidence
   and should be repaired.

3. **Enum construction and matching are NOT broken in-guest.** `strHit=Y` and
   `intHit=Y`: a locally constructed `HirTypeKind.Str` / `HirTypeKind.Int(64,true)`
   matches its own arm. So the `case _` fallthrough is a property of the OBJECT
   handed in, not of the match machinery.

### What this ESTABLISHES as a new, separate defect

**`rt_enum_discriminant` answers garbage in-guest.** For locally constructed,
provably well-formed enum values it returned `discStr=3560734392`,
`discInt=2375492728`, `discUnit=406810393` — three different pointer-sized
values where the declaration order requires small constants (`Int`=0, `Str`=4,
`Unit`=5). These are not discriminants.

This matters beyond the diagnostic, because `lower_type` PRE-DISPATCHES on it
(`function_lowering.spl:846-880`): Dict, Named, Any and Optional are each
selected by `_sffi_hir_type_discriminant(type_.kind) == <disc of a freshly
constructed exemplar>`. With both sides garbage and allocation-dependent, those
four pre-dispatch arms are dead in-guest — they can neither fire correctly nor
be trusted if they do.

Related divergence found by reading both runtimes (static, not yet measured):
the riscv64 baremetal `rt_enum_discriminant`
(`baremetal_runtime_core.inc.c:1260`) returns **0** for a non-enum, while the
hosted one (`src/runtime/runtime.c:1567`) returns **-1**. `0` collides with the
legitimate discriminant of `HirTypeKind.Int`, so on this target "not an enum"
and "Int" are indistinguishable. `rt_enum_id` has the same 0-vs-(-1) split.
The observed `disc=0` for the failing `type_.kind` is that failure path.

### Still open

Which of `main`'s body constructs produces a zeroed `HirType` at call 5.
`type_.kind` reads raw 0 while `type_` itself is a live object, so the `kind`
slot was never written or was overwritten with 0. Next probe: tag the
`lower_type` CALL SITE, since the object carries nothing else readable.
