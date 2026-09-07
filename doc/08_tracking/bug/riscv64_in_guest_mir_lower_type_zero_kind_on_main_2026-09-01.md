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

### CORRECTION to round 1 (same day, before acting on it)

**The "rt_enum_discriminant answers garbage" claim above is WITHDRAWN. It was
wrong, and the error was mine: I compared the measured values against
declaration indices without checking what this compiler actually uses.**

Simple discriminants are **hashes of the variant NAME**, not declaration
indices — `simple_runtime::value::hash_variant_discriminant`, used consistently
by the HIR lowerer (`hir/lower/expr/mod.rs:102`), the interpreter's enum SFFI
(`interpreter_extern/enum_sffi.rs:26`) and stmt lowering
(`hir/lower/stmt_lowering.rs:2802`, "All enums use hashed variant name
discriminants consistently"). So `discStr=3560734392`, `discInt=2375492728`,
`discUnit=406810393` are three correct, distinct u32 name hashes. Expecting
`Int`=0 / `Str`=4 / `Unit`=5 was the mistake; nothing about them is corrupt,
and `lower_type`'s four discriminant pre-dispatch arms are FINE in-guest —
they compare a hash against a hash of a freshly built exemplar.

What survives from round 1, unchanged and still measured:

* `calls=5` — the failure is inside `main`'s BODY; the implicit-return lead
  stays refuted.
* `strHit=Y` / `intHit=Y` — enum construct and match work in-guest.
* `kindnil=N` with `type_.kind == 0` — the `kind` slot reads raw 0.
* `fn_ctx` is not real function attribution (see above).
* The hosted-vs-baremetal `rt_enum_discriminant` / `rt_enum_id` failure
  sentinel really does differ (hosted `-1`, riscv64 baremetal `0`). With hashed
  discriminants a 0 collision is improbable rather than certain, so this is a
  latent divergence worth aligning, NOT the cause of this bug. Recorded so the
  next reader does not re-derive it, and explicitly de-escalated.

## RESOLVED (2026-09-01, nonce 4d2ef4c711455c53) — and the row's NEXT blocker

Root cause: `MirLowering.match_result_mir_type`
(`_MirLoweringExpr/switch_operators_calls.spl`) extracted its `HirType?` with
`if val expected_found = expected:` and dereferenced `expected_found.kind`.
On riscv64 freestanding that extraction ENTERS its body for an ABSENT optional
and binds a zeroed object. Localised by two boots: round 1 gave `calls=5`
(inside `main`'s body, refuting this record's own implicit-return lead) and
round 2 tagged all 61 external `lower_type` call sites, naming
`switch_operators_calls:839`. Reached from the value-position `if total == 42:`
in the interpreted program's `main`.

Fixed by guarding the bound name before the dereference and routing a
miscompiled extraction to the same `MirType.i64()` the function already returns
for an absent expected type. Hosted behaviour unchanged (measured). Pinned by
`scripts/check/check-rv64-match-result-type-guarded.shs` (RED at the fix's
parent, GREEN at the fix, 8 fatal selftest fixtures, wired in
`.github/workflows/repo-hygiene.yml`).

MEASURED in-guest after the fix, real OpenSBI v1.4 `-bios fw_payload`:

```
[buildrun] phase=hir-ok
[buildrun] phase=mir-ok functions lowered        <-- FIRST TIME EVER
[buildrun] running the built program
[buildrun] FAIL run error: function 'add' not found
```

**The BUILD half of row 2 is now green in-guest.** Real MIR lowering runs over
real source and produces real functions. The row is still RED, at a new and
different blocker in the RUN half: the in-guest interpreter cannot resolve the
callee `add` from `main`'s body. That is a separate defect — row 1
(`interpreter_hello`) is green but its program never makes a cross-function
call, so nothing on this lane had exercised callee resolution before. Filed as
the row's next blocker; it is NOT a regression of this fix.
