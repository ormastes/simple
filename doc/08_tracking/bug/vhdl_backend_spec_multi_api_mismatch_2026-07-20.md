# vhdl_backend_spec: multiple genuine API mismatches after import/rename fixes (22 failures remain)
## Triage 2026-11-25 — still OPEN; repro path updated, 24 failures at release/1.0.0 HEAD

The filed repro target `.spipe_matchers_vhdl_backend_spec.spl` was a
generated artifact, untracked in `83ae6d31588`; the live spec is
`test/01_unit/compiler/backend/vhdl_backend_spec.spl`. Re-run at
release/1.0.0 HEAD (Windows x86_64, pinned `bin/simple.exe` v1.0.0-rc.1,
`--mode=interpreter`; the 152 `@representation_boundary` lines the seed
rejects were temporarily stripped for the probe and restored after):
**58 examples, 34 passed, 24 failed**, exit 1. Movement vs the filed 22:
the dead-import and `lower_module`-missing causes are gone at HEAD
(`src/hardware/fpga_linux/` now exists so bare `hardware.` resolves, and
`HirLowering.lower_module` exists at
`src/compiler/20.hir/hir_lowering/_Items/module_build.spl:401`), but 6
examples still hit `class \`VhdlEntity\` has no field named \`vhdl\``
(the struct at `src/compiler/70.backend/backend/vhdl_backend.spl:243`
remains `{name, port_count}`), plus assertion-value mismatches and a
`VHDL combinational local ... must be a fixed scalar or record` lowering
rejection. Still genuine production-side VHDL-backend API mismatches, not
test typos; left OPEN for an owner per the original assessment.

### Prior header (2026-09-16)

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Context

`test/01_unit/compiler/backend/.spipe_matchers_vhdl_backend_spec.spl` had two
value-preserving stale-test issues that were fixed in-place (both verified to
genuinely improve the pass count, not just silence errors):

1. **Dead import prefix** (line 22): `use hardware.fpga_linux.riscv_fpga_linux.{RiscvFpgaLane}`
   does not resolve (bare `hardware.` maps to `src/hardware/`, which doesn't
   exist) — changed to `use std.hardware.fpga_linux.riscv_fpga_linux.{RiscvFpgaLane}`
   (`std.` maps to `src/lib/`, and the real file is
   `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`). This alone went from
   "no examples executed" (module wouldn't resolve at all) to 13/58 passing.

2. **Enum variant rename**: 43 call sites used `MirTerminator.Return(...)`, but
   `src/compiler/50.mir/mir_instructions.spl:570` defines the variant as
   `Ret(value: MirOperand?)`, not `Return`. Bulk-renamed all 43
   `MirTerminator.Return(` → `MirTerminator.Ret(` (mechanical, argument lists
   unchanged). This went from 13/58 to 36/58 passing.

## Remaining 22 failures — genuine API mismatches, NOT test-only fixable

After both fixes, `SIMPLE_RUST_SEED_WARNING=0 timeout 90
bin/release/x86_64-unknown-linux-gnu/simple test
test/01_unit/compiler/backend/.spipe_matchers_vhdl_backend_spec.spl
--no-session-daemon` still reports `Passed: 36, Failed: 22`, spanning several
distinct root causes in production compiler source, each needing an owner
familiar with the VHDL backend / HIR-lowering refactor history to resolve
(NOT attempted — out of test-shard scope, and the fixes are not one-liners):

1. **`class \`VhdlEntity\` has no field named \`vhdl\`` (6 examples)** — e.g.
   `"lowers payload-free variants of payload enums with default payload
   fields"`, `"...with the payload operand"`, `"projects payload enum tag and
   payload fields from tagged records"`, `"switches on payload enum tags while
   projecting payload fields"`, `"lowers unit-return hardware entities without
   result ports"`, `"lowers payload-free variants of payload enums inside
   processes"`. The spec constructs/reads a `.vhdl` field on `VhdlEntity` that
   doesn't exist in the current struct definition.

2. **`method \`lower_module\` not found on type \`HirLowering\`` (7 examples)**
   — e.g. all the `"lowers ... hardware bitfield ..."` cases and `"lowers
   generated rv32 decode helpers..."`. Several of these also print a
   `[parser_error] line N:M: expected type annotation` just before the
   semantic error, suggesting the fixture source string passed to
   `HirLowering` may itself be stale/malformed in addition to the missing
   method.

3. **`semantic: type mismatch: cannot convert object to int` (3 examples)** —
   `"rejects anonymous hardware tuple outputs before VHDL emission"`,
   `"rejects helper name collisions after sanitization"`, `"rejects
   unsupported helper memory behavior with a specific diagnostic"`.

4. **`semantic: class \`MirOperand\` has no field named \`id\`` (1 example)** —
   `"switches on payload enum tags inside combinational processes"`.

5. **Assertion value mismatches (not missing-symbol errors, 2 examples)** —
   `"resolves vhdl by backend name"` (`expected nil to equal true`) and
   `"compiles tuple aggregates through a generated tuple record type"`
   (`expected false to equal true`) — these look like real behavioral
   regressions in `backend_for_name`/tuple-aggregate lowering, not typos.

6. **Generated-VHDL string mismatches (2 examples)** — `"compiles payloadless
   enum aggregates to variant literals"` and `"emits called pure
   combinational helpers as package functions"` — expected output starts with
   `library ieee;\nuse ieee.std_logic_1164.all;` but actual output differs
   (not shown in this triage pass; needs a full diff).

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/compiler/backend/.spipe_matchers_vhdl_backend_spec.spl \
  --no-session-daemon
```

## Affected specs

- `test/01_unit/compiler/backend/.spipe_matchers_vhdl_backend_spec.spl` (import
  path and `Ret` rename fixed in-place; 22/58 examples still fail on genuine
  VHDL-backend/HIR-lowering API mismatches enumerated above)

