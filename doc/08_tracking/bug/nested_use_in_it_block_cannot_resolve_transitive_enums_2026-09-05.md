# `use` nested inside an `it` block cannot resolve transitively-reached enums

- **Filed:** 2026-09-05
- **Status:** OPEN
- **Lane:** `src/compiler_rust/target/debug/simple run <spec>` (Rust seed interpreter)

## Symptom

A `use` statement written INSIDE an `it` block imports the named symbol
successfully, but any enum that the imported module reaches through its own
`use` graph is not in scope when that module's code runs:

```
✗ W3.4 board flow ...
  semantic: enum `Xlen` not found in this scope
✗ W3.x — pending (headline)
  semantic: enum `MirTypeKind` not found in this scope
```

Both enums are imported explicitly and correctly by the modules that use them:

- `src/compiler/80.driver/riscv_fpga_bundle.spl:22`
  `use std.hardware.fpga_linux.riscv_fpga_linux.{XilinxBoardProfile, Xlen}`
- `src/compiler/70.backend/backend/unified_kernel_emit.spl:25`
  `use compiler.mir.mir_types.{MirLocal, MirType, MirTypeKind, LocalKind}`

## Reproduction / discrimination

Same binary, same two modules, same call arguments, differing ONLY in where the
`use` line sits:

| `use` placement | result |
|---|---|
| inside the `it` block | `semantic: enum <E> not found in this scope` |
| module top level | passes; real PTX/OpenCL/VHDL and a real board bundle are produced |

Measured 2026-09-05 with
`src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/sycl_parity_unified_kernel_plan_spec.spl`
(nested: 4 examples / 2 failures) versus an equivalent probe spec with the same
imports hoisted to file scope (3 examples / 1 failure, and that one failure was
an unrelated `case F16:` arm, not a scope error).

A nested `use` of a module with NO transitive enum dependency
(`compiler.frontend.descriptive_kernel_lowering`) works fine, which localises
the defect to transitive resolution rather than to nested `use` as such.

## Impact

Specs that deliberately pin a promised entry point with a nested `use` — the
plan-acceptance lane's forcing-function idiom — cannot import any module that
touches MIR or a hardware profile enum. The failure is reported as a semantic
error attributed to the imported module, which reads as a defect in that module
rather than in the import path.

## Workaround in place

`test/03_system/plan_acceptance/sycl_parity_unified_kernel_plan_spec.spl` hoists
the two affected `use` lines to file scope, with a comment pointing here. No
assertion was changed. Revert the hoist once this is fixed.

## Unblock condition

A nested `use` resolves its imported module's transitive enum imports
identically to a file-scope `use`.
