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

## Addendum 2026-11-11 (lane ne17) — mechanism re-confirmed LIVE; surface symbol changed

Fresh seed 46fe8f6b6def (Windows, worktree simple-p3-ne17-20261111):

1. Minimal synthetic repro (one module importing a one-enum module; spec
   nests the `use` inside the `it`) PASSES — a single-level transitive enum
   now resolves. The 2026-09-05 failure needs the deeper real import graph.
2. Real spec, re-nested (the two hoisted `use` lines moved back into their
   `it` blocks, otherwise identical): the two affected `it`s FAIL with
   `semantic: function 'vhdl_kernel_accepts' not found` — a TRANSITIVE import
   of `compiler.backend.unified_kernel_emit` (its own
   `use compiler.backend.vhdl.vhdl_kernel_entity.{..., vhdl_kernel_accepts}`)
   fails to resolve when the module is pulled in through the nested-use
   path. Same mechanism as the recorded `enum Xlen / MirTypeKind not found
   in this scope`; the module graph changed since 2026-09-05 so a function
   surfaces first instead of the enums. 5 examples: 3 pass, 2 fail.
3. Control (byte-identical file with the two `use` lines hoisted to top
   level) does not compile at all on the current tree:
   `error: semantic: duplicate impl for trait 'Codegen' and type
   'OpenClBackend'` — a co-compiled-closure collision (owner decision
   2026-11-09 family), 0 examples executed. So the hoist workaround is
   currently unevaluable end-to-end, and the nested-use defect is confirmed
   by the only runnable shape. Do NOT revert the hoist in the spec.

Fix lives in the module loader / import-resolution of the running engine
(seed here; pure-Simple frontend parity unverifiable on this lane).
**Grant:** seed-lane fix, with the spec's nested-use revert as the
acceptance run.
