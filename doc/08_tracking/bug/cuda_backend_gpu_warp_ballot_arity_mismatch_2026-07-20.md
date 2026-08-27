# CUDA backend requires 2 args for gpu_warp_ballot but codegen (and the intrinsic's real signature) only uses 1

**Status:** Open
**Category:** GENUINE-BUG (backend arity-validation bug, precisely root-caused)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 60 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl --no-session-daemon
```

```
  ✗ emits vote.sync.ballot.b32 for gpu_warp_ballot
    semantic: called unwrap on Err: CompileError(message: CUDA intrinsic
    'gpu_warp_ballot' requires 2 arguments, phase: backend (cuda), location:
    nil, has_location: false)
```

## Minimal repro (spec unedited, sole failure remaining after unrelated `.?`
fix in the same file)

`test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl:151-157`
builds a 1-argument `gpu_warp_ballot` MIR intrinsic call:
```
fn warp_ballot_block() -> MirBlock:
    MirBlock(
        id: BlockId.entry(),
        label: Some("entry"),
        instructions: [MirInst(kind: MirInstKind.Intrinsic(Some(LocalId(id: 0)), "gpu_warp_ballot", [MirOperand.copy(LocalId(id: 1))]), span: nil)],
        terminator: MirTerminator.Ret(nil)
    )
```
and the equivalent OpenCL-backend test at line 208-211 using the exact same
`warp_ballot_block()` fixture PASSES (`sub_group_ballot(` is emitted). Only
the CUDA-backend test at line 282-287 fails, because the CUDA backend's arity
validator rejects the 1-arg call.

## Root cause (precisely identified)

`src/compiler/70.backend/backend/cuda_backend.spl`:

1. The actual CUDA codegen for `gpu_warp_ballot` (lines 734-738) only reads
   **one** argument:
   ```
   case "gpu_warp_ballot":
       val d9 = "%r{dest.unwrap().id}"
       val pred9 = self.operand_to_reg(builder, args[0])
       builder.emit_reg_decl(d9, PrimitiveType.I32)
       builder.emit_line("vote.sync.ballot.b32 {d9}, {pred9}, 0xffffffff;")
   ```
   (`args[1]` is never referenced; the sync mask `0xffffffff` is hardcoded,
   not taken from an operand.)

2. But `validate_intrinsic` (lines 1013-1023) bundles `"gpu_warp_ballot"`
   into the SAME match arm as the genuinely-2-arg shuffle-family intrinsics:
   ```
   case "min" | "max" | ... | "gpu_warp_shuffle" | "gpu_warp_shuffle_down"
      | "gpu_warp_shuffle_up" | "gpu_warp_shuffle_xor" | "gpu_warp_ballot"
      | "gpu_warp_broadcast" | ... : required_args = 2
   ```
   forcing `required_args = 2` for `gpu_warp_ballot` even though its own
   codegen case only consumes `args[0]`.

3. This also contradicts the intrinsic's documented signature in
   `src/compiler/10.frontend/parser_types_expr.spl:299`:
   `WarpBallot   # gpu_warp_ballot(pred)` — a single-parameter intrinsic.

4. The OpenCL backend (`src/compiler/70.backend/backend/opencl_backend.spl:737`)
   handles `gpu_warp_ballot` correctly with 1 argument, confirming the CUDA
   backend's `required_args = 2` for this specific case is the outlier/bug,
   not the test fixture.

## Suggested fix

In `src/compiler/70.backend/backend/cuda_backend.spl`, move `"gpu_warp_ballot"`
out of the `required_args = 2` match arm (line ~1019) into a `required_args = 1`
arm (alongside `"gpu_lane_id"`-style single-operand intrinsics, though note
`gpu_lane_id`/`gpu_warp_id`/`gpu_warp_size` are 0-arg — `gpu_warp_ballot` needs
its own `required_args = 1` case, e.g. add `"gpu_warp_ballot"` to a new/expanded
1-arg arm alongside `"sin" | "cos" | ...` which already uses `required_args = 1`).

This is a one-line-ish behavioral fix to `src/compiler/70.backend/backend/cuda_backend.spl`
(not an import/rename), so it is out of scope for this triage pass per the
campaign's src/** edit restriction — filed here instead.

## Affected specs

- `test/01_unit/compiler/codegen/subgroup_intrinsics_contract_spec.spl` (1 of 24 examples: "emits vote.sync.ballot.b32 for gpu_warp_ballot")
