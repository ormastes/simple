# Frozen stage2: the MIR local-symbol hash index buckets a binding by a tagged/decoded id, so every `val`-then-use is "undefined variable"

- **ID:** stage2_local_symbol_index_bucket_tagged_id_2026-11-03
- **Priority:** P1 (phase 3: no stage3-compiled program with a local variable lowers; `val s = "x"; print(s)` fails MIR)
- **Status:** open. Source workaround landed in `src/compiler/50.mir/mir_lowering_types.spl` (`bind_local` mirrors every
  binding into `local_map`; `find_local` consults it after an index miss). The stage2 miscompile itself is not fixed.

## Symptom
Stage3 (`s3_fable10.exe`, objects by stage2 ef0681fc0e1) compiling `fn main(): val s = "x"; print(s)` reports
`MIR lowering error: undefined variable` at `print(s)`. hello (no locals) compiles.

## Root cause (stack-only minidump veh_13196 at MirLowering.error entry, frame lower_expr_impl)
`bind_local` stores the id in `local_symbol_ids` (`[i64]`, read back as 8) and its slot into the open-addressed
`local_symbol_index_slots` (capacity 16). The dump shows the binding in bucket **1** while `local_symbol_slot(8)` probes
bucket `8 % 16 = 8` (empty, read as -8: the `-1` fill came back with its tag bits masked). Bucket 1 is `(8<<3|1) % 16`
(the tagged encoding of 8) and also `(8>>3) % 16`: in stage2-compiled code an i64 that round-trips through an `[i64]`
array (`rebuild_local_symbol_index` reads `self.local_symbol_ids[slot]` before `% capacity`) does not agree with the same
value held directly, so insert and lookup hash different numbers. `local_map: Dict<i64, LocalId>` was empty (the legacy map
nothing wrote any more), which is why the lookup had no second chance.

## Workaround
Mirror every `bind_local` into `self.local_map` (runtime dict keys are canonicalized on both set and get) and let
`find_local` fall back to it after the index miss. `local_map` is already reset per function together with the index
(`function_lowering.spl:358-359`) and no path removes bindings, so the mirror cannot resolve a stale name.

## Removal condition
A stage2 whose `[i64]` element reads agree with direct i64 values (any seed-built stage2 from release/1.0.0 at or after
this change); then the mirror is redundant and can be dropped.

## Behaviour note (review of fefac1c2128)
The fallback also resolves bindings that other sites write straight into `local_map` without `bind_local`
(e.g. the catch-pattern `Binding` at expr_dispatch.spl:7447). Under a correct compiler those used to answer
`LocalId(id: -1)` from `find_local`; now they resolve. That is the intended semantics of the mirror, but it is a change.
