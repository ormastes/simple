# VHDL MIR Backend ABI Parity Task

Date: 2026-04-23
Task ID: VHDL-PARITY-016
Owner: Rust MIR backend parity agent
Status: Pending

## Goal

Move the labeled multi-output and direct hardware-call behavior from the
Simple source facade into the Rust MIR VHDL backend. The target backend is
`src/compiler_rust/compiler/src/pipeline/codegen.rs`, where `generate_vhdl`
currently emits one entity per MIR function with a single `result_out` output.

This pass is analysis only. Rust implementation is intentionally deferred.

## Worker-Safe Implementation Breakdown

The implementation should be split by file ownership so multiple Rust workers
can proceed without stepping on each other. Workers must not edit another
worker's files without first rebasing their local task plan against completed
changes.

### Worker 1: MIR Type View Plumbing

Primary files:

- `src/compiler_rust/compiler/src/mir/function.rs`
- `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`
- `src/compiler_rust/compiler/src/mir/lower/mod.rs`
- `src/compiler_rust/compiler/src/hir/type_registry.rs`
- `src/compiler_rust/compiler/src/pipeline/codegen.rs`

Exact source tasks:

1. Confirm the existing data flow before editing:
   - `HirType::LabeledTuple(Vec<(String, TypeId)>)` already exists in
     `src/compiler_rust/compiler/src/hir/types/type_system.rs`.
   - `HirModule` owns `pub types: TypeRegistry` in
     `src/compiler_rust/compiler/src/hir/types/module.rs`.
   - `MirLowerer::lower_module` receives `hir: &HirModule`, sets
     `self.type_registry = Some(&hir.types)`, creates `let mut module =
     MirModule::new();`, then lowers each `HirFunction`.
   - `MirFunction` already preserves `return_type: TypeId` and each parameter's
     `MirLocal.ty`, but `MirModule` does not preserve the registry needed to
     interpret those IDs after HIR lowering.
2. In `src/compiler_rust/compiler/src/hir/type_registry.rs`, add `Clone` to
   `TypeRegistry` only. `TypeIdAllocator` is already `#[derive(Debug, Clone)]`,
   and `HirType` is already cloneable, so this should be a one-line derive:
   `#[derive(Debug, Default, Clone)]`.
3. In `src/compiler_rust/compiler/src/mir/function.rs`, add
   `pub type_registry: crate::hir::TypeRegistry` to `MirModule`. Initialize it
   in `MirModule::new()` with `crate::hir::TypeRegistry::new()`. This keeps old
   tests and hand-built MIR modules valid because they still call `new()`.
4. In `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`, immediately
   after `let mut module = MirModule::new();` and `module.name = hir.name.clone();`,
   set `module.type_registry = hir.types.clone();`. Do not change
   `MirLowerer::with_type_registry` or the lowering public API; those references
   remain for unit/refinement/dynamic-dispatch lowering.
5. Keep `CompilerPipeline::compile_file_to_vhdl` unchanged at the boundary:
   `let vhdl = generate_vhdl(&mir_module)?;`. Worker 1 should not thread
   `HirModule` or `TypeRegistry` through `compile_file_to_vhdl`; the MIR module
   becomes the carrier.
6. In `src/compiler_rust/compiler/src/pipeline/codegen.rs`, introduce a local
   binding at the top of `generate_vhdl`:
   `let types = &module.type_registry;`, then pass `types` to VHDL helpers. Make
   the signature changes mechanically:
   - `emit_vhdl_function(out, func, types)`
   - `lower_vhdl_block_instructions(func, state, block, types)`
   - `lower_vhdl_return_block(func, state, id, types)`
   - `lower_vhdl_instruction(func, state, inst, types)`
   - `reg_expr_for_type(reg_expr, reg_int_const, reg, ty, types)`
   - `vhdl_type(ty, types)`
   - `vhdl_int_literal(value, ty, types)`
7. Keep `vhdl_type(TypeId, &TypeRegistry)` scalar-only in Worker 1. It should
   preserve current behavior for built-in `I32`, `I64`, and `BOOL`. For any
   non-scalar, include resolved type detail when available:
   `types.get(ty)` can show `HirType::Tuple` or `HirType::LabeledTuple` in the
   error, but Worker 1 must not implement tuple VHDL ports yet.
8. Do not alter `MirFunction` return/parameter fields, MIR instruction shapes,
   or `VhdlLowerState` in Worker 1. Later workers own return ABI, tuple
   decomposition, virtual aggregates, and hardware call lowering.

Tests:

- Add a focused Rust test under the existing MIR lowering test area, preferably
  `src/compiler_rust/compiler/src/mir/lower/tests/`, that constructs or lowers a
  tiny HIR module with a registered `HirType::LabeledTuple` return type and
  asserts:
  - `mir_module.functions[0].return_type` equals the HIR function return
    `TypeId`;
  - `mir_module.type_registry.get(return_type)` returns
    `Some(HirType::LabeledTuple(fields))`;
  - field labels and field `TypeId`s are preserved in order.
- Add a VHDL helper-level regression only if convenient: a hand-built
  `MirModule` with `TypeRegistry::new()` should still emit the same scalar VHDL
  for a scalar `bool` or `i64` function. Avoid end-to-end tuple VHDL assertions;
  Worker 2 owns ABI behavior.
- Run `cargo test -p simple-compiler mir` or the narrower MIR lowering test
  target that contains the new case.
- Run `cargo check -p simple-compiler`.

Worker 1 must land first because every later worker depends on resolved tuple
field names and field types.

### Worker 2: Return ABI and Entity Port Emission

Primary file:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`

Exact source tasks:

1. Add backend-local structs immediately above `VhdlLowerState`:
   - `VhdlPort { source_name: String, vhdl_name: String, ty: TypeId, direction: VhdlPortDirection }`
   - `VhdlPortDirection::{In, Out}`
   - `VhdlReturnField { label: Option<String>, vhdl_name: String, ty: TypeId, tuple_index: Option<usize> }`
   - `VhdlReturnAbi::{Scalar(VhdlReturnField), Tuple(Vec<VhdlReturnField>)}`
2. Add `fn vhdl_return_abi(func: &MirFunction, types: &TypeRegistry) -> Result<VhdlReturnAbi, CompileError>`.
   The helper must inspect `types.get(func.return_type)` after Worker 1 lands.
3. Implement return classification:
   - `None` or scalar `HirType`: one output named `result_out`, with
     `tuple_index: None`;
   - `HirType::Tuple(fields)`: outputs named `out0`, `out1`, etc., with
     `label: None` and `tuple_index: Some(index)`;
   - `HirType::LabeledTuple(fields)`: outputs named from labels, with
     `label: Some(label.clone())` and `tuple_index: Some(index)`.
4. Reject tuple output fields whose element type is not scalar-lowerable by
   `vhdl_type(field_ty, types)`. Diagnostic shape:
   `VHDL backend unsupported tuple output type in <function>.<field>: <type>`.
5. Add a shared sanitizer:
   `fn sanitize_unique_vhdl_ident(raw: &str, used: &mut HashMap<String, String>, context: &str) -> Result<String, CompileError>`.
   It must call existing `sanitize_vhdl_ident`, then reject if the sanitized
   name is already present for a different raw name. Diagnostic shape:
   `VHDL backend name collision in <context>: <left> and <right> both sanitize to <name>`.
6. Use the collision checker for entity names, input ports, and output ports.
   Check input and output ports in one shared `used_ports` map so a parameter
   cannot collide with a return label, for example `sum-value` and
   `sum_value`.
7. Replace direct `result_out : out <vhdl_type(func.return_type)>` emission in
   `emit_vhdl_function` with ABI output ports. Port semicolon handling must be
   list based, not branch based: build `Vec<VhdlPort>`, then emit `;` after all
   but the last port.
8. Keep scalar behavior byte-for-byte close to current output where possible:
   scalar functions still emit `result_out : out ...` and later Workers will
   preserve existing scalar assignment tests.
9. Keep `vhdl_type(TypeId, &TypeRegistry)` scalar-only for this worker. Tuple
   ports must be decomposed before calling it; packed tuple VHDL types are out
   of scope for Worker 2.
10. Do not modify return assignment lowering in this worker. Until Worker 3
    lands, tuple-return functions may emit ports but still fail later with a
    clear assignment-lowering diagnostic if exercised end-to-end.

Tests:

- Prefer inline tests in `src/compiler_rust/compiler/src/pipeline/codegen.rs`
  beside the existing VHDL tests unless those tests become too large.
- Add a labeled tuple return ABI test using source:
  `@hardware fn full_add(a: bool, b: bool, cin: bool) -> (sum: bool, cout: bool): ...`
  The test should assert `sum : out std_logic`, `cout : out std_logic`, and no
  `result_out` port in that entity after Worker 3 makes end-to-end generation
  possible. Before Worker 3, isolate `vhdl_return_abi` directly if necessary.
- Add an anonymous tuple return ABI test asserting deterministic `out0`,
  `out1` names for distinct scalar field types.
- Add a sanitized collision negative test for labels `a-b` and `a_b`, and a
  separate param/output collision negative test.
- Keep existing scalar tests:
  `vhdl_emits_combinational_adder_from_simple_source`,
  `vhdl_emits_typed_constants_unary_ops_and_const_compare`, and
  `vhdl_emits_simple_if_else_return_mux`.
- Run `cargo test -p simple-compiler vhdl`.
- Run `cargo check -p simple-compiler`.

Worker 2 must not implement call lowering.

### Worker 3: Tuple Return Assignment Decomposition

Primary file:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`

Exact source tasks:

1. Confirm the current MIR form before editing: tuple expressions lower in
   `src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` as
   `MirInst::TupleLit { dest, elements }`, and returns lower in
   `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` as
   `Terminator::Return(Some(dest))`. Labeled tuple expressions are already
   positional at MIR level; Worker 2's `VhdlReturnAbi` supplies field names and
   field types.
2. Add a backend-local tuple field record near `VhdlLowerState`:
   `struct VhdlTupleFieldExpr { index: usize, ty: TypeId, expr: String }`.
   Keep the type explicit; later call-lowering workers need the same metadata
   for virtual hardware-call aggregates.
3. Extend `VhdlLowerState` with
   `reg_tuple_fields: HashMap<u32, Vec<VhdlTupleFieldExpr>>`. Preserve this map
   in `Clone`, because the existing branch lowering clones the state for
   then/else arms.
4. Teach `lower_vhdl_instruction` to handle
   `MirInst::TupleLit { dest, elements }` by resolving each element register
   through `reg_expr_for_type(...)`. Derive each element type from
   `state.reg_ty[element]`; if absent, fall back to the corresponding field type
   from the destination/return ABI only when `dest` is the returned register.
   Store the ordered field vector in `reg_tuple_fields[dest.0]`; do not emit a
   packed VHDL tuple signal.
5. Add `fn return_output_exprs(...) -> Result<Vec<(String, String)>,
   CompileError>` that accepts a return register, `VhdlReturnAbi`, current
   `VhdlLowerState`, and the type registry. For scalar ABI, return
   `[(result_out, scalar_expr)]`. For tuple/labeled tuple ABI, require
   `reg_tuple_fields[reg.0]`, verify arity matches ABI fields, and pair each ABI
   output port with the positional tuple field expression.
6. Add `fn push_return_assignments(...)` that appends concurrent assignments
   for the vector from `return_output_exprs`, one line per output:
   `    <port> <= <expr>;`.
7. Replace `result_expr: Option<String>` in `emit_vhdl_function` with
   `return_assigns: Vec<String>` or a small `VhdlReturnAssignments` helper. Do
   not special-case scalar returns; scalar and tuple returns should both flow
   through `return_output_exprs`.
8. Update `lower_vhdl_return_block` to return the output-expression vector, not
   a single expression string. Its only supported terminator remains
   `Terminator::Return(Some(reg))`.
9. Update the existing entry-block branch special case. After cloning the base
   state and lowering each return arm, combine outputs by ABI field/port name:
   `sum <= then_sum when cond = '1' else else_sum;`. Reject branch arms whose
   output port lists differ; this indicates an ABI/lowering bug.
10. Keep all non-return tuple values virtual. If a tuple register is later used
   where a scalar expression is required, `reg_expr_for_type` should continue to
   fail with "no expression for vN" unless Worker 5 adds a supported virtual
   field-access path.

Tests:

- MIR unit test for returning `TupleLit(sum_expr, cout_expr)` into labeled
  output ports.
- GHDL smoke for a generated `full_add` entity with two output assignments.

Worker 3 depends on Worker 2.

### Worker 4: Hardware Function Selection and Direct Call Instances

Primary file:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`

Exact source tasks:

1. Add `fn is_vhdl_entity_function(func: &MirFunction) -> bool`, initially true
   only for functions with `func.attributes` containing `"hardware"`. Keep any
   all-non-main compatibility behavior behind a clearly named helper such as
   `is_legacy_vhdl_emit_candidate`, so the call-lowering path can require a
   real hardware entity boundary.
2. In `generate_vhdl`, build a deterministic entity table before emission:
   `BTreeMap<String, &MirFunction>` keyed by the unsanitized MIR function name.
   Reject duplicate sanitized entity names before emitting text.
3. Thread the entity table and type registry through:
   `emit_vhdl_function`, `lower_vhdl_block_instructions`,
   `lower_vhdl_return_block`, and `lower_vhdl_instruction`.
4. Emit only functions selected by `is_vhdl_entity_function`. Do not emit
   runtime helpers, pure software helpers, or `main` as entities. Later
   VHDL-PARITY-010 may lower eligible pure helpers as VHDL subprograms instead.
5. Extend `VhdlLowerState` with:
   - `instances: Vec<String>`;
   - `call_ordinal: usize`;
   - `reg_tuple_fields` from Worker 3 if not already present;
   - `declared_signal_names: BTreeSet<String>` or equivalent collision tracker.
6. Extend `lower_vhdl_instruction` for `MirInst::Call { dest, target, args }`.
   This codebase does not have a `CallTarget::Direct` variant; treat a call as
   hardware-direct only when `target.name()` exists in the entity table. Reject
   every other `MirInst::Call`, including names beginning with `rt_`, with a
   diagnostic such as `VHDL backend unsupported non-hardware call <name> in
   <caller>`.
7. Validate `args.len() == callee.params.len()` before port-map emission. For
   each argument, use `reg_expr_for_type(..., callee.params[i].ty, types)` so
   bool constants render as `'0'`/`'1'` and integers preserve width.
8. Compute the callee `VhdlReturnAbi` using Worker 2's helper. For scalar
   returns, allocate one temp signal. For tuple/labeled tuple returns, allocate
   one signal per output field using deterministic names:
   `call_<dest-vreg>_<sanitized-field>` when `dest` exists, otherwise
   `call_<ordinal>_<sanitized-field>` for discarded calls.
9. Register call-output signals through the same collision-checked signal helper
   used for arithmetic temps. Signal type is each `VhdlReturnField.ty`.
10. Emit a deterministic instance label `u_<sanitized-callee>_<ordinal>` and a
    named port map. Inputs map by sanitized callee parameter names; outputs map
    by ABI port names:

    ```vhdl
    u_full_add_0: entity work.full_add
        port map (
            a => a0,
            b => b0,
            cin => '0',
            sum => call_7_sum,
            cout => call_7_cout
        );
    ```

11. Store scalar call results in `state.reg_expr[dest]`. Store multi-output call
    results in `state.reg_tuple_fields[dest]` as field-index metadata that
    includes field label, field type, and temp signal name. A call with `dest:
    None` still emits the instance and output temp signals if the callee ABI has
    outputs, but no register metadata is recorded.
12. Append instance text to `state.instances`, not `state.assigns`. In
    `emit_vhdl_function`, print signal declarations first, then `begin`, then
    instances, then concurrent assignments, then return-output assignments. This
    keeps instance declarations before expressions that consume `lo_sum` /
    `lo_cout`.
13. Return hard errors for `MirInst::IndirectCall`, `MirInst::InterpCall`,
    `ExternMethodCall`, missing callee metadata, runtime calls, and unsupported
    tuple runtime calls. Worker 5 owns the narrow `rt_tuple_get` recognizer for
    virtual hardware-call aggregates.

Tests:

- System spec `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl`
  covering `add2` calling `full_add` twice and asserting named `port map`.
- GHDL analysis/elaboration/synthesis for generated callee and caller.

Worker 4 depends on Workers 1-3.

### Worker 5: Tuple Field Access over Hardware Call Results

Primary files:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`
- Read-only reference:
  `src/compiler_rust/compiler/src/mir/lower/lowering_expr.rs`
  `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`
  `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`

Read-only findings:

- HIR type resolution maps both labeled tuple access and numeric tuple access
  to positional field indexes. In `type_resolver.rs`, `HirType::LabeledTuple`
  resolves `lo.sum` to `(0, field_ty)`, `lo.cout` to `(1, field_ty)`, and
  `lo.0` to `(0, field_ty)`. The field label is not preserved in
  `HirExprKind::FieldAccess`; only `field_index` remains.
- MIR lowering dispatches `HirExprKind::FieldAccess { receiver, field_index }`
  through `lower_field_access_expr(receiver, field_index, expr_ty)` in
  `lowering_expr.rs`.
- `lower_field_access_expr` currently treats only `HirType::Tuple(_)` as tuple
  storage. It does not include `HirType::LabeledTuple(_)`, so labeled tuple
  values can incorrectly fall through to `MirInst::FieldGet`.
- For tuple storage, the exact MIR shape is:

  ```text
  MirInst::ConstInt { dest: index_reg, value: field_index as i64 }
  MirInst::Call {
      dest: Some(dest),
      target: CallTarget::from_name("rt_tuple_get"),
      args: vec![receiver_reg, index_reg],
  }
  ```

- Therefore `lo.sum`, `lo.cout`, and `lo.0` are indistinguishable by the time
  they reach VHDL lowering. Worker 5 must resolve them by numeric index against
  `state.reg_tuple_fields[receiver_reg]`, where Worker 4 recorded the virtual
  hardware-call aggregate fields.

Exact source tasks:

1. In `lowering_expr_struct.rs`, update tuple detection in
   `lower_field_access_expr` from `matches!(t, HirType::Tuple(_))` to include
   `HirType::LabeledTuple(_)`. This is needed before VHDL lowering can see
   `rt_tuple_get` for labeled tuple values.
2. Add a helper in `pipeline/codegen.rs`:
   `fn call_target_name(target: &CallTarget) -> &str` if `target.name()` is not
   directly reusable at the needed call sites.
3. Add `fn const_index_arg(state: &VhdlLowerState, reg: VReg) -> Result<usize,
   CompileError>` that reads `state.reg_int_const[reg.0]`, rejects missing or
   negative indexes, and returns `usize`.
4. Add `fn lower_virtual_tuple_get(dest: VReg, receiver: VReg, index_reg: VReg,
   state: &mut VhdlLowerState) -> Result<(), CompileError>`.
   - Require `state.reg_tuple_fields.get(&receiver.0)`.
   - Resolve the index from `index_reg`.
   - Bounds-check against the field vector.
   - Insert the selected field expression into `state.reg_expr[dest.0]`.
   - Insert the selected field type into `state.reg_ty[dest.0]`.
   - Do not emit VHDL text; this is a virtual projection over call-output
     signals that Worker 4 already declared.
5. In `lower_vhdl_instruction`, handle:

   ```text
   MirInst::Call {
       dest: Some(dest),
       target,
       args
   } if target.name() == "rt_tuple_get" && args.len() == 2
   ```

   before the general hardware-call branch from Worker 4. Call
   `lower_virtual_tuple_get(*dest, args[0], args[1], state)`.
6. If the `rt_tuple_get` receiver is absent from `state.reg_tuple_fields`, emit
   a hard VHDL diagnostic:
   `VHDL backend unsupported runtime tuple access in <function>; only field access on direct @hardware call results is supported`.
7. If the index is not a compile-time integer constant, emit:
   `VHDL backend unsupported dynamic tuple field access in <function>`.
8. If the index is out of bounds for the virtual aggregate, emit:
   `VHDL backend tuple field index <n> out of range for hardware call result in <function>`.
9. Keep `MirInst::FieldGet` unsupported for tuple projection. Seeing
   `FieldGet` for a tuple/labeled tuple in VHDL lowering should be treated as a
   lowering bug or unsupported struct field access, not as a second tuple path.
10. Do not add a general runtime tuple implementation. Ordinary tuple literals
    can be projected only when Worker 3 stored them in `reg_tuple_fields`; heap
    tuple access, dynamic indexes, and runtime helper calls remain unsupported.

Tests:

- MIR/system test where caller returns `(sum0: lo.sum, sum1: hi.sum, carry:
  hi.cout)`. Assert that generated VHDL uses the Worker 4 call-output signals,
  for example `sum0 <= call_<lo>_sum`, `sum1 <= call_<hi>_sum`, and
  `carry <= call_<hi>_cout`.
- Numeric access compatibility test using `lo.0` and `lo.1` over the same
  labeled hardware-call result. The generated VHDL should match the labeled
  access output signals.
- Negative test where arbitrary runtime tuple access in hardware lowering
  reports the unsupported runtime tuple access diagnostic.
- Negative test where the tuple index is not a constant reports the dynamic
  tuple field access diagnostic.

Worker 5 depends on Worker 4.

### Worker 6: Backend Test Harness and Facade Demotion

Primary files:

- `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl`
- `test/system/compiler/vhdl_mir_backend_call_port_map_spec.spl`
- `test/system/compiler/vhdl_source_facade_spec.spl`
- `test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip`
- `doc/04_architecture/vhdl_support_matrix.md`

Exact source tasks:

1. Add the MIR backend system spec only after Workers 2-5 expose a runnable
   CLI/API path.
2. Cover:
   - labeled tuple return emits multiple ports;
   - same-type labeled outputs compile;
   - direct hardware call emits named `port map`;
   - generated caller and callee pass `ghdl -a --std=08`,
     `ghdl -e --std=08`, and `ghdl --synth --std=08`;
   - same-type anonymous return fails before VHDL emission.
3. Keep source-facade tests as compatibility smoke. Remove duplicate parity
   assertions only after MIR tests pass.
4. Update the support matrix to name the MIR backend as the source of truth for
   labeled multi-output and hardware-call ABI.
5. Mark only `VHDL-PARITY-016` pending specs complete; do not mark unrelated
   reset/domain, bit-op, memory, enum, or testbench parity complete.

MIR backend test harness scope:

- `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl` owns return ABI
  coverage. It must compile Simple source through the Rust MIR VHDL backend,
  not through `aot_vhdl_file` facade helpers. If the public CLI path is not
  named yet, add a small pending helper wrapper in the spec with one call site
  so the eventual command can be swapped without changing assertions.
- `test/system/compiler/vhdl_mir_backend_call_port_map_spec.spl` owns direct
  hardware-call coverage. It should use `full_add` and `add2` as the canonical
  fixture because it exercises same-type labeled outputs and `lo.sum` /
  `lo.cout` field access.
- Keep all generated VHDL under the spec temp directory. Each example should
  assert the generated text first, then run GHDL only when `ghdl` is available.
  Missing `ghdl` is a skip for the GHDL sub-check, not a pass for malformed
  text.
- Use exact string assertions for stable ABI markers:
  `sum : out std_logic`, `cout : out std_logic`,
  `u_full_add_0: entity work.full_add`, `port map`, `sum => lo_sum`, and
  `cout => lo_cout`.
- Use negative tests for diagnostics before GHDL:
  repeated same-type anonymous return, duplicate sanitized output labels, and
  unsupported runtime tuple access over non-hardware-call tuples.

Required GHDL checks:

```sh
ghdl -a --std=08 full_add.vhd add2.vhd
ghdl -e --std=08 add2
ghdl --synth --std=08 add2
```

Acceptance criteria for moving source-of-truth:

- MIR backend specs prove labeled tuple output ports and direct hardware calls
  without relying on facade parsing shortcuts.
- The generated caller and callee pass GHDL analysis, elaboration, and synth.
- Facade specs remain as compatibility smoke and no longer contain unique
  parity assertions for `VHDL-PARITY-016`.
- `doc/04_architecture/vhdl_support_matrix.md` names the Rust MIR VHDL backend
  as authoritative for multi-output ABI and direct `@hardware` call lowering.

Verification:

- `bin/simple test test/system/compiler/vhdl_mir_backend_multi_output_spec.spl`
- `bin/simple test test/system/compiler/vhdl_mir_backend_call_port_map_spec.spl`
- `bin/simple test test/system/compiler/vhdl_source_facade_spec.spl`
- `bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip`

Worker 6 runs last and owns docs/spec cleanup only.

## Current Backend Shape

- `generate_vhdl(module: &mir::MirModule)` iterates MIR functions and emits
  each non-main, non-internal function.
- `emit_vhdl_function` emits every return through one output port:
  `result_out : out <vhdl_type(func.return_type)>`.
- `VhdlLowerState` tracks register expressions, integer constants, local
  addresses, temp signals, and concurrent assignments.
- `lower_vhdl_instruction` supports a narrow combinational subset:
  `LocalAddr`, `Load`, `ConstInt`, `ConstBool`, `Copy`, `BinOp`, `UnaryOp`,
  and `Drop`.
- `MirInst::Call` is currently unsupported by VHDL lowering.
- MIR function signatures carry only `return_type: TypeId`; labeled tuple field
  names are available in HIR as `HirType::LabeledTuple(Vec<(String, TypeId)>)`,
  but `MirModule` does not currently carry a type registry.

## Required ABI Changes

### 1. Make VHDL Lowering Type-Aware

The MIR VHDL backend needs access to resolved HIR type structure, not just raw
`TypeId`, for:

- detecting `HirType::LabeledTuple` return types;
- extracting output labels and field types;
- detecting anonymous tuple returns for deterministic `out0`, `out1`, etc.;
- detecting repeated same-type anonymous returns if an earlier common Simple
  diagnostic did not already stop compilation;
- flattening labeled tuple inputs and future bundle ports;
- resolving field access on hardware-call results.

Preferred implementation order:

1. Thread `&TypeRegistry` or an equivalent VHDL type view into
   `generate_vhdl`, `emit_vhdl_function`, `vhdl_type`, and helpers.
2. Keep `TypeId` as the compact MIR reference; do not duplicate labels into
   every instruction unless the existing pipeline cannot expose the registry.
3. Add a small backend-local `VhdlPort` / `VhdlReturnAbi` helper:
   name, direction, field index, field type, source label, and sanitized name.

### 2. Labeled Tuple Output ABI

For `@hardware fn full_add(...) -> (sum: bool, cout: bool)`, emit:

```vhdl
entity full_add is
    port (
        a : in std_logic;
        b : in std_logic;
        cin : in std_logic;
        sum : out std_logic;
        cout : out std_logic
    );
end entity full_add;
```

Backend behavior:

- Labeled return fields become output ports using sanitized labels.
- Duplicate labels and duplicate sanitized output names are hard errors.
- Anonymous distinct-type returns use deterministic `out0`, `out1`, etc. with
  the common warning policy preserved outside the backend.
- Repeated same-type anonymous returns remain a hard error before emission.
- Single scalar returns may keep `result_out` for compatibility until facade
  tests are migrated.

Return lowering must decompose the returned tuple register into field
expressions. If MIR currently lowers labeled tuple literals as positional
`TupleLit`, the backend should map return field indexes through the return ABI.

### 3. Direct `@hardware` Call Lowering

For:

```simple
val lo = full_add(a0, b0, false)
val hi = full_add(a1, b1, lo.cout)
```

emit component/entity instances with named port maps:

```vhdl
signal lo_sum : std_logic;
signal lo_cout : std_logic;
signal hi_sum : std_logic;
signal hi_cout : std_logic;

u_full_add_0: entity work.full_add
    port map (
        a => a0,
        b => b0,
        cin => '0',
        sum => lo_sum,
        cout => lo_cout
    );
```

Backend behavior:

- Only direct calls to functions selected for hardware entity emission lower to
  instances.
- Calls to runtime functions such as `rt_tuple_get` remain unsupported in VHDL;
  tuple field access for hardware-call results should be handled through
  backend metadata, not runtime calls.
- Each multi-return call allocates one temp signal per returned field.
- The destination register for the call should map to a virtual aggregate in
  `VhdlLowerState`, e.g. `reg_tuple_fields: HashMap<u32, Vec<String>>`.
- A subsequent field access must resolve to the already allocated field signal.
  If MIR represents field access as `rt_tuple_get`, add a VHDL-only recognizer
  for `rt_tuple_get(call_result, const_index)` over virtual aggregates.
- Instance labels must be deterministic and collision-safe:
  `u_<callee>_<ordinal>`.
- Port maps must be named, never positional.

### 4. Temp Signal Handling

Extend `VhdlLowerState` with explicit declaration queues:

- scalar temp signals from arithmetic and unary operations;
- call-output field signals;
- optional aggregate/register metadata for virtual tuple values;
- instance text separate from concurrent assignments.

Signal naming rules:

- sanitize all labels and callee names with the same identifier policy;
- include the destination vreg or instance ordinal to avoid reuse;
- reject collisions after sanitization;
- preserve stable output text order for golden tests.

### 5. Function Selection and `@hardware`

Current `generate_vhdl` emits all non-main, non-internal functions. True parity
needs a hardware boundary decision:

- public `@hardware` functions emit entities;
- pure helper functions may later lower as VHDL subprograms under
  VHDL-PARITY-010;
- unsupported non-hardware runtime helpers must not accidentally become
  entities.

Implementation should inspect `MirFunction.attributes` for `hardware`,
`clocked`, generic/domain metadata, or whatever attribute names the HIR/MIR
lowering preserves.

## Facade Test Migration

Move these source-facade behaviors into MIR backend runnable coverage:

- labeled tuple return emits multiple output ports;
- generated `full_add` analyzes, elaborates, and synthesizes with GHDL;
- direct hardware caller instantiates callee with named `port map`;
- `lo.sum`, `lo.cout`, and nested call-result field access wire to temp
  signals;
- same-type labeled outputs compile;
- same-type anonymous outputs fail before VHDL emission.

Suggested new tests:

- `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl`
- golden string checks for entity ports and `port map`;
- GHDL checks for generated callee plus caller;
- one negative diagnostic spec for unsupported runtime tuple access in hardware
  lowering.

Keep the existing facade tests until MIR coverage is stable, then mark facade
coverage as compatibility smoke rather than the source of truth.

## Implementation Order

1. Add a backend type view to MIR VHDL generation.
2. Implement `VhdlReturnAbi` for scalar, anonymous tuple, and labeled tuple
   returns.
3. Emit labeled tuple return fields as entity output ports.
4. Decompose tuple-return terminators into per-output assignments.
5. Add deterministic temp signal and instance state to `VhdlLowerState`.
6. Lower direct hardware `MirInst::Call` to entity instances with named
   `port map`.
7. Resolve `rt_tuple_get` over virtual hardware-call aggregates to field temp
   signals.
8. Add strict diagnostics for unsupported calls, unsynthesizable tuple runtime
   access, and sanitized name collisions.
9. Add MIR backend system specs and GHDL analysis/elaboration/synthesis checks.
10. Retire duplicated facade assertions once MIR backend tests cover the same
    behavior.

## Verification

Focused gate:

```sh
cargo check -p simple-compiler -p simple-driver
bin/simple test test/system/compiler/vhdl_mir_backend_multi_output_spec.spl
ghdl -a --std=08 <generated-callee-and-caller>.vhd
ghdl -e --std=08 <top_entity>
ghdl --synth --std=08 <top_entity>
```

Full contribution gate:

```sh
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
sh scripts/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs
```
