# Phase 1 whole-test runner: CostEstimate collision causes JIT fallback

Status: OPEN — diagnosis and regression plan only; no compiler fix or new test execution.
Owner: compiler flattened-module nominal type resolution (Rust bootstrap seed).

## Observed evidence

The FreeBSD Phase 1 whole-suite baseline at source `051ee9d97809` reports:

```text
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'CostEstimate' field 'scalar_cost' (declared fields: island_root_id, estimated_work, cpu_us, gpu_kernel_us, scheduling_us, host_to_device_bytes, device_to_host_bytes, synchronization_points, predicted_gpu_us) [in src/app/test_runner_new/main.spl]
```

Preserved host evidence:

- `/home/yoon/dev/simple-phase1-bottom-up-20261007/build/phase1-local-manager-20261007/phase1-whole-tests-051ee9d97809-attempt1/results/stderr.log`, lines 1802–1805.
- SHA-256: `28a0bc43f2ccb0cf78b2ec9712d16d6b784397a16e9be0e68bc288bfff61b617`.
- The following lines explicitly record `reason=jit-compile-error` and interpreter fallback.

Read-only source inspection was performed at `e934d53a7e7` and compared with
release `3001767f85eba3b6e401135aab1e1bfc18fac110`. The relevant source files
listed below are unchanged from the baseline. A read-only `git ls-remote`
confirmed that release SHA when this report was prepared. Attempt 2 was already
running and was not modified or restarted for this investigation.

This is evidence of whole-runner engine demotion, not proof that the suite has
failed. The interpreter can continue. The diagnostic's generic slowdown estimate
is not a measured performance ratio for this run; no comparative timing was run.

## Root cause

The entry imports `app.test_runner_new.test_runner_main.{run_test_cli}`. Its
flattened closure contains at least three unrelated nominal declarations:

| Declaration | Fields identifying its layout |
|---|---|
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_cost.spl:14` | scalar_cost, vector_cost, speedup, profitable |
| `src/lib/common/compute/placement_contracts/planner.spl:31` | cpu_work, simd_work, gpu_work, transfer fields, confidence_milli |
| `src/lib/common/structural/execution/contracts.spl:19` | island_root_id, estimated_work, CPU/GPU timing and transfer fields |

The only constructor naming `scalar_cost` is
`estimate_vectorization_cost` in `auto_vectorize_cost.spl:49`. Its local nominal
type is valid. The logged declared-field list exactly matches the structural
execution declaration instead.

Compiler ownership is lost at these boundaries:

1. `pipeline/module_loader.rs::tag_node_function_owners` tags functions and
   methods during flattening. It does not retain declaration ownership directly
   on methodless structs/classes. Function metadata alone cannot identify these
   zero-method types.
2. `hir/lower/type_registration.rs::register_struct` records
   `struct_decl_files[s.name] = current_file` (line 173). In the flattened lane,
   this attributes imported types to the runner entry file. Class registration
   has the same issue. Registry lookup remains keyed by bare name. Distinct
   layouts can receive distinct TypeIds, but the bare name selects the last
   registration.
3. Constructor resolution uses the bare type lookup (`expr/calls.rs:343` and
   `expr/collections.rs::lower_struct_init`). Consequently the auto-vectorizer
   constructor receives the structural execution TypeId/layout.
4. `expr/collections.rs::lower_struct_init_fields` trusts that registry layout;
   its `declared_here` gate (around line 539) incorrectly considers this a local
   declaration and rejects `scalar_cost`.

The duplicate-layout field-read fallback cannot repair constructor identity.
Relaxing the rejection, selecting a layout by matching field names, or renaming
the application type would conceal the nominal-ownership defect and could allow
incorrect field placement, defaults, or annotations.

Related prior diagnosis:
[caret flattened-type collision](caret_jit_fallback_flatten_same_name_types_2026-10-04.md).
This report adds an independent Phase 1 runner occurrence; it does not supersede
or claim to resolve that report.

## Proposed bounded repair

Preserve owner metadata on struct/class declarations themselves, including
zero-method declarations and nested reexports. Register nominal TypeIds,
declaration locations, and defaults by owner-qualified identity. Resolve
constructor references and type annotations using the function/declaration owner
and existing `flatten_owner_import_bindings`, including aliases. Bind signatures
in their own declaration context, before function bodies are lowered. Keep
ordinary single-module behavior and genuine unknown-field rejection intact.

Coordinate this compiler change with the other host's compiler owner before
editing. The repair crosses registration, constructor, and annotation lookup;
changing only the diagnostic gate is insufficient. No such rewrite is included
in this report.

## Focused regression plan (not executed)

1. Load temporary modules A, B, and C through the real
   `load_module_with_imports` path. Each declares a methodless `CostEstimate`
   with different fields and a function constructing and returning its own type.
2. Lower with the actual flattened JIT entrypoint. Assert distinct nominal
   identities and the correct constructor field order, field types, defaults,
   and return/parameter annotations. Include both paren-call and brace literals.
3. Reverse import order. Include a shared field name at different indices and
   with different types; this catches silent wrong-layout selection even when
   every field name is accepted.
4. Include explicit imported aliases, nested reexports, and a declaration-owned
   default expression. Confirm references remain bound to their source owner.
5. Include an actual misspelled constructor field and assert rejection against
   its correct declaration. Do not weaken the fail-closed behavior.
6. Execute the small fixture with strict JIT and assert returned values, with no
   interpreter fallback. Only after focused tests pass, qualify the real runner
   once on the pinned corrected release and retain engine/admission evidence.

No test, build, or whole-suite retry was launched for this read-only diagnosis.
The active whole-suite interpreter run remains useful evidence, but does not
prove native/JIT runner qualification or resolution of this performance defect.
