# `SpirvBuilder.emit_function()` cannot be paired with a pre-allocated entry-point id

**Status:** Open (workaround applied in the affected caller)
**Component:** `src/compiler/70.backend/backend/vulkan/spirv_builder.spl`
**Found by:** lane A1-FINAL, board-Vulkan SPIR-V Khronos-validity boundary,
2026-08-11.

## Symptom

Building a minimal compute-shader module through `SpirvBuilder`'s public API
using the "obvious" sequence —

```
val main_id = builder.alloc_id()
builder.emit_entry_point("main", main_id, [])
builder.emit_execution_mode(main_id, [1, 1, 1])
...
builder.emit_function(void_id, fn_type_id, "None")   # <-- allocates ANOTHER id
```

— produces a module where `OpEntryPoint` references `%1` (the pre-allocated
`main_id`) but `OpFunction` is emitted against a *different*, later-allocated
id (`%4` in the reproduction). `main_id` is never defined by anything.
`spirv-val` correctly rejects this:

```
error: line 0: The following forward referenced IDs have not been defined:
'1[%1]'
```

`spirv-as` alone does not catch it (assembly succeeds, exit 0) — only
`spirv-val`, the normative validator, catches the defect. This is exactly the
scenario the board-Vulkan plan's Khronos-tools boundary exists to catch.

## Root cause

`SpirvBuilder.emit_function(result_type_id, func_type_id, control) -> i64`
(`spirv_builder.spl:302`) always calls `self.alloc_id()` internally and has
no variant that accepts a caller-supplied id. But SPIR-V's mandatory global
section order requires `OpEntryPoint`/`OpExecutionMode` to appear *before*
the type/function section, while `OpEntryPoint` must reference the
function's id — so any caller building a complete module has to allocate
the function's id up front, before it can call `emit_function()`.

## Workaround (already used correctly elsewhere)

The sibling boundary `boundary_spirv_provider.spl` (glslang structural
comparison, already landed) sidesteps this by never calling
`emit_function()` for its entry-point function: it pre-allocates `main_id`
and writes the `OpFunction` line by hand via the builder's own `emit()`
escape hatch:

```
builder.emit("{builder.id_str(main_id)} = OpFunction {builder.id_str(void_id)} None {builder.id_str(fn_type_id)}")
```

`boundary_spirv_khronos_provider.spl` (this lane) now does the same, with a
comment recording why. This is a workaround at the CALL SITE, not a fix to
`SpirvBuilder` itself — `spirv_builder.spl` was intentionally left untouched
per this lane's scope (only a genuine emission defect justifies editing it,
and the builder's behavior here is a documented API gap, not incorrect
per-instruction emission).

## Suggested real fix (not applied here, out of this lane's scope)

Add an `emit_function_with_id(id: i64, result_type_id: i64, func_type_id: i64, control: text)`
that emits the `OpFunction` line against a caller-supplied id, so a caller
building a module with a well-known entry-point id does not have to reach
for the raw `emit()` escape hatch. Low risk, additive, does not change
`emit_function()`'s existing contract.

## Evidence

Reproduced directly against the real installed toolchain
(SPIRV-Tools v2025.1, `/usr/bin/spirv-as`, `/usr/bin/spirv-val`), independent
of the Simple compiler (hand-authored `.spvasm` mirroring the buggy call
sequence byte-for-byte):

- Buggy sequence: `spirv-as` exit 0, `spirv-val` exit 1, diagnostic
  `"forward referenced IDs have not been defined: '1[%1]'"`.
- Corrected sequence (pre-allocated id used for both `OpEntryPoint` and the
  hand-emitted `OpFunction` line): `spirv-as` exit 0, `spirv-val` exit 0.

## Related

- `src/os/drivers/gpu/board_vulkan/boundary_spirv_khronos_provider.spl` —
  candidate builder for this boundary, uses the workaround.
- `test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl` — proof spec
  (blocked from running by an unrelated pre-existing merge conflict, see
  below; verified instead by direct hand-reproduction against the real
  tools, transcript above).
- `src/os/drivers/gpu/board_vulkan/boundary_spirv_provider.spl` — sibling
  boundary that already uses the correct pattern (unaffected).

## Separate, unrelated blocker hit while verifying this

At the time of this investigation, `git status` showed 13 files in
unresolved-merge (`UU`) state repo-wide (e.g.
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` with live
`<<<<<<<`/`=======`/`>>>>>>>` markers), left mid-flight by another session.
This makes the ENTIRE compiler tree fail to parse — both
`bin/simple test <spec>` and `bin/simple run <spec>` fail with
`error: compile failed: parse: ... expr_dispatch.spl: Unexpected token:
expected Indent, found Dedent`, for every spec in the repo, not just this
one. This lane did not resolve those conflicts (out of scope, and resolving
someone else's overlapping bugfix conflict without full context risks
reverting a landed fix — see `.claude/rules/vcs.md` "Sync must never
clobber"). The Khronos-tools findings above were therefore verified by
hand-reproducing the exact instruction sequences against the real installed
`spirv-as`/`spirv-val` directly, decoupled from the broken compiler tree; the
committed spec file will execute as soon as those conflicts are resolved.
