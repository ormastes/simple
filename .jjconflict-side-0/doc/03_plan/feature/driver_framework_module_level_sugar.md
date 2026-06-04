# Plan: Driver Framework Module-Level Sugar (FR-DRIVER-0001 Remaining)

- **Date:** 2026-05-30
- **Status:** Planned
- **Priority:** P1
- **FR:** `doc/08_tracking/feature_request/driver_framework_requests.md` (FR-DRIVER-0001)
- **Effort:** M (1-2 weeks)

## Context

FR-DRIVER-0001 is partially complete. Function-level `@driver(..., ops=...)`
and `@native_lib(..., ops=...)` are wired as of 2026-05-30. The remaining work
is **module-level and impl-level sugar** -- placing `@driver(...)` on a `module`
or `impl` block so that all exported ops are auto-collected without requiring
the author to list them in the attribute.

Current state:
- Parser recognizes `@driver(...)` / `@native_lib(...)` with named args
- HIR stores manifest on `FunctionAttr`
- Synthetic codegen (`src/compiler/50.mir/synthetic_driver_codegen.spl`) emits
  `register_static_driver(manifest, ops)` for functions marked `ReadyToSynthesize`
- Rust seed mirrors function-level synthesis in HIR lowering
- `sffi_lint.spl` has driver-shim conformance rule
- Example `null_block.spl` uses function-level `@driver(...)` and passes tests
- Module-level / impl-level: **NOT implemented** -- `ModuleAttr` does not exist

Related completed FRs:
- FR-DRIVER-0002 (Cranelift `>>` fix): Implemented
- FR-DRIVER-0003 (`@packed struct` bitfield): Implemented
- FR-DRIVER-0004 (`.drv_manifest` SMF section): Implemented
- FR-DRIVER-0005 (DMA cache maintenance): Implemented
- FR-DRIVER-0006 (fs/gpu adapter integration): Implemented
- FR-DRIVER-0008 (Rust-seed bitfield codegen): Implemented

## Prerequisites and Blockers

1. **Function-level `@driver` working** -- done (prerequisite met)
2. **`ModuleAttr` in HIR** -- must be added; currently only `FunctionAttr` exists
   in `src/compiler/20.hir/hir_definitions.spl`
3. **Self-hosted bootstrap** -- the synthetic codegen in `mir_lowering.spl` is
   unreached until self-hosted replaces Rust seed; module-level sugar also needs
   Rust seed support for immediate usability
4. **No compiler blocker** -- this is additive sugar on top of working infra

## Phased Implementation Steps

### Phase 1: Module/Impl Attribute AST Support (S)

Add `@driver(...)` and `@native_lib(...)` recognition on module and impl
declarations.

1. Extend `src/compiler/00.common/attributes.spl`:
   - `parse_driver_manifest_attrs` already handles function-level; add a variant
     or flag for module/impl context
   - When on a module/impl, the `ops=...` argument is optional (ops will be
     auto-collected from the block's exported functions)
2. Add `ModuleAttr` / `ImplAttr` to `src/compiler/20.hir/hir_definitions.spl`:
   - Store `DriverManifestAttr?` on module/impl declarations
3. Update parser in `src/compiler/10.parser/` to attach the attribute to the
   owning module/impl node (not to individual functions)
4. Verify: `bin/simple check src/compiler/` passes

**Files to modify:** `src/compiler/00.common/attributes.spl`,
`src/compiler/20.hir/hir_definitions.spl`,
`src/compiler/10.parser/parser_decls.spl` (or equivalent)

### Phase 2: Op Collection from Module/Impl Body (M)

Auto-collect driver ops from the attributed block's exported functions.

1. In `src/compiler/50.mir/synthetic_driver_codegen.spl`, add a new pass:
   `collect_module_driver_ops(module: HirModule) -> List<DriverOp>`:
   - Scan all public functions in the module/impl block
   - Match function signatures against the `Driver` trait surface
     (`init`, `probe`, `attach`, `detach`, `read`, `write`, `ioctl`, `irq`)
   - Build `DriverOps` struct from matched functions
2. When a module has `@driver(...)` without explicit `ops=...`, invoke
   `collect_module_driver_ops` and synthesize the registration call
3. When `ops=...` IS provided on a module-level attribute, use the explicit
   list (same as function-level behavior)
4. Error if the module declares `@driver(...)` but has zero matching op functions

**Files to modify:** `src/compiler/50.mir/synthetic_driver_codegen.spl`,
`src/compiler/50.mir/mir_lowering.spl`

### Phase 3: Rust Seed Mirror (M)

Mirror the module/impl-level sugar in the Rust seed for immediate usability.

1. Update `src/compiler_rust/parser/src/types_def/mod.rs` to parse
   `@driver(...)` / `@native_lib(...)` on module/impl blocks
2. Add `ModuleAttr` to `src/compiler_rust/parser/src/ast/nodes/core.rs`
3. In HIR lowering (`src/compiler_rust/compiler/src/hir/lower/`), mirror the
   op-collection logic: scan the module's public functions, match against
   Driver trait surface, synthesize `register_static_driver` call
4. In the interpreter path, ensure the synthesized registration runs at
   module load time

**Files to modify:** `src/compiler_rust/parser/src/types_def/mod.rs`,
`src/compiler_rust/parser/src/ast/nodes/core.rs`,
`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`,
`src/compiler_rust/compiler/src/interpreter_eval.rs`

### Phase 4: Lint and Diagnostics (S)

1. Update `sffi_lint.spl` module-level rule: a module with `@driver(...)` must
   contain at least `init` and `probe` functions
2. Add diagnostic: "module-level @driver without any matching op functions" as
   a warning (not error, since the module may re-export ops from sub-modules)
3. Add diagnostic: "impl-level @driver on a non-Driver-conforming impl" as error

**Files to modify:** `src/app/build/sffi_lint.spl`

### Phase 5: Tests and Migration (S)

1. Create `test/01_unit/compiler/driver_module_attr_spec.spl`:
   - Module-level `@driver(...)` with auto-collected ops
   - Module-level `@driver(...)` with explicit `ops=...`
   - Impl-level `@driver(...)` on a `impl Driver for MyBlock`
   - Error case: `@driver(...)` on module with no matching functions
2. Migrate `examples/simple_os/src/drivers/null_block.spl` to use module-level
   `@driver(...)` instead of function-level, verify test still passes
3. Write migration guide snippet in
   `doc/07_guide/driver_attribute_migration.md` (optional, only if requested)

**Files to create:** `test/01_unit/compiler/driver_module_attr_spec.spl`
**Files to modify:** `examples/simple_os/src/drivers/null_block.spl`

## Acceptance Criteria

- [ ] `@driver(class=..., vendor=..., device=..., version=...)` compiles on
      a `module` declaration and auto-collects ops from exported functions
- [ ] `@driver(...)` compiles on an `impl Driver for X` block and collects ops
      from the impl's methods
- [ ] Auto-collection matches: `init`, `probe`, `attach`, `detach`, `read`,
      `write`, `ioctl`, `irq` function names against the Driver trait surface
- [ ] Explicit `ops=...` on module-level still works (override auto-collection)
- [ ] `sffi_lint` warns on module `@driver(...)` with no matching ops
- [ ] `null_block.spl` example works with module-level attribute
- [ ] Both Rust seed and self-hosted paths support the sugar
- [ ] Procedural registration path (`register_static_driver(m, ops)`) continues
      to compile for legacy drivers

## Risk Factors

- **Op signature matching (Medium):** Auto-collecting ops by function name is
  fragile; a function named `init` that is not a driver init could be
  incorrectly matched. Mitigation: require the function to be inside a
  `impl Driver` block, or require `@driver_op` sub-attributes on individual
  functions when using module-level `@driver`
- **Rust seed/self-hosted parity (Medium):** Module-level attribute in the
  self-hosted path is unreached until bootstrap replaces Rust seed; risk of
  drift. Mitigation: test both paths in Phase 5
- **Module re-export (Low):** If a module re-exports ops from sub-modules,
  the auto-collection may not find them. Mitigation: document that
  auto-collection only scans direct children; use explicit `ops=...` for
  re-exported ops
- **Backward compatibility (Low):** Function-level `@driver(...)` must continue
  working; the module-level sugar is strictly additive
