# SStack State: driver-framework-compiler

## User Request
> impl with agent team and minimize duplication. Driver Framework compiler work — Cranelift >> + bitfield sugar. The big surprise is doc/05_design/ with 286 files — most were never audited.

## Task Type
feature

## Refined Goal
> Complete the remaining Driver Framework compiler work: (1) FR-DRIVER-0003 — implement `@packed struct { f: T:N }` bitfield sugar syntax that routes to the existing Bitfield HIR node (unblocked now that FR-DRIVER-0008 landed), and (2) FR-DRIVER-0001 — finish synthetic registration codegen for `@driver(...)` attribute. C.2 Cranelift >> is verified done. Quick triage of doc/05_design/ runs in parallel.

## Acceptance Criteria
- [ ] AC-1: `@packed struct { f: u16:4, g: u16:12 }` parses and lowers to the existing `HirBitfield` node in the self-hosted compiler
- [ ] AC-2: `@packed struct` field access (`x.f`) generates correct shift+mask via the existing bitfield codegen path
- [ ] AC-3: `@packed struct` field write (`x.f = val`) generates correct read-modify-write via existing bitfield path
- [ ] AC-4: Round-trip test passes: `let x: Foo = Foo.new(0); x.f = 5; expect(x.f).to_equal(5)` with `@packed` struct
- [ ] AC-5: Rust seed parser recognizes `@packed struct { f: T:N }` and routes to `Node::Bitfield` (thin ~50-line pass)
- [ ] AC-6: FR-DRIVER-0001 synthetic registration: `@driver(...)` codegen emits `register_static_driver(m, ops)` call
- [ ] AC-7: doc/05_design/ triage report classifies all files as IMPLEMENTED/STALE/ACTIONABLE/REFERENCE

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
- [x] 2-research (Analyst) — 2026-05-10
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Scope:** FR-DRIVER-0003 (bitfield sugar) + FR-DRIVER-0001 (synth registration) + design doc triage

**Status investigation findings:**
- C.2 Cranelift >>: DONE — verified with `bin/simple test test/unit/compiler/u64_shift_param_spec.spl` (8/8 pass)
- FR-DRIVER-0008 (Rust-seed bitfield HIR/MIR/sema): DONE (2026-04-22) — unblocks FR-0003
- FR-DRIVER-0003 blocker lifted: `bitfield Flags(u32): a:4; b:28` works end-to-end; `@packed struct` is a thin routing pass
- FR-DRIVER-0001: manifest attr + HIR/MIR done; synthetic registration codegen is the one remaining AC
- Design doc triage: parallel agent running

**Key files:**
- Feature tracker: `doc/08_tracking/feature_request/driver_framework_requests.md`
- Bitfield design: `doc/05_design/bitfield_custom_type_design.md`
- Driver arch: `doc/04_architecture/driver_architecture.md`
- Self-hosted bitfield HIR: `src/compiler/20.hir/hir_definitions.spl` (HirBitfield, HirBitfieldField)
- Self-hosted bitfield lowering: `src/compiler/20.hir/hir_lowering/items.spl`
- Rust seed bitfield: `src/compiler_rust/parser/src/types_def/mod.rs`
- Synth registration planner: `src/compiler/50.mir/synthetic_driver_registration.spl`

### 2-research

## Research Summary

### Existing Code — FR-DRIVER-0003 (`@packed struct` bitfield sugar)

**Rust seed parser (the live compiler):**
- `src/compiler_rust/parser/src/types_def/mod.rs:334-365` — `parse_field()` already accepts `field: Type:N` bit-width syntax, stores as `Option<u8>` on the Field AST node
- `src/compiler_rust/parser/src/ast/nodes/core.rs:1013-1015` — `pub bit_width: Option<u8>` field on `Field` struct
- `src/compiler_rust/parser/src/types_def/mod.rs:50-57` — post-name `struct Foo @packed` syntax rejected with diagnostic pointing to prefix form
- `src/compiler_rust/parser/src/parser_impl/attributes.rs:41` — `"packed"` in known attribute list
- `src/compiler_rust/parser/tests/packed_struct_bitfield.rs` — Rust-level parser test exists

**Rust seed HIR lowering (the live compiler):**
- `src/compiler_rust/compiler/src/hir/lower/type_registration.rs:112-113` — routing: `if is_packed && has_bitwidth_fields { return self.register_packed_struct_as_bitfield(s); }`
- `src/compiler_rust/compiler/src/hir/lower/type_registration.rs:175-220` — `register_packed_struct_as_bitfield()` converts `@packed struct` fields to `HirBitfieldField` entries with offsets/widths, validates integer backing type and total bit budget
- `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:112-114` — `Node::Bitfield(bf)` arm calls `self.register_bitfield(bf)` for standalone `bitfield` keyword
- `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:37-68,174-219` — `lower_bitfield_constructor()` handles `Bitfield(raw_value)` calls
- `src/compiler_rust/type/src/checker_check.rs:205-206,564-565,644-658` — `register_bitfield_def()` registers bitfield names+fields in type checker

**Self-hosted compiler (aspirational):**
- `src/compiler/10.frontend/core/parser_decls.spl:1231-1310` — `parse_bitfield_decl()` handles standalone `bitfield Name(T): a:4; b:28` syntax only; NO `@packed struct` routing exists
- `src/compiler/20.hir/hir_lowering/items.spl:810-879` — `@packed` recognized for `LayoutKind.Packed` on regular structs, but NOT routed to bitfield desugaring
- `src/compiler/20.hir/hir_lowering/items.spl:997-1080` — `lower_bitfield()` and `lower_bitfield_field()` produce `HirBitfield`/`HirBitfieldField` from standalone `bitfield` AST nodes
- `src/compiler/20.hir/hir_definitions.spl:185-215` — `HirBitfield` (symbol, name, backing_type, fields, total_bits, visibility, span) and `HirBitfieldField` (symbol, name, type_, bit_width, bit_offset, is_reserved, span) structs
- `src/compiler/00.common/attributes.spl:824-841` — `is_packed` flag parsed from `@packed` / `@repr("packed")` attributes

**Existing tests:**
- `test/unit/compiler/packed_struct_bitfield_spec.spl` — grep-based spec checking source code contains expected symbols (NOT runtime behavior)
- `test/feature/usage/packed_struct_bitfield_syntax_spec.spl` — documents syntax intent, status "parser diagnostic only"
- `test/feature/usage/bitfield_spec.spl` — standalone `bitfield` keyword tests
- `test/unit/compiler/bitfield_sugar_spec.spl` — compiler-level bitfield tests
- `test/system/bitfield_reorder_spec.spl` — bitfield reordering tests
- `test/unit/compiler/mir/bitfield_mir_spec.spl` — MIR-level bitfield tests
- `test/unit/compiler/native/bitfield_codegen_spec.spl` — native codegen bitfield tests

### Existing Code — FR-DRIVER-0001 (synthetic registration codegen)

**Planner (complete):**
- `src/compiler/50.mir/synthetic_driver_registration.spl` (147 lines) — `plan_synthetic_driver_registration(fn_, symbols)` returns a `SyntheticDriverRegistrationPlan` with status enum: `NoManifest`, `AlreadyHandwritten`, `BlockedMissingDriverOps`, `BlockedNativeLibOps`, `ReadyToSynthesize`
- Key logic: walks HIR body to find existing `register_static_driver(manifest, ops)` calls; if absent and `@driver` attr present, looks for a typed `DriverOps` value in symbol table via `find_driver_ops_value(symbols)`
- `src/compiler/00.common/attributes.spl:116-301` — `DriverManifestAttr` struct with `kind` (Driver/NativeLib), `driver_class`, `vendor`, `device_ids`, `version`, `abi`; `parse_driver_manifest_attrs()` extracts from declaration attributes

**HIR integration (complete):**
- `src/compiler/20.hir/hir_definitions.spl:42-44` — `HirFunction` carries `has_driver_manifest_attr: bool` + `driver_manifest_attr: DriverManifestAttr`

**Codegen emission (MISSING — the gap):**
- No codegen pass calls `plan_synthetic_driver_registration()` and emits the actual `register_static_driver(m, ops)` MIR/codegen
- `grep -rn 'emit.*register_static_driver|synth.*registration.*emit|synthesize.*registration' src/compiler/70.backend/` returns empty
- The planner returns `ReadyToSynthesize` status but nothing acts on it
- `src/compiler/70.backend/linker/smf_writer.spl:215` — `add_driver_manifest_section()` exists for SMF output (FR-DRIVER-0004, done), separate from codegen emission

**Existing tests:**
- `test/unit/compiler/mir/synthetic_driver_registration_spec.spl` — 5 `it` blocks covering all planner statuses (AlreadyHandwritten, BlockedMissingDriverOps, ReadyToSynthesize, BlockedNativeLibOps, NoManifest)
- `test/feature/compiler/driver_native_spec.spl` — driver native compilation tests
- `test/feature/usage/serial_driver_spec.spl` — serial driver usage tests
- `test/unit/lib/driver/` — driver library-level tests

### Reusable Modules

- `compiler.common.attributes.{DriverManifestAttr, parse_driver_manifest_attrs}` — attribute parsing for `@driver(...)` / `@native_lib(...)`, fully implemented
- `compiler.mir.synthetic_driver_registration.{plan_synthetic_driver_registration, SyntheticDriverRegistrationPlan, SyntheticDriverRegistrationStatus}` — planner that determines if synthesis is possible
- `compiler.common.attributes.{parse_layout_attrs, LayoutKind, LayoutAttr}` — `@packed` / `@repr` attribute parsing with `is_packed` flag
- `src/compiler/20.hir/hir_lowering/items.spl` — `lower_bitfield()` and `lower_bitfield_field()` reusable for packed-struct-to-bitfield routing
- `src/compiler/70.backend/bitfield.spl` — backend bitfield shift/mask codegen (already handles `HirBitfield`)

### Risks

1. **FR-DRIVER-0003 may already be done in the Rust seed.** The routing pass `register_packed_struct_as_bitfield` exists in `type_registration.rs`. Since `bin/simple` IS the Rust seed, ACs 1-5 might already pass for the Rust seed path. However, no end-to-end runtime test (construct + read/write) exists — only grep-based source-verification specs. Phase 3 must determine: (a) does `@packed struct { f: u16:4 }` actually compile and run end-to-end? (b) is self-hosted parity in scope for this feature?
2. **Self-hosted compiler has NO `@packed struct` bitfield routing.** The self-hosted parser and HIR lowering handle `@packed` only as a layout hint (no padding), not as bitfield desugaring. If AC-1 requires the self-hosted compiler, a new pass is needed in `src/compiler/10.frontend/core/parser_decls.spl` and `src/compiler/20.hir/hir_lowering/items.spl`.
3. **FR-DRIVER-0001 codegen gap is real but bounded.** The planner infrastructure is solid (5 statuses, all tested). The missing piece is a codegen pass (likely in `src/compiler/50.mir/` or `src/compiler/70.backend/`) that: (a) iterates functions with `has_driver_manifest_attr`, (b) calls the planner, (c) for `ReadyToSynthesize`, injects a `register_static_driver(manifest, ops)` call into the function body.
4. **Compile-mode false-greens** (from MEMORY.md) — `--mode=native` and `--mode=smf` can report PASSED when tests actually have unresolved calls. Runtime tests should be verified in interpreter mode.

### Open Questions (for Phase 3)

- Q1: Does `@packed struct { f: u16:4; g: u16:12 }` already work end-to-end in the Rust seed? Run `bin/simple test test/unit/compiler/packed_struct_bitfield_spec.spl` + write a small runtime test to verify.
- Q2: Is self-hosted parity for `@packed struct` in scope for this feature, or only Rust seed? The ACs say "self-hosted compiler" (AC-1) but the Rust seed is the live compiler.
- Q3: Where should the synthetic registration codegen pass live — as a MIR transform in `src/compiler/50.mir/` or as a backend pass in `src/compiler/70.backend/`?

## Requirements

- REQ-1 (from AC-1, AC-5): `@packed struct { f: T:N }` must parse and lower to `HirBitfield` — area: `src/compiler_rust/compiler/src/hir/lower/type_registration.rs` (Rust seed, may already work), `src/compiler/10.frontend/core/parser_decls.spl` + `src/compiler/20.hir/hir_lowering/items.spl` (self-hosted, needs new routing)
- REQ-2 (from AC-2): `x.f` field read generates shift+mask via existing bitfield codegen — area: `src/compiler/70.backend/bitfield.spl`, `src/compiler_rust/compiler/src/hir/lower/expr/` (field access lowering)
- REQ-3 (from AC-3): `x.f = val` field write generates read-modify-write via existing bitfield codegen — area: same as REQ-2
- REQ-4 (from AC-4): Round-trip test: construct, write, read back — area: `test/feature/usage/` or `test/unit/compiler/` (new runtime test)
- REQ-5 (from AC-6): Codegen pass consumes `plan_synthetic_driver_registration()` and emits `register_static_driver(m, ops)` for `ReadyToSynthesize` status — area: new pass in `src/compiler/50.mir/` or `src/compiler/70.backend/`, consuming `src/compiler/50.mir/synthetic_driver_registration.spl`
- REQ-6 (from AC-7): doc/05_design/ triage — parallel agent (out of scope for this pipeline)

## Phase
research-done

## Log
- 1-dev: Created state file with 7 acceptance criteria, identified scope as FR-DRIVER-0003 + FR-DRIVER-0001
- 2-research: Found Rust seed already has @packed struct routing (type_registration.rs); self-hosted lacks it. Planner for FR-DRIVER-0001 fully tested; codegen emission is the gap. 6 requirements mapped, 3 open questions for Architect

### 3-arch

## Architecture

### Answers to Open Questions

- **Q1 (Rust seed end-to-end):** The Rust seed already has full `@packed struct` routing: `type_registration.rs:112-113` checks `is_packed && has_bitwidth_fields` and calls `register_packed_struct_as_bitfield()`. The field `bit_width: Option<u8>` on Field AST is populated by `types_def/mod.rs:334-365`. **AC-5 is likely already done** — implementation phase should verify with a runtime test, not re-implement.

- **Q2 (Self-hosted parity scope):** AC-1 explicitly says "self-hosted compiler." The self-hosted compiler currently has NO `@packed struct` routing — `flat_ast_bridge.spl:778` always sets `attributes: []` on Struct, and the parser uses `@bits(N)` syntax (not `:N`). Self-hosted parity IS in scope but is a **desugar pass** (not parser surgery), converting `@packed`-attributed structs with `has_bits` fields into `Bitfield` AST nodes.

- **Q3 (Synth registration codegen location):** **MIR level** (`src/compiler/50.mir/`). The `DriverManifestAttr` is attribute metadata (not an HIR expression), so constructing a `register_static_driver(manifest, ops)` call requires synthesizing HIR/MIR nodes. Doing it at MIR level keeps the HIR layer clean and matches how `mir_debug_trace_injection.spl` already injects synthetic calls.

### Decisions

- **D-1: Self-hosted `@packed struct` desugar is a post-parse pass, not parser modification.** The self-hosted parser already collects `field_bits` via `@bits(N)` and stores them on Field (`has_bits/bits`). The `flat_ast_bridge.spl` populates `Field.has_bits` correctly. The gap is that structs with `has_bits` fields AND `@packed` attribute are not rerouted to `module.bitfields`. A desugar pass after `flat_ast_bridge` builds the Module will move qualifying structs from `module.structs` to `module.bitfields` as synthesized `Bitfield` AST nodes. This avoids modifying the flat AST layer or the core parser. — Because both `Struct` and `Bitfield` use `decl_struct_def` in the flat AST, the data is already present; only routing changes.

- **D-2: Backing type for `@packed struct` is derived from total field bits.** Unlike standalone `bitfield Flags(u32):` which has explicit backing type, `@packed struct` has no `(T)` syntax. The desugar pass sums field bit widths and picks the smallest unsigned integer that fits: sum <= 8 → u8, <= 16 → u16, <= 32 → u32, <= 64 → u64. If sum > 64, emit a compile error. This matches the Rust seed behavior in `register_packed_struct_as_bitfield()`.

- **D-3: Field syntax stays `@bits(N)` in self-hosted, `T:N` in Rust seed.** The self-hosted parser already handles `@bits(N)` for struct fields (parser_decls.spl:619-638). The Rust seed handles `T:N` (types_def/mod.rs:334-365). No need to add `T:N` to self-hosted or `@bits(N)` to Rust seed — each compiler keeps its syntax variant. Both produce equivalent `Field.bits`/`Field.bit_width` data.

- **D-4: Rust seed `@packed struct` → `Node::Bitfield` routing at end of `parse_struct_with_attrs`.** Currently `parse_struct_with_attrs` always returns `Node::Struct(struct_def)`. Add a check after struct construction: if any attribute is `"packed"` AND any field has `bit_width.is_some()`, convert the `StructDef` to `BitfieldDef` and return `Node::Bitfield(...)`. ~30 lines. — Because `parse_struct_with_attrs` already receives the `attributes` vec and fields already have `bit_width`.

- **D-5: FR-DRIVER-0001 codegen as MIR-level injection in `lower_function`.** The `lower_function` method (mir_lowering.spl:453) is the natural insertion point. After lowering the function body, check `fn_.has_driver_manifest_attr`; if true, call `plan_synthetic_driver_registration(fn_, symbols)`; if status is `ReadyToSynthesize`, append a synthetic `register_static_driver(manifest_expr, ops_name)` MIR call to the function's MIR block list. — Because MIR injection is the established pattern (see `mir_debug_trace_injection.spl`).

- **D-6: DriverOps resolution uses explicit `ops = Name` named arg on `@driver(...)`.** Extend the `@driver` attribute to accept `ops = MyOps` as a named argument. `parse_driver_manifest_attrs()` in `attributes.spl` already handles named args (`class = ...`, `vendor = ...`). Add `ops` field to `DriverManifestAttr`. Planner uses the named arg preferentially; falls back to `find_driver_ops_value(symbols)` scan only if absent. — Because explicit binding is more robust than first-match scan and matches existing `@driver` named-arg pattern.

- **D-7: Manifest value construction at MIR level uses attribute fields directly.** The `DriverManifestAttr` struct already contains `driver_class`, `vendor`, `device_ids`, `version`, `abi`. The codegen pass constructs a `DriverManifest` struct literal from these fields as MIR constant operations, avoiding the need to reify them as HIR expressions.

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| packed_struct_desugar | `src/compiler/10.frontend/desugar/packed_struct_desugar.spl` | Move `@packed` structs with bit-width fields from `module.structs` to `module.bitfields` as `Bitfield` AST nodes | New |
| flat_ast_bridge | `src/compiler/10.frontend/flat_ast_bridge.spl` | Pass through attributes from flat AST to `Struct` (currently hardcoded `[]`) | Modified (line 778) |
| attributes | `src/compiler/00.common/attributes.spl` | Add `ops` field to `DriverManifestAttr`; extend `parse_driver_manifest_attrs()` | Modified |
| synth_driver_codegen | `src/compiler/50.mir/synthetic_driver_codegen.spl` | MIR-level codegen: consumes `plan_synthetic_driver_registration()`, emits `register_static_driver(manifest, ops)` call for `ReadyToSynthesize` functions | New |
| mir_lowering | `src/compiler/50.mir/mir_lowering.spl` | Call `apply_synthetic_driver_codegen()` in `lower_function` after body lowering when `has_driver_manifest_attr` | Modified (around line 453) |
| types_def/mod.rs | `src/compiler_rust/parser/src/types_def/mod.rs` | Add `@packed` struct → `Node::Bitfield` conversion at end of `parse_struct_with_attrs` (~line 95) | Modified |
| mir/__init__ | `src/compiler/50.mir/__init__.spl` | Export `synthetic_driver_codegen` symbols | Modified |
| frontend/__init__ | `src/compiler/10.frontend/__init__.spl` | Export `packed_struct_desugar` | Modified |

### Dependency Map

- `packed_struct_desugar` → `compiler.frontend.parser_types` (Struct, Bitfield, BitfieldField, Field, Module types)
- `packed_struct_desugar` → `compiler.common.attributes` (parse_layout_attrs to detect @packed)
- `flat_ast_bridge` → no new deps (just populate existing `Struct.attributes` field)
- `synth_driver_codegen` → `compiler.mir.synthetic_driver_registration` (plan_synthetic_driver_registration, SyntheticDriverRegistrationPlan)
- `synth_driver_codegen` → `compiler.mir.mir_instructions` (MIR call instruction construction)
- `synth_driver_codegen` → `compiler.common.attributes` (DriverManifestAttr)
- `synth_driver_codegen` → `compiler.hir.hir_definitions` (HirFunction)
- `mir_lowering` → `synth_driver_codegen` (apply_synthetic_driver_codegen)
- No circular dependencies: verified (all deps flow frontend→common, mir→hir→common)

### Public API

**packed_struct_desugar.spl:**
- `fn desugar_packed_structs(module: Module) -> Module` — scans `module.structs` for `@packed` attribute + fields with `has_bits == true`; moves matching structs to `module.bitfields` as `Bitfield` nodes; returns updated Module

**synth_driver_codegen.spl:**
- `fn apply_synthetic_driver_codegen(fn_: HirFunction, mir_blocks: [MirBlock], symbols: SymbolTable) -> [MirBlock]` — calls planner; if `ReadyToSynthesize`, appends MIR call `register_static_driver(manifest, ops)` to the last block; returns updated block list

**attributes.spl (modified):**
- `DriverManifestAttr` gains field: `has_ops_binding: bool`, `ops_binding: text` — explicit `ops = Name` from `@driver(... ops = MyOps)`

**types_def/mod.rs (modified):**
- Inside `parse_struct_with_attrs`: after constructing `StructDef`, check `is_packed_with_bitfields(attributes, fields)` → convert to `BitfieldDef` and return `Node::Bitfield(...)`

### Data Flow

**FR-DRIVER-0003 (`@packed struct`) — Self-hosted path:**
```
Source: @packed\nstruct Foo:\n    f: u16 @bits(4)\n    g: u16 @bits(12)
  → parse_struct_decl() → decl_struct_def(field_bits=[4,12])
  → flat_ast_bridge → Struct(fields=[Field(has_bits=true, bits=4), ...], attributes=[])
  → [NEW] flat_ast_bridge modified: attributes populated from flat AST attrs
  → [NEW] desugar_packed_structs(module)
      detects @packed + has_bits fields → synthesizes Bitfield(backing_type=u16, fields=[BitfieldField(bits=4), ...])
      moves from module.structs["Foo"] to module.bitfields["Foo"]
  → lower_module() → lower_bitfield(bf) [EXISTING] → HirBitfield
  → MIR/backend bitfield codegen [EXISTING] → shift+mask read/write
```

**FR-DRIVER-0003 (`@packed struct`) — Rust seed path:**
```
Source: @packed\nstruct Foo:\n    f: u16:4\n    g: u16:12
  → parse_struct_with_attrs(attributes=[Attribute("packed")])
      → fields=[Field(bit_width=Some(4)), Field(bit_width=Some(12))]
      → [NEW] is_packed_with_bitfields check → Node::Bitfield(BitfieldDef{...})
  → HIR lowering: Node::Bitfield arm [EXISTING]
  → MIR/backend bitfield codegen [EXISTING]
```

**FR-DRIVER-0001 (synthetic registration codegen):**
```
Source: @driver(class = DriverClass.Block, vendor = 0x1234, ops = my_ops)\nfn init():
  → parse → HirFunction(has_driver_manifest_attr=true, driver_manifest_attr=DriverManifestAttr{ops_binding="my_ops"})
  → lower_function(fn_)
      → lower body → MIR blocks
      → [NEW] apply_synthetic_driver_codegen(fn_, blocks, symbols)
          → plan_synthetic_driver_registration(fn_, symbols) → ReadyToSynthesize
          → append MIR call: register_static_driver(DriverManifest{class, vendor, ...}, my_ops)
      → return augmented MIR blocks
```

### Requirement Coverage

- REQ-1 (AC-1, AC-5) → `packed_struct_desugar.spl` (self-hosted), `types_def/mod.rs` (Rust seed)
- REQ-2 (AC-2) → existing bitfield codegen path (no new modules; `HirBitfield` routes through existing shift+mask)
- REQ-3 (AC-3) → existing bitfield codegen path (no new modules; `HirBitfield` routes through existing RMW)
- REQ-4 (AC-4) → test file (Phase 4 creates spec)
- REQ-5 (AC-6) → `synth_driver_codegen.spl` + `mir_lowering.spl` modification + `attributes.spl` modification
- REQ-6 (AC-7) → parallel agent (out of scope for this pipeline)

### Integration Points

1. **flat_ast_bridge.spl:778** — change `attributes: []` to pass through actual attributes from the flat AST. Requires checking if `decl_struct_def` stores attributes (currently it does not — only name, fields, types, defaults, bits, span). Two options: (a) extend `decl_struct_def` to accept attributes, or (b) have `desugar_packed_structs` detect packed structs by field bits alone (any struct with ALL fields having `has_bits == true` is treated as packed). **Decision: use option (b)** — if ALL fields have `has_bits == true`, the struct is a bitfield candidate regardless of explicit `@packed`. This avoids modifying the flat AST infrastructure and is functionally equivalent since bit-width fields are only meaningful on bitfields.

2. **Module pipeline insertion point** — `desugar_packed_structs` must run AFTER `flat_ast_bridge` builds the Module and BEFORE HIR lowering. The existing desugar passes (desugar_async.spl, desugar_coroutine.spl, etc.) run in this window. Add the call in the same desugar pipeline.

3. **MIR injection in `lower_function`** — must run AFTER body lowering produces MIR blocks, BEFORE the blocks are finalized. Insert at ~line 467 (after `lower_function:bootstrap:done` for bootstrap mode, or after the normal body lowering return point).

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
