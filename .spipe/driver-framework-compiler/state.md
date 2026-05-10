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
- [ ] 2-research (Analyst)
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
<pending>

### 3-arch
<pending>

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
