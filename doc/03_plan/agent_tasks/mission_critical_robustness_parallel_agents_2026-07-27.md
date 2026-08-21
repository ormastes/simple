# Mission-Critical Robustness — Parallel Agent Dev Plan

**Date:** 2026-07-27 (verified against source 2026-07-28)
**Research base:** `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`
(§13 verification appendix has file:line ground truth for every premise below).
**See also (2026-08-21):** the completeness/Any/mono/aspect hardening lanes extend this plan's wave model — `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md` (waves 0–5) and `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md`.


**Principle:** shared contracts first (serial Wave 0), then agents work individually on
disjoint file ownership. No agent edits a shared dispatcher, root export, or aggregate
doc. Scope manifests enforced via `git diff --name-only` comparison.

---

## Wave 0 — serial contract lock (1 architect + 1 reviewer, blocks everything)

Freeze these schemas/interfaces before any feature agent starts:

| Contract | Deliverable |
|----------|-------------|
| Assurance profile schema | `doc/02_requirements/language/mission_critical_profile.md` + sdn schema |
| Primitive-type-graph API | one canonical primitive table + recursive-reachability API signature |
| SymbolId schema | 128-bit hash inputs/exclusions, `doc/04_architecture/compiler/semantic_symbol_id.md` |
| Semantic-link URI grammar | `spl:` / `spl://` forms, kind disambiguators, fingerprint rules |
| Verification IR schema | `doc/04_architecture/compiler/verification_ir.md` |
| Lean proof-state + trust-manifest schema | extends existing `verification/state.spl` states |
| Accelerated IR op vocabulary | semantic op families + attribute set |
| ISA registry schema | `spec/isa/schema` + row format |
| Rust feature-ledger schema | `doc/08_tracking/rust_feature_assurance.sdn` row format |
| Diagnostic IDs | `W-DOC-AST-001` etc., reserved ranges per lane |
| Evidence-manifest format | shared by release gate |

Hotspot removal (also Wave 0, because verified ground truth shows shared files):

- **Unify the 3+ divergent primitive tables** (`primitive_api.spl:20`,
  `rules.rs:6-8`, `primitive_api_arena.spl:35-38`, `query_lint.spl:99-102`,
  `lint_primitive_api.spl:21-24`) into ONE generated table consumed by all engines.
  This alone fixes the bool contradiction everywhere at once.
- Add parser extension hooks in `src/compiler/10.frontend/core/_ParserDecls/` so enum
  agents (A3/A4) don't both edit `parser_decls_types.spl`.
- Registry hooks instead of central `match` in `gpu_intrinsics.spl:17` and
  `cuda_backend.spl:616+` (structural IDs replace string dispatch).
- Backend registration fragments so D1-D6 never touch a common dispatcher.
- Scope manifest format + CI check script under `scripts/check/`.

---

## Wave 1 — parallel foundations (5 agents, independent)

| Agent | Exclusive ownership | Deliverable | Verified starting point |
|-------|--------------------|-------------|------------------------|
| A1 API semantic checker | `src/compiler/35.semantics/lint/semantic_api/**` | Recursive normalized-type-graph checker (post-resolution, never text) | Replace text paths `query_lint.spl:122-162`, fix bool omission `primitive_api.spl:20`; kill `_all_same_primitive` in MC profile (`lint_primitive_api.spl:158-167`); stop skipping `extern fn` — generate checked wrappers instead |
| B1 Semantic identity | `src/compiler/20.hir/semantic_id/**` | Stable SymbolId, index build, collision checks, redirect table | Nothing reusable: HIR SymbolId is compile-local i64 (`backend/env.spl:25-29`); fingerprint precedent = `llm_process_gen` sha256 markers |
| C1 Verification IR | `src/compiler/60.verification/vir/**` | Typed V-IR + validation | Bridges the two Lean systems (`70.backend/backend/lean_*` vs `compiler_rust/lib/std/src/verification/lean/`) |
| D0 ISA registry generator | `tools/isa_registry/**`, `spec/isa/**` | Registry parser + generated coverage tables | Doc drift proven: `simd_implementation_status_2026-05-02_evening.md:146,295` claims RVV absent; tree has `riscv_rvv.spl` + 8 encoders |
| E1 Rust ledger importer | `tools/rust_assurance/**` | Pinned Reference/FLS section importer + shard merger | New |

Also Wave 1 (small, independent): **fix newunit registry scaffold**
(`src/compiler/30.types/units/unit_registry.spl:253-282` no-op collector) — A1's checker
depends on newunit actually being registered. Fix the `newtype` typo suggestion
(`primitive_classification.spl:86`).

---

## Wave 2 — parallel feature lanes

### A lane — API + enums
| Agent | Exclusive area | Notes |
|-------|---------------|-------|
| A2 | Primitive baseline + migration fixer | Baseline keyed by SymbolId+signature; replace no-op EasyFix (`lint_primitive_api.spl:128-151` currently returns the original line) |
| A3 | `@condition` two-state enums | Via Wave-0 parser hooks |
| A4 | Closed + evolving enums | Prereq: enum payload metadata — parser currently discards payloads (`parser_decls_types.spl:122-149`) and `decl_enum_def` takes names only (`decl_nodes.spl:586`) |
| A5 | Boundary manifests (FFI/layout/hardware/intrinsics) | `@representation_boundary` |

### B lane — semantic md links (LSP + lint + refactor share ONE resolver)
| Agent | Exclusive area | Notes |
|-------|---------------|-------|
| B2 | `std.tooling.semantic_link` resolver + `simple ast-link` | Interval index over span pool (`types.spl:94-101`); consumes B1 index read-only |
| B3 | Markdown lint + fixer | Hook into existing `.md` walk `_LintMain/lint_checks.spl:645` (`check_stale_md_diagrams` precedent); rewriter precedent `md_diagram_update`; extend `llm_process_gen` `should_check_link:646` to accept `spl:` URIs. New rule `W-DOC-AST-001`. Command is `simple doc check-links` — NOT `check-links` (that's linker dep resolution, `src/app/cli/check_links.spl`) |
| B4 | Doc renderer integration | `spec_gen/markdown.spl:128` + spipe_docgen emit semantic links |
| B5 | LSP + rename | LSP has NO rename today (`render_adapter.spl:53-62`); `query rename` is grep+sed over `src/**/*.spl` only (`query_navigation.spl:14`) — B5 builds semantic rename that atomically rewrites `.md` links + emits SymbolId redirects; definition/hover work from inside `.md` on `spl:` links |

### C lane — Lean
| Agent | Exclusive area | Notes |
|-------|---------------|-------|
| C2 | Type/data export | Replace stub `lean_backend.spl:351-356` |
| C3 | Contract + obligation extraction | Replace `FunctionContract.empty` (`:400`) and `pass` (`:405-409`) |
| C4 | Structured CFG + loops | `lean_mir_translate.spl:232-261` rejects Goto/If/Switch/Call — add structured translation, keep fail-closed |
| C5 | Mutable state, arrays, memory model | BitVec semantics, no silent Int |
| C6 | Proof workspace, cache, trust manifest | Also fix substring `_count_sorry` (`verify/checker.spl:246-254`) — checked-in proofs are already 0-sorry but comment prose false-positives |
| C7 | Translation-validation + negative tests | Intentionally-faulty compiler tests |

### D lane — ISA/accelerator (registration fragments, no shared dispatcher)
| Agent | Exclusive area | Notes |
|-------|---------------|-------|
| D1 | `backend/native/_X8664Avx512/**` + x86 shard | AVX10, AMX later |
| D2 | `backend/native/_ArmNeon/**`, `arm_sve2.spl` + arm shard | SME after SVE2 complete |
| D3 | `backend/native/riscv_rvv.spl`, `encode_rvv_*.spl` + riscv shard | RVV 1.0 completeness vs registry |
| D4 | `backend/cuda/**` + PTX shard | **Fix first:** wire `cuda_type_mapper.spl:272-295` (correct sizes exist, unused) into `cuda_backend.spl:565-611` 8-byte assumptions; bump hardcoded `.version 7.8` (`ptx_builder.spl:67`); widen `gpu_portable_compute.spl:18-20` beyond U32/F32 |
| D5 | `backend/spirv/**` | |
| D6 | amdgpu | |
| D7 | `test/isa_conformance/**` | byte-golden, roundtrip, llvm-mc diff, emulator lanes |

### E lane — Rust ledger shards
7 shard agents (syntax/modules; types/generics/traits; ownership/unsafe; concurrency/
async; ABI/FFI/codegen; stdlib; tooling). Generator merges deterministically; agents
never edit one shared ledger file.

---

## Wave 3 — parallel validation

Public-API migration dry run · semantic-link migration over all maintained `.md` · Lean
proof-coverage audit · ISA completeness audit · encoder/assembler differential · GPU
semantic differential · Rust ledger completeness · doc generation + stale-link detection
· reproducible-build comparison · deliberate false-green injection.

## Wave 4 — serial integration + red-team

Single integration owner edits root exports, pipeline registration, profile config,
aggregate release gate, generated indexes. Independent reviewer attacks: primitives
hidden via aliases/containers, invalid enum reprs, moved/renamed linked decls, wrong Lean
translations, hidden sorry/axioms, unsupported CPU feature selection, forced scalar
fallback, corrupted registry metadata, missing tools, stale evidence. Only the aggregate
gate may emit "production ready".

## Scope enforcement

```sdn
(agent_scope
  id: "D3-riscv"
  allow: ["src/compiler/70.backend/backend/native/riscv_rvv.spl",
          "src/compiler/70.backend/backend/native/encode_rvv_*.spl",
          "test/isa_conformance/riscv/**", "spec/isa/riscv.sdn"]
  deny:  ["src/compiler/50.mir/**",
          "src/compiler/70.backend/backend/mod.spl",
          "doc/08_tracking/isa_coverage.sdn"])
```

CI compares `git diff --name-only` with scope; out-of-scope edit fails the agent gate.
Shared-interface changes require a serial contract-lock mini-wave.

## Batch 2 — safety-property enforcement lanes (added 2026-07-28)

**Profile naming (2026-07-28):** Profile ladder renamed to moderate, strict (formerly lib), robust (formerly reliable), critical (formerly mission-critical). Old spellings are deprecated aliases. See `doc/02_requirements/language/mission_critical_profile.md` § Profile ladder rename for engine axis + default pairing (interpreter→moderate default; compiler/loader→robust at WARN).

Source: `doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`
(verified matrix + G1-G10 gap list + 4-category classification). Goal: close the
enforcement gaps so the robust spec's Rust-parity claims become executable.

| Lane | Exclusive ownership | Work (evidence-anchored) |
|------|--------------------|--------------------------|
| SF1 `borrow-feed` (G1) | `src/compiler/50.mir/mir_data.spl`, `_MirLoweringExpr/expr_dispatch.spl`, `55.borrow/borrow_check/**` | Emit `Move` at move sites (`emit_move` has ZERO callers, `mir_data.spl:337-343`); propagate `moved_places` forward across program points (`borrow_graph.spl:439-461` same-point-only); emit `Ref` for reference-semantic class params (today only unary `&`/`&mut`, `expr_dispatch.spl:2241-2243`); ALSO fix the silent bounds-check bailout on untyped base (`expr_dispatch.spl:856-861`). Reproduce-first red specs: use-after-move, move-then-use-later-point |
| SF2 `unsafe-boundary` (G3) | `src/compiler/35.semantics/safety_checker.spl`, self-hosted `unsafe:` parsing hooks, driver invocation site | Fix "pass never invoked" (`doc/08_tracking/bug/safety_checker_pass_never_invoked_2026-07-27.md`); construct dead rules `RawPointerOutsideUnsafe`/`UnsafeFfiOutsideUnsafe` (`safety_checker.spl:20-21`); parse `unsafe:`/`danger:` in self-hosted frontend (`KwUnsafe` declared unused, `lexer_types.spl:42`); default warn-on (not env-gated); capability-scoped `@unsafe(reason, capabilities:[...])` annotation parsed + recorded (enforcement of scope = later) |
| SF3 `mir-interp-oob` (G4) | `src/compiler/95.interp/mir_interpreter.spl` | OOB currently returns 1 silently (`:634-643`) — trap loudly like `runtime.c:1817-1823`. Red spec proving silent-wrong before, loud after |
| SF4 `mutex-guard` (G5) | `src/lib/*/concurrent/mutex.spl`, `rwlock.spl` (all 4 tier copies) | RAII guard type + `with lock.lock() as guard:` pattern; implement the EMPTY async-tier mutex stub; guard-use-after-unlock impossible by construction; keep manual API as deprecated-warn |
| SF5 `generation-handles` (G6) | `src/lib/nogc_sync_mut/engine/resource/handle.spl`, `storage/arena.spl`, `engine/core/object_pool.spl`, `db/dbfs_engine/raw_nvme_arena.spl` | Promote `HandleArena<T>` to canonical; migrate storage-arena + object-pool schemes onto it; FIX NVMe generation≡0 (`raw_nvme_arena.spl:160,178` — handles not actually protected); red spec: stale NVMe handle accepted before, rejected after |
| SF6 `doc-truth` (G10) | the 6 conflict docs only | Fix "Simple has no unsafe" (`rust_to_simple_error_mapping.md`); false COMPLETE claims (`memory_model_implementation.md:5`, `MEMORY_VERIFICATION_COMPLETE.md:208-235` → mark actual status w/ evidence links); annotate `capability_system.md` unsafe-allows-all + `effect_system.md` @unsafe rows as superseded-by mission-critical boundary model; note extern-wrapper requirement in `extern_functions.md` |

Deferred to Batch 3 (dependencies): G2 semantic param-mutability/E1047 (conflicts with
SF1 file ownership; R lint is its warn phase), G7 iterator invalidation (needs G2), G8
Transfer/Share capabilities (needs contract lock), G9 cancellation effects, Cat-4
Miri-mode (builds on SF3), editions, SBOM tool, registry unification, Pin-alternative,
**PE profile-aware execution (REQ-MC-012, user design)**: `run`/`test` accept
`--profile=moderate|strict|robust|critical` (today lint-only); profile gates
pre-run lint fail-closure + runtime check strictness (bounds/MIR-interp traps,
sanitizers); `simple.sdn [lints] profile=` as package default, CLI overrides.
Depends on R2's mission-critical profile skeleton + SF3's trap mode.
**PR2 profile-rename-and-defaults lane**: implement deprecated aliases + compiler/loader robust-at-warn default phasing; queues behind R2 (same config file).

Cross-lane rules: SF1 exclusively owns `expr_dispatch.spl` — SF3 does NOT touch MIR
lowering. All lanes: reproduce-first red specs for defect fixes; A/B both engines on
behavioral claims; no commits (orchestrator merges).

## Batch 2.5 — profile rules landed alongside Batch 2 (2026-07-28)

| Lane | Ownership | Work |
|------|-----------|------|
| R `const-ref` (AC-7) | `35.semantics/lint/const_ref_default.spl` + registration | W-MC-REF-001 warn all tiers — DONE, 14/14 |
| R2 `bare-primitive-internal` (AC-8) | `35.semantics/lint/bare_primitive_internal.spl` + `config_and_model.spl` mission-critical profile skeleton | W-MC-VAL-001 allow-default, warn in critical profile; digit-separator-aware suffix detection — landed, spec verification pending runner |

## Batch D — Debug and Evidence Spine (added 2026-07-28, all defects repo-verified)

Source: `doc/01_research/language/simple_vs_rust_debug_logging_2026-07-28.md`
(§Verification = file:line ground truth; RAG matrix; P0-P2). Goal: debug/logging equal
or better than practical Rust (rustc DWARF controls + tracing/OTel + tokio-console +
sanitizers/Miri). Milestone name: **Debug and Evidence Spine v1** — one identity model
(SourceAnchor → SymbolId → BuildId → ExecutionId → TraceId/SpanId → TaskId/ActorId),
not another standalone subsystem.

| Lane | Exclusive ownership | Work (verified anchors) |
|------|--------------------|--------------------------|
| DS1 `span-truth` | `00.common/diagnostics/span.spl` + spec | Fix `merge()` file/length loss (`span.spl:48-53` routes through `Span.new` which hardcodes `file:"", length:0`; `to()` :33-45 is the correct model). Red-first spec |
| DS2 `diagnostic-v1` | new `00.common/diagnostics/diagnostic_v1.spl` + SDN schema | Canonical DiagnosticV1 (children, multi-file labels, expansion chain, fixes w/ applicability, stable codes) closing native (`diagnostic.spl:9-16`) vs Rust (`diagnostic.rs:26-57` EasyFix/Replacement/FixConfidence/JSON) drift; JSON renderer first, LSP/SARIF later |
| DS3 `dwarf-wire` | `70.backend/backend/llvm_backend.spl`, `llvm_ir_builder.spl` | Wire the DEAD DWARF emitters (`llvm_ir_builder.spl:468-489` `emit_debug_info_header`/`emit_di_subprogram` — zero callers) into `compile_module` (:256-323) gated on `debug_info`; add `--debug-info=none\|line-tables\|full` CLI; system gate = real `llvm-dwarfdump` on a compiled binary |
| DS4 `log-dispatch` | `src/lib/log.spl` + spec | Fix `log_dispatch_text` (:574-584) dummy-p0 defect so text reaches ring backends outside panic mode; add context_id/callsite_id fields to the record WITHOUT breaking 40-byte no-alloc fast path (two-tier: FastEventRecord + hosted EventV1 enrichment on drain) |
| DS5 `mir-span-thread` | `50.mir/mir_data.spl` emit_* signatures + lowering callers | Thread spans through the 21 `span: nil` emit sites (`mir_data.spl:305-595`) — **queues behind SF1** (same file ownership). Enables debugger line maps, replay locations, coverage |
| DS6 `gdb-transport` | `debug/remote/protocol/gdb_mi.spl`, `dap/adapter/gdb_mi.spl` | Replace mkfifo/`sh -c`/`echo`/`timeout grep` transport with real subprocess pipes + streaming MI parser + token table; stop discarding condition/hit/log on rich breakpoints (:265-271) |
| DS7 `crash-native` | new `src/lib/*/crash/**` + runtime hook | POSIX signal-safe SIGSEGV/SIGABRT capture → CrashBundleV1 (build id, fault addr, registers, stacks, recent ring records); guide currently marks this "Planned" (`crash_containment.md:163`) |
| DS8 `otlp-bridge` | `web_framework/tracing.spl` exporter + `src/lib/*/observe/**` | ObserveContext shared by std.log/tracing/scheduler; OTLP export replacing JSON-array exporter (:321-326); W3C context already correct — reuse |

Later (P1/P2, after v1): DAP capability honesty sweep, async console (tokio-console
class), sanitizer profiles (`--sanitize=`), checked-interpreter Miri mode (builds on
SF3), BuildManifest/symbolizer, traceability graph, replay-in-debugger.

## Batch 3 additions (2026-07-28, closing audit Category-4 lane gaps)

- **PT `platform-tiers`:** documented tier-1/2/3 platform policy + per-tier CI guarantees
  (27 workflows exist; no policy doc).
- **FZ `coverage-fuzz`:** wire existing corpus fuzz (`test/06_fuzz/`) to coverage
  feedback via in-stdlib sanitizers; harness generator.
- **AM `unsafe-aliasing-model`:** define the simplified Tree-Borrows-style model for raw
  pointers (doc + checked in the Miri-mode interpreter when it lands).

## First merge batch (order)

1. Wave-0 contract lock + unified primitive table (fixes bool contradiction repo-wide).
2. newunit registry scaffold fix + `newtype` typo fix.
3. A1 semantic checker replacing text scanners.
4. B1 SymbolId foundation.
5. D4 CUDA layout wiring + PTX version (small, high-value, verified-independent).
6. C6 `_count_sorry` matcher fix (tiny).

Broad backend fan-out (D1-D6 coverage expansion) only after registry + contracts freeze.
