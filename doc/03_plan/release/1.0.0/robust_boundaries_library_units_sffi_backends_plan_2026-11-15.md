# Simple Robust Boundaries, Library Units, SFFI, and Optional Backend Hardening

**Integrated architecture, source audit, migration, implementation, and verification plan**
**Date:** 2026-11-15
**Branch:** `release/1.0.0` (audit inspected `830879893c3`)
**Status:** Design and source-inspection plan. "Existing" = source inspected; "proposed" = to implement and validate. Not a build/test claim.

## Implementation log

| Date | Slice | What landed | Evidence |
|---|---|---|---|
| 2026-11-16 | rb4-unitmethod | Seed `call_method_on_value` gains a `Value::Unit` arm: chained `opt.unwrap().value()` / `.to_i64()` work (bug `seed_unit_value_nested_method_dispatch_2026-11-16.md`, verification-pending); pure-Simple parity not audited | `test/01_unit/compiler/interpreter/unit_nested_method_dispatch_spec.spl` |
| 2026-11-15 | D (policy scaffold) | `SPL-BOUND-001..003` (warn, no ratified error date), `SPL-SFFI-ABI-001`, `SPL-SFFI-RANGE-001` (deny now via the `security` stage, `exception_policy: forbidden`) registered in `config/policy/diagnostic_policy.sdn`. Policy only: no detector emits these codes yet (slices B/C) | `test/01_unit/compiler/diagnostics/diagnostic_rule_policy_spec.spl` |
| 2026-11-15 | B (bound001) | `SPL-BOUND-001` (raw extern result returned unconverted from a non-boundary fn: `return raw` / final bare `raw`, declared non-Nil return) and `x as Unit` form for `SPL-BOUND-002`, in `bound_late_cast.spl`; same lint row and code mapping. Function-local only. The old no-leak spec fixture now returns `text` via `format_num(raw)` because a bare `raw` return is exactly what 001 flags | `test/01_unit/compiler/lint/bound_late_cast_spec.spl` |
| 2026-11-15 | 3.2 (SFFI ABI width) | `SPL-SFFI-ABI-001` detector `check_sffi_abi_mismatch(source, path, triple)` over `@c_abi(Unit: "ctype")` annotations; target C ABI table (`c_target_data_model`, `c_scalar_underlying`: lp64/llp64/ilp32) in `30.types/custom_primitive_info.spl`; unknown target/C type rejected. Not yet in lint registry (triple is an input) | `test/01_unit/compiler/lint/sffi_abi_mismatch_spec.spl` (6/6) |
| 2026-11-15 | B1 (SPL-BOUND-002 detector) | `src/compiler/35.semantics/lint/bound_late_cast.spl` + lint row `bound_late_cast` (warn): function-local foreign origin (raw extern result + `val` copies) cast to a file-declared or `use unit.`-imported unit outside an `@unsafe(capabilities: [ffi])` adapter. Limits: no cross-function/cross-file return summaries (needs typed HIR, slice B2); `x as Unit` form not yet matched | `test/01_unit/compiler/lint/bound_late_cast_spec.spl` 19/19, `static_rule_dispatch_identity_spec.spl` 5/5 |
| 2026-11-15 | B2 step 1 (same-file cross-function origin) | `bound_late_cast.spl`: per-file fixpoint summaries; a non-boundary fn returning a bare foreign call / plain copy makes calls to it foreign for SPL-BOUND-002 (one/two hops, recursion terminates, `@unsafe` ffi adapter returning a unit breaks the chain). GAP: cross-file and typed-HIR summaries, and conversion-through-wrapper precision, remain open. | `bound_late_cast_spec.spl` 38/38 passed |
| 2026-11-15 | A1 (source inventory receipt) | `src/compiler/80.driver/driver_build/source_inventory_v1.spl`: pure `source_inventory_receipt_v1` (sorted, sha256-digested, `completeness: complete`) and `source_inventory_ownership_check_v1` (duplicate owners + orphans as `SPL-BUILD-SRC-001`). Gap: no glob resolver wired in, no CLI (`build sources`/`doctor`), no manifest-drift check. | `test/01_unit/compiler/80.driver/source_inventory_v1_spec.spl` |
| 2026-11-15 | F2 (unit glob resolution) | `driver_build/source_inventory_glob_v1.spl`: pure `source_inventory_glob_match_v1` (`*`, `?`, `**`) and `source_inventory_resolve_unit_v1` (includes minus excludes over a frozen scanned list, sorted, de-duplicated). Gap: no filesystem scan, no simple.sdn unit-manifest parser, no digest attach, no `build sources` CLI. | `test/01_unit/compiler/80.driver/source_inventory_glob_v1_spec.spl` (4/4) |
| 2026-11-15 | B3 (SPL-BOUND-003 detector) | `src/compiler/35.semantics/lint/bound_unit_reassert.spl` + lint row `bound_unit_reassert` (warn): function-local unit A erased via `.value`/`.raw()`/`.to_f64()`/`.to_i64()` (origin: unit-typed params, `Unit(...)` locals, copies/arithmetic) then cast to a different unit B. Same-unit recast allowed. Spec `test/01_unit/compiler/lint/bound_unit_reassert_spec.spl`. Gap: no cross-function summaries, no `as` casts. |
| 2026-11-15 | 7.3 (SPL-BOUND-002 autofix) | `src/compiler/90.tools/fix/rules/impl_/bound_late_cast_fix.spl`: review-required (Uncertain, never Safe) `FixCandidate` creating/reusing an `@unsafe(reason: "TODO verify C ABI", capabilities: [ffi])` adapter `<extern>_as_<unit>` and rewriting the late cast site; aborts when extern args are not literals (locals) or the cast wraps a local copy. Reuses `check_bound_late_casts`; applies via `EditTransaction` preconditions. Gaps: not yet registered in the fix CLI/LSP producer; single-file, direct `Unit(ext(lit))` only | `test/01_unit/app/fix/bound_late_cast_fix_spec.spl` 7/7 |
| 2026-11-15 | 7.3 (SPL-BOUND-002 autofix) | `src/compiler/90.tools/fix/rules/impl_/bound_late_cast_fix.spl`: review-required (Uncertain, never Safe) `FixCandidate` creating/reusing an `@unsafe(reason: "TODO verify C ABI", capabilities: [ffi])` adapter `<extern>_as_<unit>` and rewriting the late cast site; aborts when extern args are not literals (locals) or the cast wraps a local copy. Reuses `check_bound_late_casts`; applies via `EditTransaction` preconditions. Registered as fix producer `SPL-BOUND-002` in `rules/registry.spl` (+ `impl_/__init__.spl`), spec `test/01_unit/compiler/tools/fix/bound_late_cast_registry_spec.spl` 3/3. Gaps: single-file, direct `Unit(ext(lit))` only | `test/01_unit/app/fix/bound_late_cast_fix_spec.spl` 7/7 |
| 2026-11-15 | F prereq 2 (deterministic canonical type ids) | `canonical_type_symbol_id_v1` digest ids replace the insertion counter in `canonical_mir_type_symbol_for_key_v1`; collision re-hash; MC/DC ids and cross-process byte-identity still open (see slice5 prerequisites bug) | `test/01_unit/compiler/mir/canonical_type_symbol_id_spec.spl` 4/4 |
| 2026-11-15 | G (§6.1 backend groups) | Opt-in `config/build/backends_{c,vhdl,cuda,rocm,vulkan}.sdn` (`default: false`, one `kind: shared` target each, entry = existing `*_backend.spl`), included from `targets.sdn`; default host selection unchanged. `build_targets.spl` parse/select fns made `pub` (sibling spec was ERROR on visibility). Gaps: no `provider_entry.spl` anywhere; `runtime_gpu.sdn` not added (no Simple entry source); no `backend_rocm` dir (HIP used) | `test/01_unit/app/build/targets_backend_groups_spec.spl` 3/3, `targets_include_group_spec.spl` 10/10 |
| 2026-11-15 | C1 (constrained unit SFFI return) | `src/compiler/90.tools/sffi_gen/constrained_unit_gen.spl`: input model `ConstrainedUnitReturn` (integer range_min/range_max) -> validating facade `Result<Unit, ConstraintError>` over a private `__raw_` extern; unconstrained unit = direct projection; non-integer ABI or non-literal bound emits `SPL-SFFI-RANGE-001`. Gaps: no unit range syntax or parser feed, `ConstraintError` not yet defined in stdlib, not wired into module_gen | `test/01_unit/compiler/sffi_gen/constrained_unit_return_spec.spl` |
| 2026-11-15 | E1 (unit verdict loader parity) | `test/01_unit/compiler/units/unit_loader_parity_spec.spl`: unit_op verdict matrix (nominal/point/index/alias/legacy newtype) and interpreter `unit_value_binop` results identical after `flat_type_pools_dump` / `flat_type_pools_restore` (the loader/cache pool path). Also removed dead `next_canonical_type_symbol` field + sync copies. Gaps: loader iface_digest/ABI/capability validation not covered; no real SMF file round trip | `unit_loader_parity_spec.spl` |
| 2026-11-15 | boundfollow (SPL-BOUND review follow-ups) | bound_late_cast: compound assignment keeps taint, unit return type skips BOUND-001, multi-line fn headers, parenthesised/wrapped and if/else branch-final raw returns, Nil spec now returns raw; bound_unit_reassert: multi-line headers + non-ASCII line guard | bound_late_cast_spec 37/37, bound_unit_reassert_spec 11/11 (spec cases for the 3 reassert-side items 2/11 pass; non-ASCII case does not prove red-before) |
| 2026-11-15 | boundfollow (SPL-BOUND review follow-ups) | bound_late_cast: compound assignment keeps taint, unit return type skips BOUND-001, multi-line fn headers, parenthesised/wrapped and if/else branch-final raw returns, Nil spec now returns raw; bound_unit_reassert: multi-line headers + non-ASCII line guard | bound_late_cast_spec 37/37, bound_unit_reassert_spec 11/11 (red-before not separately observed for the non-ASCII case) |
| 2026-11-15 | C1b (rangewire) | `src/lib/common/constraint_error.spl` real `ConstraintError` (unit_name/value/min_text/max_text/message, `out_of_range`); `sffi_gen/constrained_unit_scan.spl` scans `unit X: T as S` + `# @unit_range X lo..hi` + `extern fn ... -> X` text into facades via constrained_unit_gen. Gaps: range is an annotation comment (no `unit` range syntax); not yet a CLI flag/module_gen step; facade run in interpreter via hand-copied shape, not eval of generated source | `test/01_unit/compiler/sffi_gen/constraint_error_spec.spl`, `constrained_unit_facade_wire_spec.spl` |
| 2026-11-15 | C1b (rangewire) | `src/lib/common/constraint_error.spl` real `ConstraintError` (unit_name/value/min_text/max_text/message, `out_of_range`); `sffi_gen/constrained_unit_scan.spl` scans `unit X: T as S` + `# @unit_range X lo..hi` + `extern fn ... -> X` text into facades via constrained_unit_gen. Gaps: range is an annotation comment (no `unit` range syntax); not yet a CLI flag/module_gen step; facade run in interpreter via hand-copied shape, not eval of generated source; emitted `Ok(Unit(raw))` cannot run today (doc/08_tracking/bug/unit_from_primitive_construction_unsupported_runtime_2026-11-15.md), form left unchanged pending owner decision | `test/01_unit/compiler/sffi_gen/constraint_error_spec.spl`, `constrained_unit_facade_wire_spec.spl` |

Reconcile with (do not fork): `unit_primitive_api_lane_plan_2026-11-12.md`,
`doc/05_design/compiler/incremental_build/library_unit_build_and_link.md`,
`doc/08_tracking/bug/library_unit_build_slice5_prerequisites_2026-11-13.md`,
`doc/05_design/compiler/backend_dynamic_plugin_build_groups.md`,
`doc/07_guide/platform/ffi/sffi.md`, `doc/03_plan/agent_tasks/sffi_v2_hardening.md`.

## 0. Executive decisions

1. `text` stays a built-in general-purpose type, never automatically a semantic `unit`. Numeric primitives stay legal in private arithmetic and general math APIs.
2. A semantic `unit` is an intentional guarantee with four independent facts: nominal identity, representation/ABI, dimension/scale, invariant.
3. Establish a semantic unit at the origin boundary (typed SFFI return / generated adapter, HAL wrapper, or admitted binary-provider ABI adapter). Late raw-to-unit casts on foreign-origin data warn, ratcheting to error in robust. No repeat casts across library calls.
4. SFFI may project an ABI-identical C primitive directly as an unconstrained unit. A constrained unit is checked before it is trusted; the safe facade is fallible (`Result<Unit, ConstraintError>`) unless a verified producer contract proves the constraint. C `int` is checked against the target ABI, never assumed `i32`.
5. Dimensionally sound synthesis (`1km / 2hr` -> `0.5km/h`) is not a foreign cast; numeric promotion and scale are defined. Nominal domain mixing is rejected unless declared in `unit_ops`.
6. Robust enforcement is scoped per build unit (library/runtime/application/shared). Each unit has a generated, sorted, hashed source-membership receipt resolved from canonical config; no handwritten path copies.
7. Compiler, interpreter, loader, runtime and stdlib families become separately built units linked via validated interfaces. Keep the single-closure bootstrap until library-unit parity is proven.
8. Default bootstrap builds only essential host components. Cross-OS/CPU codegen, VHDL, CUDA, ROCm/HIP, Vulkan/SPIR-V, runtime GPU providers and SIMD tiers are opt-in groups, loaded on demand after ABI/capability admission.
9. Extend `DiagnosticV1`, `DiagnosticRulePolicy`, the semantic exported-type checker and the revision-checked fix transaction. Ranked, previewable boundary-return fixes; never a no-op or a falsely-Safe unsafe conversion.
10. Compatibility first: inventory + warnings, then CI blocks new violations, then robust errors in a ratified edition. Fatal ABI, invalid arithmetic and security violations are never demoted to warnings.

Not in scope: new keywords for text/casts/build; global replacement of every `text`/`i64`; a second type system for interpreter/LSP/loader/SFFI; activating all backends in host bootstrap; calling a plugin production-ready because a header/stub exists.

## 1. Source audit

| Area | Evidence | Finding | Required work |
|---|---|---|---|
| Primitive classification | `35.semantics/lint/primitive_types.spl`, `semantic_api/tag_walk.spl` | Numeric/bool leaves flagged; `text`/`char` classified but not flagged by default | Keep; add contextual boundary findings, no blanket `text` ban |
| Public API traversal | `semantic_api/exported_graph.spl` | Exported graph over interned tags, visibility, nested types; re-export limits noted | Add build-unit policy + semantic-origin facts |
| Primitive autofix | `90.tools/fix/rules/impl_/lint_primitive_api.spl` | No-op EasyFix already removed; ranked substitutions are review-required | Add boundary-move multi-file actions |
| Diagnostic policy | `00.common/diagnostics/diagnostic_rule_policy.spl`, `config/policy/diagnostic_policy.sdn` | Per-rule/profile edition+date severity; dates illustrative | Add origin/cast/boundary rules (done: see log); ratify schedule |
| Diagnostics/edits | `src/lib/common/diagnostics/diagnostic_v1.spl`, `fix_transaction.spl` | Rich diagnostics + hash-checked edit transactions | Wire all paths to the same IDs/policy snapshot |
| Units | `30.types/units/unit_registry.spl`, `unit_ops.spl`, `src/app/interpreter/expr/arithmetic.spl` | Catalog + shared op matrix + interpreter wiring | Test dimension vs nominal, scale, promotion, constrained construction, parity |
| SFFI | `sffi_custom_primitive.spl`, `30.types/custom_primitive_info.spl`, `90.tools/sffi_gen/type_mapping.spl` | Transparent ABI mapping exists; checked fallible constrained return not established | Constrained return contract, stub gen, provenance, real ABI fixtures |
| Raw extern calls | `35.semantics/lint/raw_sffi_call.spl` | Raw externs + `@unsafe(capabilities:[ffi])` linted | Boundary rule independent but co-reported |
| Compiler ownership | `src/compiler/simple.sdn` | One application owns all layers; critical profile with broad exception string | Extract libraries; audited expiring permissions |
| Library units | `driver_build/library_unit_{plan,iface,archive,graph,link}_v1.spl` | Pure slices exist; unit-scoped lowering/link unwired | Lower from dependency interfaces, deterministic IDs, archive/link |
| Library-unit blockers | `library_unit_build_slice5_prerequisites_2026-11-13.md` | Independent lowering; order-dependent `canonical_type_symbols`/MCDC IDs; manifest dependency drift | Solve before `--library-units` in production |
| Targets/groups | `targets.sdn`, `src/app/build/targets/build_targets.spl`, `config/build/*` | `include:`/`group` supported; host default group; opt-in stdlib static | Consolidate optional configs |
| Dynamic backends | `70.backend/backend_plugin/*`, `simple_backend_plugin_v1.h` | Versioned ABI + checked staging; CUDA placement still `static` | Real provider exporters/descriptors/admission before selection |
| Runtime GPU provider | `src/runtime/runtime_dynload.c` | Separate lifecycle, partly present | Share identity/admission, not the codegen ABI |
| Loader split | `99.loader/loader/module_loader.spl`, `10.frontend/core/interpreter/module_loader_core.spl` | Separate lifecycles; shared-core refactor planned | One ABI/interface/receipt contract |

## 2. Type and conversion semantics

| Usage | Normal | Robust |
|---|---|---|
| local `text`, formatting, logging | allow | allow |
| `fn echo(message: text) -> text` | allow | allow (genuinely arbitrary text) |
| `fn read_user(id: text)` across a declared semantic boundary | diagnostic | error after ratification |
| `fn sum(a: i64, b: i64)` in a math module | allow | allow / targeted exemption |
| public `lba: u64`, `timeout_ms: i64` | `SPL-TYPE-001` | existing deny |
| `static const NAME: text = "Simple"` | allow | allow |
| `static const NAME: AppName = "Simple"` | const-eval validated | compile error on violation |
| `UnitX -> primitive -> UnitY` in app code | `SPL-BOUND-003` | error after ratchet |
| typed unit across library calls | allow | allow |

Checked domain constructors on genuine Simple-origin data stay legal. The restriction is: foreign-origin semantic assertions only at approved, auditable trust boundaries.

## 3. Boundary and SFFI contracts

SFFI decision matrix:

| C ABI return | Simple return | Verdict | Generated behaviour |
|---|---|---|---|
| `int32_t` | unconstrained `i32` unit | compatible if CC/target agree | direct projection, zero cost |
| `int32_t` | constrained `i32` unit | layout-compatible, not value-valid | validate in stub, return `Result` |
| C `int` | `i32` unit | target-dependent | resolve from target ABI; reject unknown |
| `int64_t` | `i32` unit | not identical | explicit checked narrowing |
| `float`/`double` | `f32`/`f64` unit | exact match only | no implicit precision change |
| `_Bool`, enum, bitfield | restricted unit | invalid reprs possible | validate discriminant |
| `char*` | `text` / text unit | not transparent | ownership, length, encoding adapter |
| pointer/handle | managed ref / numeric | not compatible | explicit handle/capability adapter |

Compare ABI class, register/stack passing, alignment, ownership and triple; `sizeof` equality is insufficient. Returning `Result` from the facade does not change the C ABI.

Proposed HIR facts: `ValueSemanticOrigin` (InternalTyped | CompileTimeLiteral | InternalRaw | ForeignRaw | HalValidated | BinaryProviderValidated), `SemanticUnitInfo`, `BoundaryPermit`. Compact intern IDs + SSA def-use + function return summaries; no runtime origin tags.

Boundary permission is a build-unit capability (sffi adapter, tagged hal impl, admitted binary provider, audited narrow `unsafe`) — never a file or folder name. `unsafe` never bypasses ABI mismatch, invalid representation or artifact admission.

## 4. Build-unit inventory

Each build unit declares name, kind, source roots, includes/excludes, interface, dependencies, variants, target ABI and policy role. Globs are resolved once against a frozen snapshot into a sorted, digested `source_inventory` receipt. CI requires exactly one logical owner per in-scope file. Proposed CLI: `simple build units list|show`, `simple build sources --json`, `simple robust inventory|boundaries`, `simple build doctor --source-ownership`.

Repair order before library mode: manifest parser/diagnostic -> source ownership graph -> unit interface -> isolated objects -> archive -> link. Never guess an unresolved dependency path.

## 5. Compiler / interpreter / loader migration

Logical targets: `simple-core`, `simple-compiler-core`, `simple-compiler-host`, `simple-interpreter`, `simple-loader-core`, `simple-diagnostics`, `simple-runtime`, `simple-std-<family>`, `simple-tools-*`, `simple-backend-<name>`. Keep coarse boundaries first; split further only with measured benefit.

Link/cache contract: ResolvedSourceSet + DependencyInterfaceDigests + PolicySnapshot + Target/ABI + Toolchain digests + SemanticUnitCatalog -> objects + `lib<unit>.a` + `iface.sdn` + `receipt.sdn` -> link. Prerequisites: real manifest deps, lowering against dependency interfaces, deterministic type/MCDC IDs, archive admission from current keys, generics/macros/aspects across interfaces, full object registration, Stage 3 archive reuse in Stage 4, whole-closure rollback until parity.

Interpreter uses the same policy and unit graph; raw foreign values never survive outside the adapter frame. Loader validates `iface_digest`, unit/ABI contract digest, triple, policy and capability before exposing symbols; hot swap pins in-flight sessions to old bytes.

Hardening waves: P0 SOSIX/HAL, filesystem, NVMe, byte cursors, crypto, network wire; P1 toolchain IDs/spans/LSP/SFFI gen; P2 GPU/tensor/SIMD/VHDL; P3 apps (keep `text` for user strings).

## 6. Optional cross-target and accelerator groups

`targets.sdn` stays host-only. Opt-in configs under `config/build/` (`backends_{c,vhdl,cuda,rocm,vulkan}.sdn`, `runtime_gpu.sdn`, `cpu_tiers.sdn`, `cpu_tier_artifacts.sdn`, `cross_targets.sdn`), `default: false`, never resolved by the default target set. Codegen providers are host-ABI libraries whose `targets_wire` may list foreign targets. CUDA dynamic placement only after PTX export + real provider spec. SIMD tiers dispatch on CPUID/HWCAP with baseline fallback; SVE/RVV need vector-length contracts.

Provider admission receipt: name, semver, ABI major/minor, roles, targets, toolchain identity, host + foreign triples, features, MIR ABI digest, semantic interface digest, capability policy, SHA-256, boundary contract digest, provenance. Compiler codegen and runtime GPU ABIs stay distinct. Stage 0-4 bootstrap needs no GPU/HDL SDK.

## 7. Diagnostics and ratchet

| Code | Trigger | Initial | Robust (future) |
|---|---|---|---|
| `SPL-BOUND-001` | foreign raw primitive escapes adapter | warn | error |
| `SPL-BOUND-002` | late primitive->unit cast on foreign-origin value | warn | error |
| `SPL-BOUND-003` | unit erased/modified/reasserted without validated construction | warn | error |
| `SPL-SFFI-ABI-001` | ABI class/CC/width/ownership mismatch | **error now** | error |
| `SPL-SFFI-RANGE-001` | restricted unit returned without proof or validation | **error now** | error |
| `SPL-BUILD-SRC-001` | unowned/overlapping source, manifest drift | warn (inventory) | error |
| `SPL-BUILD-ROLE-001` | unapproved boundary role / expired exception | error in release | error |
| `SPL-PROVIDER-ABI-001` | provider signature/target/receipt mismatch | error | error |

Ratchet: inventory -> new-code gate -> migration -> robust error in a ratified edition -> cleanup. No wall-clock flips; severity is a function of edition + release/as-of date + policy digest. The BOUND rules deliberately carry no `error_not_before_date` until owners ratify one.

Boundary-return autofix variants: reuse typed HAL facade; generate SFFI adapter; generate checked constrained adapter + error propagation; move late cast to the boundary and update callers; scoped exemption with reason/expiry; no fix when ambiguous. All via atomic, revision-checked multi-file `fix_transaction`, rechecked after apply, never inserting `unwrap`/panic.

## 8. Slices and order

A source inventory -> D diagnostics scaffold -> B semantic boundary HIR -> C SFFI return projection -> E compiler/interpreter/loader parity -> F true library units. G (opt-in backends) after A/D, default only after F. H (stdlib/tool remediation) progressively after B/C. Small independent PRs.

## 9. Verification matrix (proposed IDs)

RB-TEXT-01, RB-PRIM-02, RB-ORIGIN-01..03, RB-SFFI-01..04, RB-UNIT-01..02, RB-BUILD-01..04, RB-LOAD-01..02, RB-PLUGIN-01..03, RB-SIMD-01, RB-FIX-01..02, RB-DIAG-01, RB-RATCHET-01 — semantics as in the original consolidated plan (ordinary text not flagged; late casts flagged at origin; one boundary check; real C ABI fixtures for int/int32_t/bool/enum/char*; `1km/2hr` parity; orphan/duplicate source ownership errors; archive reuse; hot-swap pinning; host bootstrap without GPU SDKs; guarded SIMD dispatch; atomic fixes; same rule ID across CLI/LSP/interpreter; reproducible ratchet).

Evidence classes per host/target: compile-only, link, load provider, execute. Perf targets: cold compile <= +3% CPU / +2% RSS, warm <= +1%; zero added runtime work for unconstrained ABI-compatible SFFI returns.

## 10. Stop conditions

Unresolved target ABI, unproven constrained foreign return, unknown plugin symbol/target, unowned source, stale interface digest, nondeterministic unit symbol identity, stale autofix revisions, unqualified Stage 3 links, compiler/interpreter/loader disagreement — reported as failures, never bypassed with global `unsafe`, wildcard exceptions or silent host fallback.

## 11. Execution checklist

P0 baseline + inventory + manifest drift; P1 shared diagnostics (scaffold landed); P2 SFFI/HAL constrained returns + real C fixtures; P3 origin summaries + autofix; P4 library units; P5 optional variants; P6 library/tool hardening; P7 ratchet + release.

## References

- F# units of measure: https://fsharp.github.io/fslang-spec/units-of-measure/
- Rust type layout / `repr(transparent)`: https://doc.rust-lang.org/reference/type-layout.html
- Clang taint analysis configuration: https://clang.llvm.org/docs/analyzer/user-docs/TaintAnalysisConfiguration.html
- Bazel build concepts: https://bazel.build/concepts/build-ref
| 2026-11-15 | RB-UNIT-01/02 (unit parity spec) | `test/01_unit/compiler/units/unit_dimension_parity_spec.spl`: km/hr scale 5/18, exact 1/2, `km+kg` deny, same-storage nominal deny all GREEN; Distance/Duration -> velocity through unit_ops RED (no dimension quotient in unit_ops, bug record `unit_ops_no_dimension_quotient_velocity_2026-11-15.md`) | spec 4/5 pass, 1 expected RED |
| 2026-11-15 | RB-SFFI-ABI wiring (lane abiwire) | `sffi_abi_mismatch` lint row (SPL-SFFI-ABI-001, deny) registered in static_rules/config_and_model; triple = `SIMPLE_TARGET_TRIPLE` else host, unresolvable host with no explicit target -> no findings, unknown explicit target -> unknown-target deny; host triples incl. FreeBSD and arm linux; plain `char` unsigned on aarch64/arm/riscv linux; x86_64 gnux32 = ilp32; undeclared `@c_abi` unit flagged unless imported via `use` (imported units skip the width check). Gap: no lint target field in LintParamsV1 | specs 13/13, 8/8, 7/7 pass |
| 2026-11-15 | unitctor (bug fix) | Primitive-to-unit construction: `Name(raw)` and `raw as Name` build the same unit value as `raw_sfx` in the seed (plus `.value` field, `to_f64`/`to_i64`); pure-Simple HIR lowers `raw as Name` to the unit record `StructLit`. Bug: unit_from_primitive_construction_unsupported_runtime_2026-11-15 (verification-pending) | `test/01_unit/compiler/unit_from_primitive_construction_spec.spl` |
