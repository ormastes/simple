# Simple: Unified `unit`, Primitive-API Hardening, and Scheduled Diagnostics

**Integrated implementation plan — 2026-11-12 (user-provided; saved verbatim in substance).**
Audit baseline: `ormastes/simple` commit `fd266fb3f0023da383b7decea0edec420058ed9a`.
Status: source-audited plan, NOT a claim of implementation.

## 0. Decisions
1. Keep `unit`, deprecate `newunit` (warn, do not reject). `newtype` recognized temporarily; numeric newtype auto-derives add/sub/mul/div — migration must be review-required where behavior changes.
2. Per-rule, per-profile, edition-controlled warning -> error -> removal policy in SDN/diagnostic metadata (no new keyword syntax). Record created_on, warn_since date/version, error_not_before date, error_since version, removal date/version.
3. Repair primitive-public-API warning: current EasyFix replaces a line with the identical line (no-op). Warnings must carry exact symbol/type path and meaningful fix choices; never present a no-op as a fix.
4. One `DiagnosticV1` pipeline for parser, typechecker, driver, lint, interpreter admission/eval, LSP, CMM, native editor, VS Code. One normalized rule identity + severity decision.
5. Public API checking is semantic: walk resolved effectively-exported type graph (public fields, nested type params, aliases, enum payloads, generated methods, aspects/macros, re-exports, `__init__`). Private primitives and ABI/FFI bridges legitimate with explicit boundary policy.
6. Separate dimensions from domains (ByteCount, BitCount, ByteOffset, ByteIndex, SectorCount, Lba, Timestamp, Duration, ScreenPoint, TextureUV not interchangeable). Aggregates (Point2, Rect2) stay structs with typed components.
7. No generic arithmetic granted to every unit; ops declared explicitly.
8. Preserve compile speed: one parse, one resolved exported-signature graph, memoized traversal, O(1) rule lookup, incremental invalidation, lazy cross-file fixes, no global source string scans.

Done means: check/build/lint/interpreter admission/LSP/UI show same rule + effective severity; code actions really change code and are revision-checked; robust/critical/verified cannot bypass public-type checks; `newunit` warns while accepted; unit arithmetic matrix verified in compiler AND interpreter; representative stdlib migrated; perf budgets met.

## 1. Source audit (at baseline)
| Location | Observed | Correction |
|---|---|---|
| src/compiler/35.semantics/lint/primitive_api.spl | shallow decl-level | retire as authority; keep optional quick scanner |
| src/compiler/35.semantics/lint/semantic_api/checker.spl | recursive leaf checker, NOT wired into live lint; enum payloads outstanding | wire after type resolution; enum payloads; effective visibility |
| src/compiler/35.semantics/lint/primitive_types.spl | i8..i64,u8..u64,f32/f64,bool; not usize/text/char | classify numeric/index/text families semantically |
| src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl | single-line pub fn scan; skips extern & same-primitive math; Uncertain fix with new_text: line (NO-OP) | remove false fix; precise diagnostic; ranked real whole-symbol migrations |
| src/compiler/90.tools/fix/rules/registry.spl + .../_LintMain/lint_checks.spl | primitive rule invoked via EasyFix registry AND directly -> duplicates | single owner; dedupe by (code, symbol-id, type-path, span) |
| src/compiler/90.tools/lint/_LintMain/config_and_model.spl | primitive_api deny in some policies; Warn then apply_config_level promotes | centralize policy; validate all paths |
| src/compiler/00.common/assurance/warning_phase.spl | --assurance-warning-phase downgrades ALL rules one rung | keep; add selective rule scheduling; never silently downgrade security rules |
| src/compiler/80.driver/driver_typecheck_severity.spl, driver_safety_severity.spl | robust may be Warn, critical/verified Deny | reconcile admission vs publication; fail closed for robust public API |
| src/compiler/00.common/diagnostics/diagnostic_v1.spl | one optional fix | additively: multiple ranked fixes + lifecycle metadata; JSON compat |
| src/compiler/90.tools/fix/rules/impl_/deprecation.spl | no newunit | token-aware newunit migration; explicit review for newtype |
| src/compiler/10.frontend/core/lexer_types.spl | KwNewtype=198, KwNewunit=219 | keep tokens; parse into common UnitDecl + deprecation |
| src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl | numeric newtype auto-derives add/sub/mul/div | common lowering; never silently drop generated ops |
| src/compiler/30.types/units/unit_registry.spl | newunit_* catalog + separate unit infra | unify registration; no duplicate registries |
| src/compiler/30.types/type_infer/inference_expr_ops.spl | generic arithmetic unification | cheap unit operator gate before numeric fallback |
| src/app/interpreter/expr/arithmetic.spl | raw Value.int/float; errors not DiagnosticV1 | keep unit identity; approved operators; normalize errors |
| src/lib/nogc_sync_mut/lsp/handlers/diagnostics.spl | subprocess query check --format=json, own parsing; lint not invoked | single compiler entry, policy snapshot, precise spans, fix IDs |
| src/lib/editor/services/diagnostics.spl | lacks rich fields | preserve code/labels/notes/lifecycle/fixes/version |
| src/app/editor/editor_ctrl_diagnostics.spl | quickfix only Markdown | route SPL/SDN/SHS/CMM to LSP/compiler actions |

## 2. Library primitive audit priorities (sampled, full inventory required)
P0: net byte_cursor (`pos:u64`, `read_bytes(n:u64)`, bound `self.pos + n > len` overflow-bypassable -> validate pos<=len then n <= len-pos); STUN wire fields (i64 msg_type/length/offsets/ports/octets); crypto HKDF length:i64, sqlcipher4_page offsets; packed_span (slot/generation/offset/length/count/stride u32, slot:i64); file.spl read(size:i64)/write->i64/seek/timestamps; NVMe transfer (lba/count/nsid/sector_count/buf_phys).
P1: http_core HttpLimits (all i64, negative sentinels); process_ops (timeout_ms/grace/max_output_bytes same i64); time_ops (unix us / mono ns i64 + sentinels); window_protocol geometry (signed->u32 casts); game2d texture_atlas (pixel vs UV, zero-atlas div); graphics2d_sffi raw f64; DB types (payload stays primitive; ColumnIndex distinct); compiler/interpreter ids/offsets (SourceByteOffset vs Utf16Column).
P2: audio volume/gain; paths/text counts (Utf8ByteCount, UnicodeScalarCount, GraphemeCount, Utf16CodeUnitCount).
Scan must CLASSIFY not auto-replace: payload, quantity, abs position, rel offset, index, count, id/handle, state/tag, timestamp, duration, discriminator, FFI/wire boundary; record export status, ABI need, compat.

## 3. One keyword `unit`
```simple
unit ByteCount: u64 as Bc
unit BitCount: u64 as bc
unit ByteOffset: u64 as bo
unit ByteIndex: u64 as bi
unit SectorCount: u32 as sc
unit Lba: u64 as lba
unit DurationMs: u64 as ms
val bytes = 12_Bc
val bits = 12_bc
# bytes + bits  -> compile error
```
- Suffix case-sensitive (`_Bc` byte vs `_bc` bit); collision detection via registry.
- `unit` contextual at declaration site (`unit Name: ...`), fixed lookahead, LL(1)/GPU-friendly; no new keyword/parser.
- Canonical `UnitDecl`: underlying repr, dimension expr, nominal kind, suffix, visibility, conversions, approved arithmetic, bounds, ABI layout, origin syntax. `newunit` -> same record with legacy_origin + deprecation diagnostic.
- newtype compat may keep old generated ops; strict migration must select equivalent legal ops or warn.
- Nominal and dimensional identity coexist; no implicit coercion because both wrap u64.
- Exact integral representations for counts/offsets.

### 3.1 Arithmetic matrix
ByteCount+ByteCount -> ByteCount checked; ByteCount-ByteCount -> checked or explicit ByteDelta; ByteCount*int -> ByteCount checked; ByteCount/ByteCount -> ratio only if enabled; ByteOffset+ByteCount -> ByteOffset; ByteOffset-ByteOffset -> ByteDelta; ByteIndex<ByteIndex -> bool; ByteIndex+ByteIndex REJECT; Lba+SectorCount -> Lba via checked helper; Lba+ByteCount REJECT; Timestamp-Timestamp -> Duration; Timestamp+Timestamp REJECT; Duration+Duration -> Duration; ScreenPoint2+ScreenDelta2 -> ScreenPoint2; ScreenPoint2+ScreenPoint2 REJECT; ScreenPoint2-ScreenPoint2 -> ScreenDelta2; ScreenPoint2+WorldDelta2 REJECT; PixelPoint2->TextureUV explicit with extent; bitwise on unit REJECT unless defined.
No implicit binary arithmetic for new nominal units; only compiler-validated trait impls/attribute metadata. Interned unit IDs + result table. No proof solver in normal builds.

### 3.2 x/y/z, length/offset/index
No X/Y/Z units; distinguish coordinate space. Point vs delta vs size (sizes non-negative). Length vs offset vs index. CharCount ambiguous -> Utf8 bytes / scalars / UTF-16 units / graphemes. Grid code: RowIndex/ColumnIndex/RowCount/ColumnCount/StrideBytes/ElementCount. Units at public/module boundaries; private loops may use raw with checked conversion.

## 4. Scheduled per-rule policy
`DiagnosticRulePolicy` beside DiagnosticV1 (not a second lint framework): rule_id, created_on, warn_since_date, warn_since_lang_version, error_not_before_date, error_since_lang_version, remove_not_before_date, remove_since_lang_version, mode_overrides (advisory/moderate/strict/robust/critical/verified/CI), category, replacement, exception_policy.
Reproducibility: same edition + policy snapshot => same severity on any day; dates displayed, never flip at midnight. error_since activates only in a published release dated >= error_not_before. Pin policy digest in build metadata + cache keys. Optional reproducible `--policy-as-of` for CI rehearsal.
```sdn
diagnostic_policy:
    version: 1
    rules:
        SPL-UNIT-001:
            description: "newunit is deprecated; use unit"
            created_on: "2026-11-12"
            warn_since_date: "2026-11-12"
            warn_since_lang_version: "2026.11"
            error_not_before_date: "2027-05-01"
            error_since_lang_version: "2027.2"
            modes: {default: warn, robust: warn, critical: warn, verified: warn}
        SPL-TYPE-001:
            description: "public API exposes an unclassified primitive"
            created_on: "2026-11-12"
            warn_since_date: "2026-11-12"
            warn_since_lang_version: "2026.11"
            error_not_before_date: "2027-05-01"
            error_since_lang_version: "2027.2"
            modes: {advisory: warn, moderate: warn, strict: deny, robust: deny, critical: deny, verified: deny}
        SPL-UNIT-002:
            description: "illegal or implicit unit arithmetic"
            created_on: "2026-11-12"
            warn_since_date: "2026-11-12"
            modes: {default: deny, robust: deny, critical: deny, verified: deny}
```
(dates/editions illustrative, need owner ratification)
Resolution order: fatal parser/type corruption + security invariants > edition mandatory rules > profile baseline > rule schedule > scoped exception (if allowed) > display. warning_phase may rehearse but must not produce a release-qualified artifact violating robust gates.
Now: newunit = warning everywhere it parses; newtype separate warning code; invalid unit arithmetic = error; primitive public leakage = error for robust/critical/verified once enforcement connected. At error edition parser still recognizes legacy keywords for targeted fix; removal is a separate later edition.
Exceptions: reuse `@allow(primitive_api)` / `#![allow(...)]` but require reason, owner, expires_on/edition for critical; scope to ABI/math kernel/foreign/generated transport/migration ticket. File-wide allow without expiry incompatible with robust publication gate. Remove `_all_same_primitive` blanket exclusion; pure math gets scoped documented exemption.

## 5. Shared diagnostic structures
DiagnosticV1 additive: stable_code, severity, message, primary span, multi-file labels, notes/help/children/macro_trace, rule_created_on, warn_since, error_not_before, error_since_edition, active_profile, effective_language_edition, policy_digest, related_symbols, fix_ids[], fixes[], legacy `fix` alias (first Safe/Likely fix) during transition.
DiagnosticFix: id, title, rank, confidence Safe|Likely|Uncertain, applicability automatic|review_required|unavailable, replacements[], file_revision_preconditions[], symbol/type fingerprints, prerequisites[], incompatibilities[], impacted_callers[], postconditions[].
Route: lexer/parser/typecheck -> typed DiagnosticV1 -> per-rule policy -> dedup sink -> CLI JSON/text; LSP publishDiagnostics/codeAction; CMM/MD/editor render same fields. Interpreter admission uses same policy/codes; runtime failures become DiagnosticV1. No per-file lint subprocess when typed graph exists.
Fix rules: (1) newunit->unit token replacement, Safe only when contract/suffix/ABI/ops proven equal, else Likely with preview; (2) newtype->unit inspect derived ops/FFI, never auto-apply by name; (3) primitive->semantic type: ranked candidates, full cross-file edits, check call sites/overloads; (4) unsafe unit arithmetic: suggest checked_add/sub, explicit conversion, never unchecked cast labelled Safe; (5) apply requires exact file versions, preview, atomic or abort, re-run parse/typecheck + impacted specs. Caller counts from real reference search. No fake auto-fix — help only.

## 6. Surfaces
Frontend (unified AST, same-pass warning), HIR/MIR (interned UnitTypeId, unit dispatch before numeric fallback, post-mono exported gate), optimizer/codegen (erase after verification, unit-aware const fold), interpreter/REPL (unit tags, DiagnosticV1 errors, admission), loader/SCV (unit identity in interface, edition+fingerprint in cache), lint & check (same engine), LSP (compiler diagnostics, versioned WorkspaceEdit, deprecated tags), editor/VS Code/CMM (problem panel w/ rule+dates+profile+fix count; SPL/SDN/SHS quickfix route; invalidate stale actions), MD/SDN/SHS (same schema), build/test runners (diff-aware, policy-keyed caches, CI no expired suppression), docs (unit guide, deprecation catalog, recipes, diagnostic authoring guide).

## 7. Performance
No extra parse pass; no full-tree primitive scan; memoize (TypeId, visibility ctx); two-tier (cheap mandatory vs expensive analysis/CI); O(1) policy table; incremental interface caches; diagnostic cache separate from codegen; editor fast local + lazy cross-file fixes; interned IDs; lockless first-requester-produces caching.
Budgets (targets): cold compile <=3% CPU / <=2% mem; warm <=1%; body-only incremental <=1%; parser throughput <=1%; 3000 exported types O(V+E)/O(affected); no UI blocking; release unit arithmetic 0 extra branches/allocs vs checked raw.

## 8. Profile behavior
newunit: warn (all profiles) -> error w/ fix at error edition -> lexical removal later. newtype numeric: warn. Raw primitive public: moderate warn / strict deny / robust+ deny. Illegal unit arithmetic: deny everywhere. Private raw: allowed. Native ABI/wire field: allowed at adapter boundary with typed facade.

## 9. Work breakdown
P0: rule policy beside DiagnosticV1; fix primitive_api double invocation + no-op EasyFix + precise spans; check/driver/lint share sink+levels; wire semantic_api on exported type graph (enum payloads, aliases, re-exports, __init__, generated, post-mono); unify DiagnosticV1 adapters (compiler/interpreter/LSP) before mass lib changes.
P1: UnitDecl shared AST/HIR; unit/newunit/newtype one lowering; registry + suffix (_Bc vs _bc) unification; compat-aware op table; unit-aware typecheck/const fold/codegen/interpreter; sspecs incl. cross-module + parser throughput.
P2: security-critical libs first (byte cursor, STUN/HTTP/TLS, packed spans, alloc lengths, HKDF/SQLCipher, file offsets, NVMe) with overflow checks in same patch; then platform, geometry/media, tooling, remaining libs in small batches.
P3: multi-fix DiagnosticV1, versioned LSP code actions, editor SPL quickfix route, CMM/MD/SDN/SHS adapters, `simple fix --list/--preview/--apply-safe/--apply-reviewed`, `simple lint --inventory-public-primitives` (proposed spellings).
P4: baseline inventory + exceptions with owner/reason/expiry; robust enforcement after smoke; ratify dates before publishing; one release of warning-only CI rehearsal; removal only in separate announced edition.

## 10. Acceptance matrix
1. Public i64/u64/bool/floats/pointers/usize, nested Option<[u64]>, tuples, aliases, generics, enum payloads, exported fields, generated methods, re-exports, macros, AOP, __init__ visibility; private counterexample silent.
2. primitive_api once per offending type path with exact byte span + UTF-16 range, same code+severity on all entry points; no same-line EasyFix.
3. @allow scoped; expired/unowned exceptions diagnosed.
4. newunit parses+warns; unit no warning; newtype reports operator risk; error edition emits error with token fix; macro origin.
5. _Bc vs _bc distinct; deterministic collision errors; cross-module suffix privacy.
6. Arithmetic matrix in compiler const-fold AND interpreter; overflow can't reach unchecked codegen.
7. Domain cases: ByteOffset vs ByteCount, FileOffset, HTTP count vs length, STUN port vs length, SQLCipher page vs offset, NVMe LBA vs sectors, timestamp vs duration, signed width->u32, pixel vs UV.
8. LSP codeAction ranked, versioned multi-file, no-op filtered, stale rejected, fix-all Safe only, cancellation.
9. Profiles x warning-phase x edition x app matrix; clock-independent.
10. Perf benchmarks per section 7.
11. Full repo inventory over all sources (src/lib, src/app, src/compiler, src/os, firmware) with per-symbol classification, re-run per batch, ratchet vs baseline.

## 11. Precedent
Rust lint levels + deprecated attrs; Swift availability (introduced/deprecated/obsoleted); LSP versioned TextDocumentEdit/WorkspaceEdit. Do not introduce parallel diagnostic or unit subsystems.

## 12. Owner gates / order
Ratify: 2027-05-01 / 2027.2 escalation target; newtype non-unit role; scalar payload & public predicate exception policy; release/edition field names; bootstrap parser/ABI compat.
Order: P0 diagnostics + no-op fix -> P1 unit AST/ops -> P0 critical lib boundary fixes (after canonical type system) -> P2 libs -> P3 UI/multi-file fixes -> P4 escalation. newunit stays warning-only during migration; invalid unit arithmetic and untyped robust exported APIs remain errors.
