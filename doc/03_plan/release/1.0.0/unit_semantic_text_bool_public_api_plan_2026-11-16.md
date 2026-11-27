# Simple: Unified `unit`, Semantic `text`/`bool`, Public-API Hardening, and Scheduled Diagnostics

> **Owner directive 2026-11-16.** No primitive on a public API, **including `text`**:
> public `text` in a semantic domain is flagged (`SPL-TEXT-001`); public `bool`,
> **including `is_*` predicates, is NOT exempt** (`SPL-BOOL-001`). This
> supersedes the 2026-11-15 "bare `text` not flagged" decision. The plan below
> (owner-supplied, retained verbatim) is the spec; the 2026-11-12 lane plan
> [unit_primitive_api_lane_plan_2026-11-12.md](unit_primitive_api_lane_plan_2026-11-12.md)
> is superseded by it.
>
> **Status as of 2026-11-16 (landed on `release/1.0.0`):**
> - Seed `unit`: #9392 (suffix-less `unit Name: T` record units), #9600 (registered-record unwrap, SPL-UNIT-002 deny), #9684 (`U <cmp> scalar` deny, SPL-UNIT-001/003 `newunit`/numeric-`newtype` warnings, refreshed `bin/simple.exe`).
> - Pure-Simple: #9488 (same-unit `U*U`/`U/U` give the underlying scalar).
> - Robust/Option: #9468 (ROB-OPT-003 on public returns and `pub type` aliases; `nil_outside_unsafe` = warn in robust/critical).
> - API checker: #9484 (`__init__.spl` visibility; re-export following not done).
> - Required ratchets: #9633 + #9720 (`push-primitive-api-added`, compared at the merge base), #9649 (`push-nil-outside-unsafe-added`).
> - Domain migrations: #9446 (STUN), #9498 (packed_span), #9533 (NVMe transfer types, SQLCipher page no), #9593 (http_core), #9640 (win_text_access `Millis`), #9658 (byte buffers `Capacity`/`Length`), #9711 (access query `Count`), #9725 (compare_view `Length`/`Count`), #9743 (`nogc_take_ident` `Offset`), #9602 (nvme_ct newtypes -> `unit`).
> - `nil` -> `None` (type-resolved `-> T?` only): #9678 (css), #9733 (io).
> - **Known gap:** the seed JIT cannot lower `.value` on a unit-typed value, so any module that reads it is demoted to the interpreter. Registering the unit class for HIR removed the demotion but made the JIT miscompile unit ops (garbage, rc 139), so it was not shipped; unit ops must be lowered on the underlying scalar in HIR first. This blocks moving `types.spl` wrappers and `byte_cursor.spl` to `unit`.

---

**Integrated implementation plan — revised 2026-11-16 (Asia/Seoul)**  
**Applies to:** Simple compiler, interpreter/REPL, LSP, CMM, Simple Editor/VS Code, libraries, runtime, Simple OS/NVMe firmware, test/build runners, and language guide.  
**Status:** Source-audited engineering plan; **not** a claim that the proposed changes have been implemented.  
**Audit baseline:** `ormastes/simple` main commit `fd266fb3f0023da383b7decea0edec420058ed9a`; `release/1.0.0` remote ref `a19a0bb11d400d180cf5a94cd075d52ef247d72c` checked selectively. Sparse clone and restricted historical blob fetch mean this is a sampled implementation audit, **not** an exhaustive repository or branch verification.  
**Previous decisions preserved:** Only `unit` remains as a declaration keyword; `newunit` and relevant `newtype` usages migrate into it; no extra language keyword; robust public API primitives must be diagnosed; expensive checks are opt-in for analysis/debug/CI; use the existing shared diagnostic infrastructure.

## 0. Decisions and completion criteria

1. **Keep `unit`, deprecate `newunit`; do not reject legacy syntax yet.** Both spelling variants share one semantic lowering path in the transition. `newtype` remains recognized temporarily because its automatically derived arithmetic may differ; a review-required migration is necessary when behavior could change.
2. **Generalize warning → error → removal as a per-rule, per-profile, edition/version-controlled policy.** Record creation/announcement date, first-warning date/version, planned error date/version, and eventual removal date/version. Do not introduce keyword syntax for policy; store it in SDN/diagnostic metadata.
3. **Repair the existing primitive-public-API warning.** It currently has an ineffective `EasyFix` that replaces a source line with the identical line. A real warning must include its exact symbol/type path and meaningful fix choices. A no-op must never be presented as an auto-fix.
4. **Use one `DiagnosticV1` pipeline** for parser, typechecker, compiler driver, lint, interpreter admission/evaluation, LSP, CMM view, native editor, and VS Code. The old adapters can remain until migration is complete, but there must be one normalized rule identity and severity decision.
5. **Make public API checking semantic.** Walk the resolved, *effectively exported* type graph, including public fields, nested type parameters, aliases, enum payloads, generated methods, aspects/macros, and re-exports. Private implementation primitives and ABI/FFI bridges remain legitimate with explicit boundary policy.
6. **Separate dimensions from domains.** `ByteCount`, `BitCount`, `ByteOffset`, `ByteIndex`, `SectorCount`, `Lba`, `Timestamp`, `Duration`, `ScreenPoint`, and `TextureUV` are not interchangeable. `unit` provides zero-cost nominal/dimensional identity; aggregates such as `Point2` and `Rect2` remain structs with typed components.
7. **Do not grant generic arithmetic to every unit.** Operations are explicitly declared/derived from rules, not automatically copied from underlying `u64`/`f64`.
8. **Preserve compilation speed.** One parse, one resolved exported-signature graph, memoized type traversal, compact rule lookup, incremental invalidation, lazy cross-file fixes; use no global full-source string scan in normal compilation.
9. **Keep ordinary `text` and internal `bool` usable.** Add semantic nominal types to *specific* trust and domain boundaries; do not wrap arbitrary prose or boolean expressions everywhere. The desired policy is an eventual prohibition on *bare public Boolean API slots*, not on the Boolean primitive existing in the compiler. `unit StatusFlag: bool` may participate directly in `if`/`while` without a duplicate `@boolable` annotation; numeric truth conversion is distinct and optional.
10. **Re-use existing stdlib classes and codecs.** `Path`, `Url`, `IpAddr` with V4/V6, `ExternalText`, and `TextSessionCodec` exist in sampled sources. Extend and reconcile them rather than introducing conflicting substitutes. Keep the established `_ip` suffix and verify release-branch behavior before changing literal grammar.
11. **Treat semantic text as a trust-boundary concern.** `LogText` is the short preferred name; `UiText` is ordinary UI display prose, while HTML/SQL/command/URL-path/secret values require domain-specific validation or context encoding. `UiIn<T>` / `UiOut<T>` and `StreamIn<T>` / `StreamOut<T>` describe directional channels/capabilities, not synonyms for `text` values.

**Done means:** `simple check`, `simple build`, `simple lint`, interpreter/REPL admission, LSP diagnostics, and UI show the same rule and effective severity; code actions actually change code and are revision-checked; robust/critical/verified artifacts cannot bypass required public-type checks; `newunit` warns while it is still accepted; the unit-aware arithmetic and `text`/`bool` operator matrices are verified in both compiler and interpreter; existing IP/path/URL/text-codec modules remain authoritative; representative stdlib APIs migrate; compile performance budgets are met.

## 1. Source audit: why the warnings exist yet are not fixing the libraries

| Location at audit commit | Observed behavior | Needed correction |
|---|---|---|
| `src/compiler/35.semantics/lint/primitive_api.spl` | Shallow declaration-level inspection; cannot prove nested type closure | Retire as authority; retain optional quick/preview scanner |
| `src/compiler/35.semantics/lint/semantic_api/checker.spl` | Recursive primitive leaf checker, explicitly **NOT wired into live lint**; enum payload traversal outstanding | Wire typed graph after type resolution; connect enum payloads and effective visibility |
| `src/compiler/35.semantics/lint/primitive_types.spl` | Canonical list of `i8..i64`, `u8..u64`, `f32/f64`, `bool`; not `usize`/text/char | Classify every numeric/index/text family by semantics; avoid blanket condemnation of a valid text API |
| `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl` | Scans only selected single-line `pub fn`/`pub me`/`pub static fn`; skips `extern` and same-primitive pure math; creates `Uncertain` line replacement with `new_text: line` (a **no-op**) | Remove false fix; emit precise diagnostic; add ranked, real whole-symbol migration actions |
| `src/compiler/90.tools/fix/rules/registry.spl` and `.../_LintMain/lint_checks.spl` | Primitive rule called through general EasyFix registry **and again directly**; potential duplicate findings | Single rule owner; de-duplicate by `(code, symbol-id, type-path, span)` |
| `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` | `primitive_api` is `deny` by default in some policies; rule emission starts at Warn then may be promoted by `apply_config_level` | Keep working strict behavior; centralize policy and validate all execution paths |
| `src/compiler/00.common/assurance/warning_phase.spl` | Existing `--assurance-warning-phase` / `SIMPLE_ASSURANCE_WARNING_PHASE` downgrades **all** rules one rung | Preserve as explicit transition mode; add **selective rule scheduling**, never silently downgrade unrelated security rules |
| `src/compiler/80.driver/driver_typecheck_severity.spl` and `driver_safety_severity.spl` | Robust typecheck/safety may be Warn while critical/verified Deny; later publication rules differ | Reconcile each rule's admission and publication guarantee; fail closed for robust public API |
| `src/compiler/00.common/diagnostics/diagnostic_v1.spl` | Stable code, labeled spans, notes, children, and one optional `fix: DiagnosticFix?` | Extend additively to multiple ranked fixes and migration lifecycle metadata; preserve JSON compatibility |
| `src/compiler/90.tools/fix/rules/impl_/deprecation.spl` | Existing syntax deprecations, but not `newunit` | Add token-aware `newunit` migration and explicit review for `newtype` |
| `src/compiler/10.frontend/core/lexer_types.spl` | Separate `KwNewtype=198`, `KwNewunit=219` | Preserve token recognition in transition; parse into common `UnitDecl` and issue deprecation |
| `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` | Independent legacy declarations; **numeric `newtype` auto-derives add/sub/mul/div** | Common lowering, but never silently discard previously generated operators |
| `src/compiler/30.types/units/unit_registry.spl` | Catalog references `newunit_*`, while other `unit` dimensional infrastructure also exists | Unify registration and fixed-point unit metadata; no duplicate registries |
| `src/compiler/30.types/type_infer/inference_expr_ops.spl` | Generic arithmetic type unification; not yet a complete operation-per-unit proof | Add a cheap unit operator type gate before generic numeric fallback |
| `src/app/interpreter/expr/arithmetic.spl` | Raw `Value.int`/`Value.float` operations; diagnostic errors independent of `DiagnosticV1` | Retain unit identity in interpreter value/type metadata and dispatch approved operators; normalize errors |
| `src/lib/nogc_sync_mut/lsp/handlers/diagnostics.spl` | LSP launches `simple ... query.spl check --format=json`, with its own JSON/text parsing; lint not visibly invoked | Single compiler diagnostic entry point, policy snapshot, precise span mapping, fix IDs |
| `src/lib/editor/services/diagnostics.spl` | Editor diagnostic model lacks several rich fields | Preserve code, labels, notes, lifecycle, multiple fixes, document version |
| `src/app/editor/editor_ctrl_diagnostics.spl` | Direct quickfix controller handles Markdown; returns `no quick fixes` for other languages | Request LSP/compiler actions for SPL/SDN/SHS/CMM; preview/apply revision-checked changes |

**Conclusion:** A lint level alone cannot close the gap. The current authoritative semantic checker is unconnected, quick-fix is ineffective, and compiler/interpreter/LSP/editor paths are divergent. The status must be tested on each entry path; do not claim all builds currently enforce `deny` just because the lint config says so.

## 2. Library primitive audit and priority

This is a **confirmed source-sampling audit**, not a claim of a complete automated scan of every library file. Selected implementation modules and their public signatures were inspected at the baseline commit. A full repository-wide audit is a required implementation deliverable in section 10, with machine-generated inventory and tracked exclusions. The distinction matters: a regex grep of `pub fn` misses exports via `__init__`, generics, generated members, and structs.

| Priority | Area and observed source examples | Dangerous mix-ups / fix direction |
|---|---|---|
| P0 | **Network parsing:** `src/lib/common/net/byte_cursor.spl` uses `pos:u64`, `read_bytes(n:u64)` and `read_be(n:u64)`; bounds compare `self.pos + n > len` | Differentiate `ByteIndex`, `ByteCount`; use `n <= len - pos` after validating `pos <= len`, or checked addition, to avoid overflow bypass. Define `WireByteOffset` vs host buffer offset where needed |
| P0 | **Protocol wire fields:** `src/lib/nogc_sync_mut/net/stun.spl` has `msg_type`, `msg_length`, byte offsets, ports and IP octets expressed as `i64` | Introduce `StunMessageType`, `ByteCount`, `ByteOffset`, `UdpPort`, `Ipv4Octet`, `TransactionId`, checked wire-width conversion; prohibit mixing count with port |
| P0 | **Security and cryptography:** `src/lib/common/crypto/typed/hashes.spl` already uses `ByteSpan`/`SharedSecret` but HKDF `length:i64`; `src/lib/nogc_sync_mut/database/codec/sqlcipher4_page.spl` manipulates page number/size/IV/HMAC offsets | Use `OutputByteCount`, `SqlitePageNo`, `PageByteOffset`, `Nonce`, `KeySize`, `DigestSize`; validate max output and page boundaries; maintain constant-time behavior; never wrap secrets in formatting-friendly generic types |
| P0 | **Memory/buffer:** `src/lib/common/memory/packed_span.spl` has `object_slot`, generation, `byte_offset`, `byte_length`, `element_count`, `element_stride` as `u32`, plus `slot:i64` APIs | `SlotId`, `Generation`, `ByteOffset`, `ByteCount`, `ElementCount`, `ByteStride` plus checked span admission; keep packed FFI/C ABI layout unchanged |
| P0 | **File IO:** `src/lib/nogc_sync_mut/io/file.spl` exposes `read(size:i64)`, `write(...) -> Result<i64, ...>`, `seek`, raw metadata timestamps; internal `fd:i64` | `ByteCount` for read/write totals, `FileOffset` for seek, `UnixTimestamp`/`Duration` for time; `FileHandle` already a useful type. Keep raw fd in private host bridge |
| P0 | **OS/NVMe:** `src/os/drivers/nvme/nvme_transfer_command.spl` has `lba:u64`, `count:u32`, `nsid:u32`, `sector_count:u64`, `buf_phys:u64` | `Lba`, `SectorCount`, `NamespaceId`, `PhysicalAddress`; preserve exact packed command fields; `Lba + SectorCount` requires bounds validation, never accept `ByteCount` as `SectorCount` |
| P1 | **HTTP resources:** `src/lib/common/net/http_core.spl` `HttpLimits` has max line bytes, header count, body bytes, idle timeout seconds, requests per connection all `i64` | Distinct `ByteCount`, `HeaderCount`, `RequestCount`, `Seconds`; remove magic negative length sentinels through typed result/state |
| P1 | **Process control:** `src/lib/nogc_sync_mut/io/process_ops.spl` passes `timeout_ms`, grace period, `max_output_bytes`, and polling wait in the same `i64` type | `DurationMs`, `ByteCount`, `ProcessHandle`, `PollDeadline`, result enums; internal FFI stays primitive with explicit conversions |
| P1 | **Time:** `src/lib/nogc_sync_mut/io/time_ops.spl` returns Unix microseconds or monotonic nanoseconds as `i64`, sometimes failure sentinels | `UnixInstant`, `MonotonicInstant`, `Microseconds`, `Nanoseconds`; subtraction of two instants yields duration; absolute instants cannot be added; return typed `Result` rather than sentinel |
| P1 | **Window/UI geometry:** `src/lib/common/window_protocol/geometry.spl` uses `Point{x:i32,y:i32}`, `Size{width:u32,height:u32}`; constructors cast signed widths/heights to `u32` | `ScreenPoint2`, `ScreenSize2`, `PixelCount`, `PixelDelta2`; reject negative dimensions before cast; keep x/y together as typed aggregate; no need to separately tag every axis |
| P1 | **2D rendering:** `src/lib/nogc_sync_mut/game2d/render/texture_atlas.spl` mixes pixel positions/sizes `i64` and normalized UV coordinates `f64`; computes `uv_x=px_x/atlas_w` | `PixelPoint2`, `PixelSize2`, `UVPoint2`, `UVSize2`, `Rect2<Space>` or distinct structs; zero-atlas dimensions and checked extent; don't reuse unqualified `Rect2` across coordinate spaces |
| P1 | **Graphics FFI:** `src/lib/nogc_sync_mut/io/graphics2d_sffi.spl` exposes raw `f64` x/y/radius/angle, internal native handles as `i64` | Public adapter uses `Point2<Space>`, `Radius`, `AngleRad`, matrix and handle types; `extern` ABI leaf explicitly exempt in host-only adapter |
| P1 | **Database:** `src/lib/nogc_sync_mut/database/sql/types.spl` has `DbValue.Integer(i64)`, `DbRow.get_at(index:i64)` | Raw DB scalar **payload** can remain primitive (value is data); `ColumnIndex` is not the same as SQL parameter slot or row count. Do not blindly wrap every SQL integer |
| P2 | **Audio:** `src/lib/nogc_sync_mut/game2d/audio/sound.spl` uses `volume:f64`, looped/spatial booleans | `UnitInterval`/`AudioGain` with `0..1` or gain range contract; named playback config; keep cheap predicate bool where permitted by policy |
| P2 | **Paths and text:** `src/lib/nogc_async_mut/fs/path.spl` already supplies a path object; string codecs elsewhere use raw byte count and text length | `Path`, `DirectoryPath`, `FilePath` when useful; separate `Utf8ByteCount`, `UnicodeScalarCount`, `GraphemeCount`, `Utf16CodeUnitCount`. Generic `CharCount` is ambiguous; text content is data, not itself a unit |
| P1 | **Compiler/interpreter:** raw `i64` type tags/offsets, source byte offset vs UTF-16 LSP character offset, runtime object handles, indices and lengths | Strong IDs `NodeId`, `DeclId`, `TypeId`, `SourceByteOffset`, `Utf16Column`, `TokenIndex`, `DiagnosticId`. Keep numeric internals private for parsing speed; convert at subsystem boundaries |

**Additional mandatory scan targets:** async/sync IO, filesystem and NVFS, network/TLS/IPsec/TCP wraparound, authentication/security/audit, cryptographic widths/nonces, DB SQLCipher/WAL, decompression/allocations, image/video/audio sampling, GUI/TUI/web layout and input, 2D/3D matrices/coordinates, SIMD/GPU grid/stream/lane indices, build/test runner IDs/timeouts, SCV object IDs, scheduler resource counts, container quotas, NVMe queue/admin commands, firmware PRPs/LBAs, VM/allocator alignment, statistics and units catalog.

**The scan must classify, not auto-replace:** `integer payload`, `physical quantity`, `absolute position`, `relative offset`, `index`, `count`, `ID/handle`, `state/tag`, `timestamp`, `duration`, `enum/discriminator`, `FFI/wire boundary`. Record whether the symbol is effectively exported, whether its underlying raw type is necessary for ABI, and whether the replacement is source- and binary-compatible.

## 3. One keyword: `unit`, and no forced x/y/z keywords

**Proposed unified declaration syntax** (grammar and compiler must be updated; not yet supported everywhere):

```simple
unit ByteCount: u64 as Bc
unit BitCount: u64 as bc
unit ByteOffset: u64 as bo
unit ByteIndex: u64 as bi
unit SectorCount: u32 as sc
unit Lba: u64 as lba
unit DurationMs: u64 as ms

val bytes = 12_Bc      # bytes, exact integer count
val bits = 12_bc       # bits, exact integer count
# bytes + bits        # compile error: different units
```

- The suffix portion after `_` is case-sensitive. Convention: general suffixes lower-case; uppercase initial `B` for byte (`_Bc`), lower-case `b` for bit (`_bc`). Detect suffix collisions using the existing registry. Do **not** turn all suffixes uppercase.
- `unit` may already appear as a return/empty type. Parse declaration-site `unit Name: ...` contextually; keep a fixed lookahead and LL(1)/GPU-friendly token grammar. No second parser or new keyword.
- Implement one canonical semantic record `UnitDecl` with underlying representation, dimensional expression, nominal kind, suffix, visibility, conversion rules, approved arithmetic, bounds, ABI layout, and origin syntax. `newunit` parses into the same record with `legacy_origin=newunit` plus a deprecation diagnostic.
- `newtype` compatibility requires care: the existing parser automatically derives `__add__`, `__sub__`, `__mul__`, `__div__`, and comparisons for numeric inner types. Compatibility mode may preserve the old generated ops; migration to strict `unit` must explicitly select equivalent legal ops or warn that semantics change.
- Nominal identity and dimensional identity coexist: `ByteCount` and `FileByteCount` may have equal dimensions but be distinct by design. No implicit coercion solely because both wrap `u64`.
- Keep exact integral representations for counts and offsets; do not substitute the current floating-point measurement catalog for byte/bit indexing. Physical floating-point measurements remain supported separately.
- `type` remains for structs, enums, and ordinary aliases; `unit` is the only unit-declaration introducer. Ordinary `Point2`, `Size2`, `Vector3`, `Rect3`, `Transform`, and `CoordinateSpace` are typed structures, not new keywords.

### 3.1 Arithmetic policy (compile-time first, no runtime penalty)

| Expression | Default result or rule | Reason |
|---|---|---|
| `ByteCount + ByteCount` | `ByteCount`, checked overflow | Counts combine |
| `ByteCount - ByteCount` | Checked result, or explicitly signed `ByteDelta` | Never wrap below zero |
| `ByteCount * integer` | `ByteCount`, checked | Integer is dimensionless scale |
| `ByteCount / ByteCount` | Dimensionless ratio only when explicitly enabled | Never silently return ByteCount |
| `ByteOffset + ByteCount` | `ByteOffset`, checked bounds at use site | Position advances by an extent |
| `ByteOffset - ByteOffset` | Signed `ByteDelta` | Position subtraction produces displacement |
| `ByteIndex < ByteIndex` | Bool/predicate; same container scope checked separately | Comparable positions |
| `ByteIndex + ByteIndex` | **Rejected** | Two absolute positions do not add |
| `Lba + SectorCount` | `Lba`, only through checked helper | Sector-based addressing |
| `Lba + ByteCount` | **Rejected** | Requires explicit sector size/rounding |
| `Timestamp - Timestamp` | `Duration` | Difference between instants |
| `Timestamp + Timestamp` | **Rejected** | Adding absolute times is meaningless |
| `Duration + Duration` | `Duration` (same clock/rate basis) | Durations combine |
| `ScreenPoint2 + ScreenDelta2` | `ScreenPoint2` | Translates position |
| `ScreenPoint2 + ScreenPoint2` | **Rejected** | Absolute 2D points do not add |
| `ScreenPoint2 - ScreenPoint2` | `ScreenDelta2` | Displacement |
| `ScreenPoint2 + WorldDelta2` | **Rejected** | Coordinate spaces differ |
| `PixelPoint2 -> TextureUV` | Explicit conversion requiring image extent | Pixel and normalized coordinates differ |
| Bitwise `&/|/<<` on a unit | **Rejected unless explicitly defined** | Size/offset is not a bit mask |

Set **no implicit binary arithmetic** for new nominal units. Permit only compiler-validated trait implementations (or existing attribute metadata) that encode the table; do not add a new keyword. Dimension-aware derived operations can use existing `UnitExpression` and exact-ratio metadata. On `+/-`, infer units using a compact interned ID and result table; on `*//`, simplify dimension exponents only where the unit opted in. Bounds/overflow checks follow existing robust/analysis policies; no proof solver in normal builds.

### 3.2 x/y/z and length/offset/index

- **No separate `X`, `Y`, `Z` unit by default.** Axes have the same dimension, so a `Point2`/`Point3` structure with named fields is sufficient. Distinguish **coordinate space**, not axes: screen/window/local/world/texture/clip; provide explicit transforms.
- Distinguish **point vs vector/delta vs size**. Sizes cannot be negative. A point may have negative coordinates. A `Rect2` combines `Point2<Space>` and `Size2<Space>`; dimensions enforce positive extents where required.
- Distinguish **length vs offset vs index** even when all are bytes. Length is an extent, offset is a displacement/base-relative position, index is an element address constrained by the container. `CharCount` is insufficient: distinguish UTF-8 bytes, Unicode scalar values, UTF-16 LSP code units, and user-perceived grapheme clusters.
- In higher-risk grid/SoA/dataframe code, `RowIndex`, `ColumnIndex`, `RowCount`, `ColumnCount`, `StrideBytes`, and `ElementCount` prevent wrong-axis interchange. A generic graphics `x/y` remains structurally named.
- Restrict `unit` parameter passing at public API and module boundary; private loops can use `usize`/`u32` for performance with checked, compiler-visible conversion at boundary.

## 4. Scheduled per-rule warning → error → removal infrastructure

### 4.1 Lifecycle and deterministic gating

Add a shared, versioned **`DiagnosticRulePolicy`** record beside `DiagnosticV1`, not a second lint framework:

```text
rule_id                   stable ID, e.g. SPL-UNIT-001
created_on                yyyy-mm-dd (proposal/registration date)
warn_since_date           yyyy-mm-dd (announcement)
warn_since_lang_version   edition/version first issuing warning
error_not_before_date     yyyy-mm-dd; optional, announcement/earliest release
error_since_lang_version  first edition/version that enforces error; optional
remove_not_before_date    optional
remove_since_lang_version optional
mode_overrides            advisory/moderate/strict/robust/critical/verified/CI
category                  deprecation/safety/performance/compatibility
replacement               suggested normalized syntax/semantic action
exception_policy          permitted reason, expiry, and profile scopes
```

**Reproducibility invariant:** A source tree built twice with the *same selected language edition and rule-policy snapshot* receives the same severity on different days. Calendar dates are stored and displayed, but do not silently flip the outcome at midnight. Activate `error_since_lang_version` only in a published compiler release whose release date is at/after `error_not_before_date`. Pin the policy digest in build metadata and cache keys. An explicitly supplied, reproducible `--policy-as-of` may be supported for CI rehearsal; it must never secretly override an edition's established failure semantics.

Example SDN **proposal** (illustrative rollout targets, **not an approved release commitment**):

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

Resolution order: fatal parser/type corruption and security invariants (always fatal) > published edition's mandatory rules > explicit profile baseline > specific rule transition schedule > scoped exception/suppression (only if allowed) > display. The existing broad assurance warning-phase modifier can rehearse future policy, but **must not create a release-qualified artifact that violates robust publication gates**.

**User-required default now:** `newunit` is **warning, not error**, in legacy editions and all profiles where the spelling still parses. `newtype` gets a separate warning code and safe/unsafe migration classification. Strict unit arithmetic errors immediately for genuinely invalid combinations; primitive-public leakage is **error now** for robust/critical/verified once full enforcement is connected. Do not wait until the proposed future default-mode promotion date to fix robust correctness.

At the agreed future transition edition, the deprecation warning becomes an error; the parser **continues recognizing** legacy keywords to show targeted fixes. Only a later explicit removal edition drops compatibility tokens, with a recovery diagnostic that still names the replacement. Distinguish **error** from **lexical removal** in policy.

### 4.2 Source-visible exceptions

Reuse existing `@allow(primitive_api)` and `#![allow(...)]` syntax where possible, but require a traceable **reason**, **owner**, and **expires_on/edition** for critical compatibility exceptions. Provide a way to limit exceptions to native ABI, math kernel, foreign code, generated transport boundary, or a migration ticket. A file-wide allow with no expiry is incompatible with the robust publication gate.

Do not automatically suppress warnings just because every argument shares the same primitive; current `_all_same_primitive` exclusion masks possible public domain errors. Pure math libraries can have a scoped documented exemption, not a blanket name-based loophole. Public `text` and database scalar payloads should be classified according to semantic purpose before warning, while public identifiers, bounds, and quantities use units/nominal types.

## 5. One shared error/diagnostic/reporting implementation

### 5.1 Canonical structures

Extend existing `compiler/00.common/diagnostics/diagnostic_v1.spl` additively:

```text
DiagnosticV1:
    stable_code; severity; message; primary span; multi-file labels
    notes/help/children/macro_trace
    rule_created_on; warn_since; error_not_before; error_since_edition
    active_profile; effective_language_edition; policy_digest
    related_symbols; fix_ids[]; fixes[]; legacy_fix? compatibility alias

DiagnosticFix:
    id; title; rank; confidence: Safe|Likely|Uncertain
    applicability: automatic|review_required|unavailable
    replacements[]; file_revision_preconditions[]
    symbol/type fingerprints; prerequisites[]; incompatibilities[]
    impacted_callers[]; postconditions[]
```

Keep existing single `fix` field as a compatibility alias to the first safe/likely fix during the transition; emit both in JSON until adapters migrate. Validate stable diagnostics schema in one place (SDN, JSON, CLI, LSP, MCP/CMM, SARIF if already supported), always use actual source spans and UTF-8 byte/UTF-16 character mapping, not guessed line text.

**Execution route:** lexer/parser/typecheck → canonical typed `DiagnosticV1` → per-rule lifecycle policy → deduplicated sink → CLI JSON/text; LSP maps to `publishDiagnostics` and `codeAction`; CMM/MD UI and editor render same fields. Interpreter admission checks source/HIR with the same policy and emits the same rule code; runtime-only failures become `DiagnosticV1` with stack/state and input span. Do not launch a separate lint subprocess per edited file if the compiler already has the typed graph.

### 5.2 Diagnostic content and fixes

Example for migrated `ByteReader` (proposed):

```text
warning[SPL-TYPE-001]: public parameter `n: u64` loses byte-count meaning
  --> src/lib/common/net/byte_cursor.spl:58
  | me read_bytes(n: u64) -> Result<[u8], text>:
  |               ^^^^^ primitive quantity crosses a public boundary
  = help: use `ByteCount` and convert at the internal indexing boundary
  = note: robust/critical/verified: error; moderate: warning until edition 2027.2
  = fixes:
      (1) Migrate to ByteCount and update 11 callers   [review required]
      (2) Use generic Count<Byte> if already imported [review required]
      (3) Add scoped documented ABI exception        [review required]
```

The reported caller count must be computed from real reference search, never invented in UI. Group repeated violations by symbol; one visible warning per distinct primitive leaf/path. When no valid transformation is known, offer only **help**—not a fake auto-fix.

Auto-fix rules:

1. **`newunit` → `unit`**: token span replacement, confidence `Safe` *only when* parsed semantic contract, literal suffix registration, ABI and operator set are proven equal under the selected edition. Otherwise `Likely` with preview; preserve comments/formatting. No raw global regex.
2. **Legacy `newtype` → `unit`**: inspect auto-derived operator use, type inference, FFI layout, constructors; present side-by-side operation policy and caller changes. Do not auto-apply merely because the names look compatible.
3. **Primitive API → semantic type**: compute multiple ranked candidates from declaration semantics and nearby known `unit` catalog; include full cross-file symbol edits (definition, imports, callers, constructors, assertions, tests, serialization and ABI adapters). No type changes without checking call sites and overload resolution.
4. **Units with unsafe arithmetic**: suggest `checked_add`/`checked_sub`, explicit count↔offset conversion, or a coordinate-space transform; never insert an unchecked cast and label it Safe.
5. **Apply fix**: require exact workspace file versions/fingerprints; preview the diff; apply edits atomically or abort all on stale state; run parser/typecheck and applicable test/sspec subset. Support `Fix all Safe` and separate reviewed changes. No silent file writes from diagnostic publication.

## 6. Integration by runtime/tool surface

| Consumer | Implementation contract |
|---|---|
| Compiler frontend | Parse legacy `newunit`/`newtype` into unified AST; record legacy span; attach warning in same pass. `unit` identifier context remains LL(1)/GPU-parsable. |
| HIR/type inference/MIR | Canonical, interned `UnitTypeId`; unit-aware operation dispatch before numeric fallback; exact conversions; zero-cost ABI layout; cross-module type fingerprint; post-monomorphization exported-type gate. |
| Optimizer/codegen | Units erase to underlying machine layout only *after* verification. Constant folding uses unit-aware, overflow-correct operations. Preserve source type/diagnostic provenance for debug. |
| Interpreter/REPL | Retain unit tags and approved operators; normalize `InterpreterError` into `DiagnosticV1`; run compatible edition/policy admission before executing code; runtime/native FFI checks only at legitimate boundary. |
| Loader/plugins/SCV cache | Publish unit identity/ABI metadata with module interface; reject incompatible dynamic replacement; include edition and semantic type fingerprint in interface cache. Diagnostic-only changes do not force codegen recompile. |
| `simple lint` and `simple check` | Same rule engine and severity result. `lint` can add style/performance findings but cannot be sole enforcer of mandatory language/API rules. |
| LSP | Reuse compiler diagnostics and exact ranges; provide `textDocument/codeAction`, versioned `WorkspaceEdit.documentChanges`, related information, and diagnostic tags for deprecated syntax. |
| Simple Editor / VS Code / CMM | Problem panel shows rule, created/target dates, effective profile, location, severity and fix count; compare fixes, preview multi-file edits, apply and recheck. `Ctrl quickfix` routes SPL/SDN/SHS to the same service, not Markdown-only branch. |
| MD/SDN/SHS | Same diagnostic schema and UI; policy scheduling applies to their deprecated syntax/features too, with language-specific rule IDs. |
| Build/test runners | Diff-aware testing; rule policy and type graph cache keyed immutably; strict release gates; CI checks no expired suppression and no unresolved robust violations. |
| Documentation | Language guide for `unit` grammar and arithmetic; deprecation catalog with schedules; recipe per library domain; compiler/interpreter/LSP diagnostic authoring guide and auto-fix contract. |

**CMM editor detail:** show a compact diagnostic under the code rectangle with code+message+fix count; expanded view provides expected error edition/date, ranked actions, related call sites, and one-click safe fix preview. CMM, LSP and console must not derive independent text from rules. **UI has to respect asynchronous revision changes:** if the buffer changed after a fix was offered, invalidate/recalculate the action.

## 7. Compile performance and memory constraints

### 7.1 Architecture

- **No extra parser pass:** generate `LegacySyntaxObserved` and `UnitDecl` directly during existing parse. Emit the `newunit` warning from token span; no full-text re-scan.
- **No full-tree primitive scan on every build:** walk type graphs of *effectively exported* symbols after type resolution. Memoize `(TypeId, normalized visibility context)` in a flat arena or small hash/bitset and traverse each referenced type node once. Include nested generics, aliases and generated items without building a second AST.
- **Two-tier analysis:** (A) cheap mandatory nominal/unit/public-boundary validation normal/release; (B) expensive interprocedural provenance, unit flow, multi-file candidate ranking, overflow-proof obligations for analysis/debug/CI. No SMT/formal solver or whole-program path analysis in normal compilation.
- **Policy lookup constant time:** parse SDN/language-edition schedule once per compilation session into a dense rule-ID table; severity decision O(1) per emitted diagnostic. No date parsing per AST node.
- **Incremental interface caches:** immutable `UnitTypeId`, canonical unit-expression/dimensional hash, public-surface closure hash, visibility/`__init__`-export epoch, rule-set/edition digest. Recompute exported closure only if a source edit can alter an exported declaration, its type dependencies, generated API, or visibility. Body-only edits reuse interface results.
- **Separate diagnostic cache from codegen:** severity/policy/language-edition changes invalidate diagnostic results and admission gate; only semantic changes that affect type layout/operations invalidate HIR/MIR/object files. Allow `simple lint` to reuse `check`'s typed cache; sharing with test/build runners must not create mutable contention.
- **Editor incremental mode:** fast parse syntax + cached typed interfaces on each change, publish local warning quickly; cross-file fix candidate computation only when user opens code actions. Cancel stale requests and precondition all edits on buffer versions.
- **Compact representations:** intern unit and suffix strings, use fixed-size numeric IDs in HIR/MIR, share arena pointers; no per-expression heavyweight wrapper. In codegen, erase `unit` tags to raw registers after compile-time verification.
- **Concurrency:** first cache requester produces, others await (reuse Simple SCV/cache AsyncRef policy); avoid global locks, use immutable result publication; cache keys include target ABI/grammar/edition when semantics differ.

### 7.2 Benchmark acceptance (targets, not measurements)

| Operation | Proposed budget | Measurement |
|---|---:|---|
| Normal cold compile with unit/public API validation | <= 3% CPU wall-time overhead, <= 2% peak memory vs same build with checks disabled | 30 repeated builds, median/p95, source sizes tiny/medium/large |
| Warm, unchanged build | <= 1% wall-time overhead | Shared cache valid; no redundant exported-closure walk |
| Body-only incremental rebuild | <= 1% wall-time overhead | No public interface invalidation |
| Parser token throughput (GPU and CPU) | No regression beyond measurement noise / <= 1% target | Lexer/parser microbench, malformed source included |
| 3,000 exported type graphs in one module cache | O(V+E) initial, O(affected subgraph) incremental | Instrument node visits, allocations and cache hits |
| Diagnostic UI typing feedback | No blocking on cross-file suggestion search | Async UI responsiveness; stale-code-action cancellation |
| Release-mode unit arithmetic runtime | 0 additional branches/allocations over equivalent checked raw operations | MIR/assembly diff, throughput/latency baseline |

Treat the percentages as explicit engineering objectives, not facts about current Simple performance. If budgets fail, profile allocations, exports, type walks and warning formatting through XRay/SCV build runner, then optimize before enabling default enforcement. Do not relax required robust safety merely to hit a throughput number; instead reduce checking duplication/cost.

## 8. Migration profile behavior and diagnostics examples

| Rule | Compatibility / moderate (now) | Strict | Robust / critical / verified | After scheduled breaking edition |
|---|---|---|---|---|
| Legacy `newunit` syntax | **Warn**, parse, offer fix | Warn, parse | Warn, parse; semantics still checked | Error with fix; lexical removal only in later explicit edition |
| Legacy numeric `newtype` headed for `unit` | Warn; auto-op compatibility retained | Warn | Warn; check operator semantic correctness | Error when announced and safe migration available |
| Raw numeric primitive on effectively public semantic API | Warn with meaning-aware fixes | Deny where existing policy sets it | **Deny** at compile/admission/publication | Deny by default when scheduled; explicit ABI exemption possible |
| Raw public `bool` parameter, return, field, or exported nested payload | **Warn now**, even for named predicates (no silent exemption); first determine semantic enum vs nominal bool wrapper | Deny where strict public-API policy applies | **Deny** at compile/admission/publication | **Deny in all profiles** at ratified edition; private/internal bool remains legal |
| Plain public `text` (ordinary message/title/content) | Allowed; classify meaning and trust boundary | Allowed if ordinary prose | Allowed if ordinary prose | Allowed; no blanket raw-text prohibition |
| Plain public `text` where a semantic domain or trusted sink is required | Warn with concrete typed-boundary fix | Deny for high-risk sink | Deny for high-risk sink | Promote per-domain rule/version; genuine safe prose unaffected |
| Illegal unit arithmetic / implicit unit cast | Deny once units are typed | Deny | Deny | Deny |
| Internal raw primitive and private hot loop | Allowed | Allowed | Allowed if not leaked or unsafe use | Allowed |
| Explicit native ABI/wire field | Allowed at adapter boundary; typed public facade | Allowed with policy | Allowed with approved, narrow boundary | Allowed with same guard |

The migration warning state is **not** equivalent to silently publishing untyped robust libraries. A robust build can accept old `newunit` *spelling* with a warning, yet must still reject any *semantic* primitive API exposure or illegal operations.

## 9. Work breakdown, dependencies and source targets

### P0 — repair diagnostics and prevent misleading fixes

- Establish immutable diagnostic policy rules alongside `DiagnosticV1`; pin edition/version and dates; test `warning_phase` compatibility.
- Fix `primitive_api` double invocation; remove no-op `EasyFix` replacement; retain precise warning source span, not line-1 fallback.
- Make `simple check`, compiler driver and `simple lint` share the rule sink and resolved levels. Run smoke tests to locate currently missing warnings.
- Wire recursive `semantic_api` and exported type graph, including enum payloads, aliases, public attrs, re-exports, `__init__`, generated macros/aspects and post-mono surfaces.
- Unify `DiagnosticV1` output adapters for compiler/interpreter and LSP before modifying many libraries.

### P1 — unify unit declarations and arithmetic

- Introduce `UnitDecl` as shared AST/HIR metadata; parse `unit`, `newunit`, `newtype` through one lowering path. Legacy syntax emits scheduled deprecation warning, not parser error.
- Migrate `newunit` registry and literal suffix registration; explicitly handle `_Bc` vs `_bc`, conflict checking, negative values, exact count conversion, mixed-endian wire encoding.
- Replace numeric `newtype` implicit-operator generation with compatibility-aware approved operation table for new `unit`; document code changes when behavior is different.
- Add unit-aware binary/unary expression type checking, constant folding, codegen lowering and interpreter arithmetic; preserve FFI ABI.
- Add unit-operator sspecs, cross-module import/visibility, LL(1)/GPU parser throughput tests.

### P2 — standard library migration and safety hardening

1. **Security-critical first:** net byte cursor, STUN/HTTP/TLS buffers, packed spans, allocation lengths, crypto HKDF/SQLCipher page geometry, file offsets, NVMe LBA/sector operations. Add arithmetic overflow checks in the same patch; types alone do not eliminate overflow.
2. **Platform surfaces:** process timeout/resource quotas, clock instants, file metadata, path wrappers, async FS and NVFS; keep FFI primitives private.
3. **Geometry/media:** window `Point/Size/Rect`, game2d atlas pixel vs UV, 3D world/local transformations, audio volume/duration/samples and graphics adapter.
4. **Developer tooling:** compiler HIR token/byte/UTF-16 offsets, LSP ranges, interpreter values, test/build runner graph IDs, cache resource labels.
5. **Remaining libs:** generated inventory sorted by risk and public dependency count, small batch migrations with SSPEC contract and caller tests. Do not do a monolithic blind rewrite.

### P3 — UI and multi-fix migration

- Extend `DiagnosticV1` with multiple actions and lifecycle fields; versioned code-action LSP transport; editor SPL quickfix route; CMM/MD/SDN/SHS diagnostic adapters.
- Add `simple fix --list --rule SPL-TYPE-001`, `--preview`, `--apply-safe`, `--apply-reviewed` and `simple lint --inventory-public-primitives` (CLI spellings are proposals). Support dry-run before changes; never auto-write on `check`.
- Build risk-ranked related-callers graph; render fix side-by-side; reject stale revision; rerun impacted tests.

### P4 — staged enforcement, release and deprecation removal

- Freeze initial inventory baseline and explicit accepted exceptions with owners/reasons/expiry. CI reports count by domain, warning age, edit count, and unresolved after-scheduled-version status.
- Enable robust/public mandatory enforcement after integration smoke tests, then moderate warning by default; publish accurate language guide and migration recipes.
- Ratify `error_not_before_date` and `error_since_lang_version` **before** publishing them as promises; run warning-only CI rehearsal for at least one release cycle.
- At error edition, keep compatibility parser path to produce actionable diagnostics. Remove old keyword recognition only after a separate, announced removal edition and migration tests.

## 10. Acceptance/SSPEC and regression matrix

**Coverage tests** (all must pass for compiler + interpreter + LSP adapter):

1. Public `i64`, `u64`, `bool`, floats, pointers, `usize` (if supported), nested `Option<[u64]>`, tuples, type aliases, generics, enum payloads, exported field, inherited/generated method, re-export, macro expansion, AOP and `__init__` effective visibility; private counterexample does not report.
2. `primitive_api` appears **once** per offending type path with exact byte span, UTF-16 LSP range, same diagnostic code and resolved severity in all client entry points; no same-line `EasyFix` replacement accepted as an action.
3. `@allow` applies only within approved exception scope; expired or unowned exception is diagnosed; no arbitrary allow of robust/critical/verified release invariant.
4. `newunit` parses and warns under legacy edition, `unit` parses without warning, `newtype` reports behavior-changing operator risk, later edition emits error with token-range fix; macro-origin correctly points to expansion and definition.
5. `_Bc` and `_bc` resolve to distinct exact integer types; suffix collision errors are deterministic; `_bc` cannot be passed as ByteCount; cross-module literal import privacy honored.
6. Every expression in section 3 arithmetic matrix passes/fails as specified in compiler constant folding and interpreter; invalid length subtraction and checked-overflow cannot reach unchecked codegen.
7. Files: `ByteOffset` vs `ByteCount` and `FileOffset` vs `ByteOffset`; HTTP count vs byte length; STUN port vs length; SQLCipher page vs byte offsets; NVMe LBA vs sector count; timestamp vs duration; window signed width cannot silently cast to `u32`; pixel vs UV coordinates require explicit conversion.
8. LSP `codeAction` returns ranked alternatives, exact versioned multi-file changes, no-op actions filtered, stale edit rejected with recalculation, fix-all Safe only, cancellation and document revision test.
9. CI tests profiles `{advisory, moderate, strict, robust, critical, verified}` × warning-phase `{off,on}` × edition `{pre-warning, warning, error, remove}` × app `{compiler, lint, interpreter, LSP}`; identical policy snapshot yields identical results independent of actual clock.
10. Run normal/release/debug/analysis profiles, CPU/GPU parser benchmarks, warm SCV cache, 3,000 symbol concurrent cache stress, incremental changes in body vs public signature vs `__init__` export. Enforce section 7 budgets with measured baselines.
11. Full repo primitive inventory is generated from **all source files** across `src/lib`, `src/app`, `src/compiler`, `src/os`, firmware and their exports, not just the sampled files in this report. Output per-file symbol → type path → domain classification → diagnostic → fix confidence → caller count → owner → migration state. Re-run inventory after each migration batch; compare against baseline to prevent regressions.

## 11. Reference research and design precedent

- Rust has centrally configurable lint severity (`allow`, `warn`, `deny`, `forbid`) and deprecated-item metadata; it demonstrates separation of the *diagnostic rule* from *enforcement level*: <https://doc.rust-lang.org/rustc/lints/levels.html> and <https://doc.rust-lang.org/reference/attributes/diagnostics.html>.
- Swift's availability annotations distinguish first availability, deprecation and obsoletion by language/platform version: <https://docs.swift.org/swift-book/ReferenceManual/Attributes.html>.
- The Language Server Protocol supports versioned `TextDocumentEdit` and cross-file `WorkspaceEdit`, essential for safe public API migration: <https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.17/types/workspaceEdit.md>.
- Simple-specific decisions are reconciled with the existing earlier extreme typing/traceability, diagnostic unification (compiler + interpreter + LSP + CMM + MD), unit/effects/robust mode, HIR/MIR cache and SSPEC plans. This document is the consolidated implementation checklist for this change; do not introduce parallel diagnostic or unit subsystems.

## 12. Unresolved gates and final recommended order

**Decisions needing release-owner ratification:** the `2027-05-01` / `2027.2` example escalation target; whether `newtype` retains additional non-unit role for compatibility; authoritative semantic exception policy for scalar payloads and public predicates; exact compiler release/edition field names; required bootstrap parser/ABI compat strategy.

**Implementation order:** P0 diagnostics and no-op fix → P1 `unit` AST/operator semantics → P0 critical library boundary fixes (in parallel only after the canonical type system lands) → P2 broad library migration → P3 UI/multi-file fixes → P4 release/edition escalation. The old `newunit` spelling must remain warning-only during the migration period, while actual invalid unit arithmetic and untyped robust exported APIs remain errors.

**Honesty checkpoint:** This report audited concrete source implementations, but the full-repository sweep, code modifications, compiler/test runs, fix correctness, and performance measurements are **implementation tasks**, not completed results at the time of writing.

---

## 13. 2026-11-16 focused source audit: `text`, `bool`, trust and direction

### 13.1 Scope and evidence level

This update inspected actual source in a **sparse local checkout** of `ormastes/simple` at the baseline commit, and checked a small number of blobs against the `release/1.0.0` ref. The local checkout contained **346 files under `src/lib`**. A line-oriented scan within that limited subset found **244 source lines** matching a public function form containing `text`, and **94 lines** matching a public function form containing `bool`. These are *matching source lines*, not unique APIs, not type-checked exports, and **not repository-wide totals**. Further source enumeration was blocked by missing blobs in the sparse checkout; exact branch-wide claims require the implementation inventory in §21. This report's source table establishes concrete targets and hypotheses, not that every endpoint was tested.

The existing primitive lint's canonical scalar set is `i8/i16/i32/i64`, `u8/u16/u32/u64`, `f32/f64`, and `bool` (`src/compiler/35.semantics/lint/primitive_types.spl`); it does **not** classify `text`, `usize` or `char`. Therefore **the fact that public primitive warnings exist does not imply public `text` is checked**. Conversely, placing `text` on an indiscriminate primitive blacklist would create mostly noise. Introduce a *separate semantic-text boundary classifier*.

| Source audited | Observed public or significant values | Concrete disposition, not blanket replacement | Priority |
|---|---|---|---|
| `src/compiler/10.frontend/core/types.spl`; `.../type_inference.spl`; `src/app/interpreter/expr/arithmetic.spl` | Built-in `TYPE_TEXT` and `TYPE_BOOL`; string `+` in interpreter; source type inference returns `TYPE_TEXT` for **all four** `+`, `-`, `*`, `/` when both operands are text | Keep core primitive representation; check and fix operator mismatch; nominal `unit` identity must survive inference, interpreter and serialization | P0 |
| `src/compiler/30.types/custom_primitive_info.spl` | `is_valid_underlying` accepts numeric and `bool`, but not `text`; C and LLVM primitive mappings differ from some older type-tag paths | Add representation-aware `unit Name: text`; test ownership/ABI/LLVM/C backend mappings and avoid implied zero-copy until proven | P0 |
| `src/lib/nogc_async_mut/fs/path.spl` | **Existing `Path` class** wraps `path:text`; existing `_path` literal documentation; public `Path.join(other:text)` and `to_string()` | Make existing `Path` canonical; typed `join(PathComponent)` when possible, preserve `from(text)` checked boundary, isolate `to_string` serialization | P0 |
| `src/lib/nogc_sync_mut/path.spl` | Public `basename`, `dirname`, `extension`, `stem`, `join2`, `normalize`, `resolve`, `relative_to` with raw `text` | Keep low-level helpers internal/compat; primary facade is typed `Path`; compare path normalization with traversal and root confinement | P0 |
| `src/lib/nogc_sync_mut/io/external_text_io.spl` | **Existing** `ExternalText`, `ExternalFormat`, decoding/encoding and `TextIoError`; documented byte transport with single codec owner | Keep existing codec; do not introduce new string encoding conversions in nominal wrappers; preserve explicit `Result` on malformed bytes | P0 |
| `src/lib/nogc_sync_mut/io/text_session.spl`; file/UDP/TCP/process sessions | **Existing** read/write encoding, byte order, BOM and byte limit types; raw `i64` byte limits, `text` endpoints; UDP `recv_text` may mix payload and address text | Retain codec for data; introduce `ByteCount`, `SocketAddr`, `Duration`, typed source/destination capability; verify actual network transport family | P0 |
| `src/lib/common/net/addr.spl`; `.../routing.spl` | **Existing** `Ipv4Addr`, `Ipv6Addr`, `IpAddr.V4/V6`; route `prefix_len:u8` | Keep `_ip` and family-tagged IP; ensure 32/128-bit prefix-width bounds, IPv6 8×16-bit segment parsing and serialization | P0 |
| `src/lib/nogc_sync_mut/net/http.spl`; browser-engine `.../net/entity/url_types.spl` | Two independently represented `Url` classes/parsers; HTTP `get/post/...` accept raw URL `text` and response headers are `{text:text}` | Reconcile constructors/policies before changing public methods; use typed URL, header name/value and query builder; leave body prose as `text` | P0 |
| `src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl`; `.../net/cookie_store.spl` | Certificate hostname verification passes `text`; cookies combine names/values with `=` and enforce UTF-8 byte limits | `HostName` (IDNA/punycode policy), validated cookie name/value and `SetCookieHeader`; retain bytes-based bounds and contextual escaping | P0 |
| `src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl` | `NativeToolPinV1` exposes `role`, `path`, `digest` as `text`; runtime checks 64-char digest and absolute path; public validation predicates return `bool` | Prefer `ToolRole`, existing `Path`/`NativePath`, binary `Sha256Digest` and checked hex parser; bool predicates become domain-specific result or nominal flag | P0 |
| `src/lib/common/security/types.spl`; `.../audit_log.spl` | `SecuritySeverity` and `SecurityEvent` are **already enums**; event free-form fields `text`; `AuditConfig` has raw bool switches; logger strips CR/LF/tab in helper | Preserve structured audit events; add `LogText` only for safe formatted field/sink, keep event descriptions plain until boundary; redaction and control-character policy | P0 |
| `src/lib/editor/services/diagnostics.spl` | `EditorDiagnostic` fields `path`, `severity`, `message`, `source` all `text`; code-action `kind`, `edit_json`, `command` also `text`; handwritten JSON parsing | Use typed `Path`/URI, `DiagnosticSeverity`/source/kind enums, structured `WorkspaceEdit`; **message remains ordinary text**; do not break JSON compatibility | P1 |
| `src/lib/nogc_sync_mut/game2d/backend/trait.spl` | `WindowConfig.title:text`, `fullscreen:bool`, `vsync:bool`; `Event.kind:text` comments enumerate `quit/key/mouse/none`; `key_down:bool` | `title` may stay `UiText` or `text`; change `Event.kind` to enum with typed payload; fullscreen/vsync options get domain enums or bool-backed `unit` | P1 |
| `src/lib/nogc_sync_mut/game2d/audio/sound.spl` | `clip_path:text`, `bus_name:text`, `volume:f64`, `looped:bool`, `spatial:bool` | Existing Path, typed `AudioBusId`, `AudioGain` bounds, `LoopMode` and `SpatialMode`; no need to wrap display names | P1 |
| `src/lib/nogc_sync_mut/net/http.spl` | `HttpResponse.is_success/is_redirect/... -> bool`; `HttpClient.follow_redirects:bool`; `UrlBuilder` yields `text` | Keep internal boolean computations; public mode is enum, status is typed; nominal two-state result only where useful, not an invented enum for every local `if` | P1 |

Other focused inventory gates: CMM and LSP text source snippets, MD/SDN/SHS parsers, ANSI/TUI/terminal escape sinks, SQL and SQLCipher query construction, database parameter binding, child-process shell arguments, HTML/CSS/JS/DOM sinks, input method/editor buffers, secret material, HTTP header/cookie/request serialization, path join and zip extraction, network IP/host/port parsing, external encoding, metrics/logging, GPU shader source, firmware command fields and error messages, CLI stdout/stderr, `__init__` re-exported aliases and AOP-generated API members.

### 13.2 Classification matrix: where `text` **must** remain unrestricted

| Value kind | Preferred public representation | Why | Example |
|---|---|---|---|
| Ordinary prose, localized title, diagnostic explanation | `text` by default; `UiText` where a sink/capability contract adds real value | Text is genuine user data; wrapping every argument creates meaningless casts and compile cost | `WindowConfig.title`, `DiagnosticV1.message` |
| Transcoding-boundary bytes | `ExternalText` + `ExternalFormat` **already exist**; after decode `text` | Encoding correctness, malformed byte handling, byte limit | File/net/process text session |
| File/directory/relative path | Existing `Path`, and stronger `SafeRelativePath` or `CanonicalPath` only when security distinction matters | Prevent path traversal and accidental host-path/URL conflation | File open, asset load, sandboxed unzip |
| URL/host/IP/socket | Existing `Url`, `HostName`, existing `IpAddr`, `SocketAddr` | Different grammar, canonical form, address family, authority | HTTP request, TLS verification, UDP send |
| SQL source and bound arguments | `SqlQuery`/parameter builder plus typed bind parameters | Prevent string-built executable SQL | DB `execute` |
| HTML/attribute/JS/CSS/URL output context | Context-specific `SafeHtml`, `HtmlAttrText`, `JsStringText`, `CssValueText`, `UrlComponent` or templating sink | Escaping in one context is **not** sufficient in another | DOM insertion and browser rendering |
| Logging payload | `LogText` for fields being rendered, `LogEvent` for structured event; secrets typed separately | Log-forging resistance and redaction | Audit, app/compiler/runtime logs |
| Diagnostic/UI/code-action protocol | Structured diagnostic/edit values; human-readable `message:text` | A diagnostic *message* is prose, but severity, path, edits and source kinds are not | Editor and CMM |
| Unsafe/raw bridge to C/OS/FFI | `text`, pointer or bytes as required by ABI **inside boundary only** | Avoid runtime ABI change; typed facade does conversions once | `rt_file_append_text` |

**`LogText` recommendation:** short, clear and domain-correct. `LogMessage` is unnecessary. Keep `LogEvent` separate; a `LogText` does not itself carry severity, event ID, trace ID, source span or structured attributes. `LogText` is *not* automatically safe for HTML, terminal control codes or a different structured logging wire format.

**Important security correction:** the audited `_sanitize_log_field` removes CR/LF/tab from the current audit formatter, which helps against log forging, but that does **not** prove all log sources, control bytes, terminal escape sequences, secret redaction or truncation are safe. Treat each output sink as a distinct validation/encoding policy and test it.

### 13.3 `text` length and indexing are not interchangeable

Keep a single Unicode-bearing `text` core with explicit, separately typed APIs for `Utf8ByteCount`, `UnicodeScalarCount`, `GraphemeCount`, `Utf16CodeUnitCount`, `SourceByteOffset`, `GraphemeIndex` and `LspUtf16Column`. A UTF-8 byte index must **never** be accepted as a UTF-16 LSP coordinate or a user-perceived grapheme offset without checked conversion. Cursor movement and selected-text UI operate on grapheme clusters where appropriate; source scanners and wire framing often require bytes. Do not eagerly materialize three index maps for each string; build line-index/byte-to-UTF16 maps lazily per document revision. See Unicode UAX #29 in §22.

## 14. One `unit` semantic model for numeric, Boolean and textual domains

`unit` remains the **only declaration keyword** for these nominal representations. `newunit` and legacy relevant `newtype` lower through the same compatibility pathway with scheduled deprecation. No `newbool`, `newtext`, `strongtext`, `@boolable` keyword or per-axis grammar is needed.

```simple
# DESIGN SYNTAX: implementation required; not current-code proof.
unit LogText: text                     # text-backed nominal type, sink-specific validation
unit UiText: text                      # ordinary UI display text with domain identity
unit HostName: text                    # validated DNS/IDNA hostname, not an IP string
unit SafeHtml: text                    # only construct from trusted contextual HTML builder
unit SqlQuery: text                    # only construct from parameterized query builder
unit SecretText: text                  # prohibit logging, formatting and auto-debug-print

unit VsyncEnabled: bool                # zero-cost two-state semantic flag
unit IsWritable: bool                  # zero-cost filesystem capability result
unit FullscreenMode: bool              # if exactly two modes, otherwise use enum
unit ByteCount: u64 as Bc              # dimensional arithmetic as in §3

enum RedirectPolicy:
    Follow
    DoNotFollow
    SameOriginOnly

val request_policy = RedirectPolicy.SameOriginOnly
val flag: VsyncEnabled = ...           # validated/explicitly constructed
if flag:                              # contextual bool conversion from bool-backed unit only
    enable_vsync()
```

**Three complementary mechanisms, not three keywords:**

1. **Primitive representation:** `bool`, numeric scalar and `text` remain compiler/runtime built-ins; private loops, comparisons, parsers, representation code and ordinary prose use them normally. `text` is not forbidden for public descriptive fields.
2. **Nominal semantic identity:** `unit Name: bool|text|number` creates a named, zero-cost *logical* type, not implicit subtype equivalence. `unit LogText: text` **cannot be considered zero-allocation without backend ownership and refcount proof**; the intended implementation passes/moves the same text handle and preserves its lifetime.
3. **Validation/capability:** a named type is only as safe as its constructor. Restrict construction of `SafeHtml`, `SqlQuery`, `HostName`, `SafeRelativePath`, `SecretText`; a public unchecked `.from(text)` would nullify the benefit. Accept untrusted `text` and produce `Result<DomainType, DomainError>` or a trusted builder. Do not pretend every semantic type is a mere re-tag.

There is no requirement to give each Boolean a distinct wrapper: use a **domain enum** if the flag can gain a third value or controls multiple mutually exclusive modes, and a `bool`-backed unit where an intrinsically binary relation with a stable name is appropriate. Generic `Predicate<Tag>` can reduce boilerplate only if already supportable without expanding the parser and if diagnostics remain comprehensible; do not introduce it solely to silence lint.

### 14.1 Frontend, HIR/MIR, interpreter and FFI details

- Extend the `CustomPrimitiveInfo` representation classifier beyond numeric/bool to the existing `TYPE_TEXT`; keep `TYPE_TEXT` and `TYPE_BOOL` internal tags and their efficient operations. In the HIR, carry `NominalTypeId`, underlying representation, construction proof/trust state and permitted operators; do **not** erase nominal identity during inference or constant folding.
- The interpreter must represent `unit` values with attached **runtime type identity** or a proven sealed/compile-checked origin; otherwise `LogText` and ordinary text, or `VsyncEnabled` and bare bool, become indistinguishable and wrong calls may pass. Runtime payload can still be the same primitive storage.
- Audit compiled backends separately: the legacy `type_tag_to_c(TYPE_TEXT)` maps to `const char*` and `TYPE_BOOL` maps to `int`, while the custom-primitive metadata can map bool to C `bool` / LLVM `i1`. A representation-dependent ABI bridge must be explicit and regression-tested across LLVM, C/SFFI, MinGW/MSVC, wasm and GPU paths. **Do not assert existing ABI equality** merely because a wrapper is nominal.
- `unit LogText: text` must preserve the current `text` ownership, allocator, GC/nogc semantics, UTF-8 validity contract, move/clone behavior and scope crossing, including async text sessions. No implicit extra copy, hidden normalization or refcount leak is acceptable.
- `unit Name: text` and `unit Name: bool` are recognized by parsing a type name after `unit`; the parser sees no new token class. The GPU lexer only identifies `unit`, colon and identifiers; semantic resolution determines representation and legality. Literal suffix parsing remains the numeric/IP domain's separate existing mechanism, not imposed on all text types.

## 15. Boolean behavior: conditions, comparison, public APIs and `@boolable`

### 15.1 Rule: keep `bool` as representation, reject untyped public semantics

| Situation | Final behavior | Reason |
|---|---|---|
| `if comparison`, `while !done`, `&&`, `||`, `not` with built-in `bool` | **Allow** | Comparisons and control flow fundamentally produce booleans; banning these would complicate compiler internals and syntax |
| `if flag` / `while flag` where `flag: VsyncEnabled` and `unit VsyncEnabled: bool` | **Allow, no annotation** | Underlying Boolean representation supplies a safe contextual condition; nominal identity is retained outside condition |
| Passing `VsyncEnabled` to a parameter requiring plain `bool`, or converting between two unrelated bool-backed units | **Reject implicit conversion** | Contextual truth in `if` is narrower than universal loss of semantic identity |
| `if n` where `n: i64` or `unit ByteCount: u64` | **Reject by default** | Zero/nonzero conflates count, status, sentinel, invalid and success semantics |
| `if n` with future optional numeric `@boolable` contract | **Opt-in only**, define explicit 0/nonzero meaning and validate bounds | `@boolable` is only potentially useful for numeric truth conversion; **not** for bool-backed types |
| `if text`, `if LogText`, `if IpAddr`, `if Result`, `if Option` | **Reject**; require explicit `.is_empty`, `.is_valid`, `match` or branch | String emptiness, address presence, and success are separate semantics |
| Public `fn foo(enabled: bool)` / `fn foo() -> bool` / `pub attr: bool` / enum payload bool | **Warn in initial compatible mode; eventually error in all profiles** | Ask for `unit`/enum/state with semantic meaning, including nested exports and generated code |
| Private/internal `fn _is_valid(x: text) -> bool` | **Allow** | Wrapper churn would be counterproductive; public boundary is the policy edge |
| `extern fn` C ABI parameter `bool` and internal wire bool field | **Allow scoped boundary**, with typed public facade | ABI/extern representation must stay accurate |

**Avoid redundant `@boolable`:** bool-backed `unit` *already* has a Boolean underlying representation. A compiler check should resolve it without traits, dynamic dispatch or user annotation. A standalone `@boolable` attribute for numeric types is only worth retaining if there is a demonstrated use case with a single deterministic `to_bool` rule and no third/unknown state; otherwise prefer explicit `.is_nonzero()` or `count > 0_Bc`. No new reserved keyword is introduced. If `@boolable` does not currently exist in the target branch, treat it as an **optional design** rather than falsely reporting it as implemented (none was found in the sampled paths).

**Recommended public example:**

```simple
unit IsReadable: bool
unit IsWritable: bool

# Raw bool remains appropriate *inside* the implementation.
fn raw_check_readable(fd: i64) -> bool:
    ...

pub fn can_read(file: FileHandle) -> IsReadable:
    IsReadable.from_bool(raw_check_readable(file.raw_fd()))

val readable = can_read(file)
if readable:
    read_file(file)

# Public APIs with more than two meaningful values prefer a real enum.
enum FileOpenDisposition:
    Opened
    Missing
    PermissionDenied
    InvalidPath
```

`IsReadable.from_bool` is **illustrative** of a checked and visibility-controlled constructor; no claim of currently supported method syntax. This construction may compile away, but must not convert `IsReadable` into `IsWritable` through primitive fallback. For a public predicate where a wrapper adds no understandable domain meaning, the lint may suggest `enum`/Result with an exception-review path; do not silently exempt all `is_*` functions, which would defeat the user's requested public-type rule.

### 15.2 Compiler and interpreter algorithm

1. Typecheck the condition once and resolve aliases; accept `bool` or a sealed `unit` whose *direct verified representation* is `bool`. Do not strip arbitrary nested wrappers or accept `i1` merely because its physical ABI matches.
2. Lower `ConditionTruth(unit_bool)` to the same single-bit branch as `bool`, with no call, heap allocation or per-iteration check; record nominal origin only for diagnostics/debug metadata.
3. For `&&`, `||`, `not` on bool-backed unit values, **default result is plain `bool`**. If the domain needs a named result, define the relevant operator explicitly; never automatically return the left-hand unit type.
4. In interpreter constant folding and REPL expression evaluation, apply exactly the same contextual rule table and error code as compiler. Preserve nominal identity outside the branch.
5. Add negative tests against `if 3`, `if 0_Bc`, `if ""`, `if 127.0.0.1_ip`, implicit `IsReadable -> IsWritable`, and direct wrapping of unvalidated external data.

## 16. Text construction, concatenation, escaping and stream semantics

### 16.1 Operators must follow type meaning

| Operation | Policy | Result / error |
|---|---|---|
| `text + text` | Allow for compatibility and ordinary short prose | `text`; optimize chains using string builder only where measurable |
| `text - text`, `text * text`, `text / text` | **Reject** | Dedicated binary-operator type error, not text concatenation |
| `LogText + LogText` | Permit **only** if the `LogText` unit explicitly derives `Concat` with log-safe builder semantics | `LogText`; preserve sink escaping, size bound and safe field separation |
| `UiText + UiText` | Optional domain-specific `Concat` | `UiText`; must not be implicitly upgraded to HTML or a terminal-safe payload |
| `UiText + text` / `LogText + text` | **Reject implicit** or require explicit checked builder append | Avoid untrusted raw text joining a validated output-domain value |
| `SafeHtml + text` | **Reject**; use `html.escape_text(value)` or typed builder | Raw text cannot be promoted to trusted HTML by `+` |
| `SafeHtml + SafeHtml` | Only via trusted fragment builder with explicit context | A document fragment is not safe in JS/CSS/attribute context |
| `SqlQuery + text`, `SqlQuery + SqlQuery` | **No unrestricted `+`** | Use SQL AST/builder and typed parameter binding, not textual interpolation |
| `Path + text`, `Url + text`, `HostName + text` | **Reject** | `.join_component`, `.with_query`, `.subdomain` respectively with checked components |
| `IpAddr + text` / `IpAddr + integer` | **Reject** unless a named, checked address offset operation exists | No accidental byte-string and address arithmetic |
| `SecretText + text` / logging a `SecretText` | **Reject** by default | Explicit capability/approved redaction or memory-safe secret-handling bridge |
| `StreamIn<T> + StreamOut<T>` | Not value concatenation; capability composition requires named method | `.pipe_to`, `.map`, `.decode`, `.encode` with backpressure |
| Repeated append in a loop (`acc = acc + item`) | Warn at perf-analysis level when likely quadratic | Suggest streaming writer, reserved builder, or rope; no global runtime rewrite |

**Specific finding:** `src/compiler/10.frontend/core/type_inference.spl` `infer_binary_op_type` currently groups `+`, `-`, `*`, `/` and returns `TYPE_TEXT` for matching text operands. `src/app/interpreter/expr/arithmetic.spl` supports text concatenation only in `eval_add`. A later semantic pass may already reject the other operators, so the mismatch is a **potential type-inference bug requiring end-to-end SSPEC reproduction**, not a proven accepted expression. Fix the early inference gate and ensure the same final diagnostic in compiled and interpreted execution.

Suggested semantic operation interfaces (exact trait names to be reconciled with existing Simple operator traits; not compulsory keywords):

```simple
# Conceptual typed API, not a verified parser grammar.
pub fn log_field(value: text) -> LogText       # strips forbidden control escapes,
                                               # caps bytes, marks trust source
pub fn ui_display(value: text) -> UiText       # ordinary safe presentation domain
pub fn html_text(value: text) -> SafeHtml      # HTML *text-node* escaping only
pub fn sql_query(template: SqlTemplate, args: [SqlArg]) -> SqlQuery
pub fn parse_host(value: text) -> Result<HostName, HostError>

val log_line = log_field(request.user_name)  # validation at boundary
logger.write(log_line)

val q = sql_query("SELECT id FROM users WHERE name = ?", [user_name])
db.execute(q)
```

Compiler/linter must reject a supposedly safe constructor that simply returns an unchecked re-tagged `text` into a high-risk sink, unless the implementation is explicitly trusted/reviewed. Auto-fix must **not** turn arbitrary SQL concatenation into guessed parameter semantics; offer a reviewed edit or fail closed when structure cannot be inferred.

### 16.2 Directional IO and UI types

Use `UiIn<T>`, `UiOut<T>`, `StreamIn<T>`, `StreamOut<T>` as **channel/capability** types: they identify which side may receive, send, decode, encode, or render. They are not primitive type aliases and should not be created just to rename a `text` variable. Prefer existing `TextSessionCodec` and `ExternalText` as the actual byte-to-text adapter, with generic channel wrappers implemented over those same codecs.

```simple
# Conceptual signatures (constrained by the existing asynchronous/synchronous API).
pub fn read_user_input(source: UiIn<text>) -> Result<text, UiError>
pub fn show_message(sink: UiOut<UiText>, value: UiText) -> Result<(), UiError>
pub fn send_line(stream: StreamOut<text>, value: text) -> Result<(), IoError>
pub fn recv_line(stream: StreamIn<text>) -> Result<text, IoError>

# HTML output is a different sink: it does not accept an unescaped UiText.
pub fn show_html(sink: UiOut<SafeHtml>, fragment: SafeHtml) -> Result<(), UiError>
```

The *direction* and *value's trust domain* are orthogonal: `StreamIn<text>` does not imply received bytes were authenticated, valid Unicode, safe SQL or safe HTML; a socket may yield `ExternalText` requiring an explicit codec. `UiOut<SafeHtml>` does not imply that `SafeHtml` is suitable for JS strings or CSS values. Full-duplex channels combine two capabilities rather than allow an unsound cast. File/process/network streams already implement buffer limits and codec choices; new wrappers **delegate** and do not reimplement framing, BOM or error propagation.

### 16.3 Text security rules by boundary

- **HTML/DOM:** escape by output *context* (HTML text, attribute, JS, CSS, URL); safe HTML text is not interchangeable with safe attribute text. A builder for rich markup must distinguish trusted static templates from runtime substitutions. OWASP XSS rules apply; no universal `SafeText` type.
- **SQL:** bind parameters through the DB driver; validate or whitelist identifiers separately. Store `SqlQuery` as a structured representation or a sealed prepared-query handle where feasible; serializing it for the driver is a controlled boundary.
- **Shell/process:** `Command` and `Argv` should be typed arrays; avoid raw shell command strings. If the caller intentionally invokes a shell, use a distinct audited `ShellScript` capability and shell-specific quoting.
- **Paths:** preserve canonicalization/join semantics of existing `Path`; `SafeRelativePath` must reject absolute, parent traversal and platform-specific escape patterns before root-bound joining. Opening a path must still resist symlink/time-of-check-to-time-of-use attacks using OS capabilities when required; a string wrapper alone cannot ensure containment.
- **Log/terminal:** `LogText` sanitizer is sink-specific, bounded and redacting. TUI/CLI terminal output separately neutralizes ANSI/control sequences from untrusted users; structured log fields encode newline/control properly without losing legitimate text content.
- **Net/HTTP:** parsed typed `Url`, `HostName`, `IpAddr`, HTTP header name/value, cookie text and bearer secrets each have independent grammar and size limits. A generic `text` parse boundary returns `Result`, never truncates into a valid trusted identity silently.
- **Secrets:** do not add format/concat, logging, debug/replay or automatic serialization traits to `SecretText`; zeroization/ownership requires separate verification and may rule out generic `text` storage for actual cryptographic keys.
- **Encoding:** decode external bytes explicitly once; normalization/case folding/IDNA as dictated by the domain; preserve Unicode bytes across ordinary text UI and log sources where allowed. Do not silently normalize all text on every function call.

## 17. Preserve and complete existing `_ip`: IPv4, IPv6 and host identity

The source already defines `Ipv4Addr` as four octets, `Ipv6Addr` as 16 bytes, and `IpAddr` as the tagged sum `V4(Ipv4Addr) | V6(Ipv6Addr)` in `src/lib/common/net/addr.spl`. The audited file's blob is identical at the inspected main and `release/1.0.0` refs; **the entire release branch's `_ip` parser/lexer behavior was not fetched or executed**. The user reports `_ip` is already used there. Preserve that suffix and its compatibility. Do **not** reduce `IpAddr` to a 16-bit scalar or force every IPv6 group into a separate public wrapper.

| Syntax / operation | Desired static meaning | Checks |
|---|---|---|
| `127.0.0.1_ip` | `IpAddr.V4(Ipv4Addr)` or existing compatible precise address type | Four decimal octets `0..255`, no malformed extra groups |
| `2001:db8::1_ip` (only if suffix grammar already permits it) | `IpAddr.V6(Ipv6Addr)` | At most eight **16-bit** groups, `::` compression rules, `0..FFFF` per group, exactly 128-bit expanded value |
| String parse `IpAddr.parse(value: text)` | `Result<IpAddr, IpParseError>` | Full-string parse, no permissive partial match, normalization only on formatting |
| `Ipv4Prefix` / `Ipv6Prefix` | Family-specific route network/prefix | `0..32` bits for v4, `0..128` bits for v6; existing raw `RoutePrefix.prefix_len:u8` cannot enforce correct family by itself |
| `SocketAddr` | `IpAddr + Port + optional scope` | Bracket IPv6 host in URI/host:port; scope handling for link-local addresses; no confusion with URL/text |
| IPv6 scope/zone ID | Explicit separately validated property | IPv6 address bits do not contain interface scope; scoped addresses are context-specific (RFC 4007) |
| `HostName` | DNS name/IDNA checked value, **not** `IpAddr` | DNS canonicalization and certificate validation policy, no implicit hostname-to-IP cast |

If an unbracketed IPv6 literal conflicts with the existing colon/indentation grammar or GPU-friendly lexer, use the *existing release-branch `_ip` forms* as the compatibility authority and add compile-time parse validation without a new keyword. Any new alternative spelling needs an explicit grammar/SSPEC comparison, not a silent change. Constant literals parse once at compile time and enter typed HIR as 4/16 bytes; a run-time text parse remains an explicit boundary. Follow RFC 5952 for canonical **formatting** (not for rejecting all noncanonical valid input), RFC 4007 for scoped IPv6; URL bracket/port serialization uses the existing `Url`/`SocketAddr` builder.

Do not overfit the `unit` feature to `IpAddr`: `IpAddr` is a **tagged enum containing two real representations**, not a trivial nominal wrapper over text or u16. Network ports, prefix lengths and packet sizes can be units; IPv4/v6 families must remain discriminated.

## 18. Shared diagnostics: missing warning, version schedule and ranked fixes

### 18.1 One rule owner and separate numeric/Boolean/text decisions

The baseline primitive checker already includes `bool`, but the effective API lint is incomplete and an existing EasyFix returns its original source line. A rule that appears configured as `deny` may still not produce the intended error when the scanner or dispatch misses a symbol. **Do not infer actual release enforcement from rule configuration.** The first implementation ticket is a reproducible `pub fn f(b: bool) -> bool` SSPEC run through each entry point, verifying *emission* and *level*, then repair the semantic exported-signature traversal and duplicate dispatch.

Proposed stable rule families (IDs to be registered in existing registry, not a second Error framework):

| Rule ID | Trigger and default phase | Ranked suggestions / fix notes |
|---|---|---|
| `SPL-BOOL-001` | Raw `bool` as effectively public parameter, result, attribute, nested payload; compat **Warn**, robust+ **Deny**; eventually all profiles Deny | 1) enum if multi-state; 2) `unit DomainFlag: bool` and migrate callers; 3) narrow, reviewed ABI facade exception |
| `SPL-TEXT-001` | Public raw `text` used as a **known semantic domain** (path, host, credential, executable query, HTML sink, etc.), not all text | 1) existing `Path`/`Url`/`HostName`/domain type; 2) checked parser/constructor at boundary; 3) structured builder/parameterization |
| `SPL-TEXT-002` | Validation boundary failure or uncontrolled `text`→high-trust unit conversion | 1) `Result`-producing parse; 2) use validated existing API; 3) manual review if trust cannot be established |
| `SPL-TEXT-003` | Invalid `text` operator, mixed nominal concat or unsafe HTML/SQL concatenation | 1) `+` only for actual text concatenation; 2) domain builder; 3) parameter bind / contextual escape; unsafe code is a hard error where required |
| `SPL-TEXT-ENC-001` | Byte/grapheme/UTF-16 index or explicit transcoding/length mismatch | 1) named conversion; 2) proper byte-grapheme index; 3) codec-boundary fix |
| `SPL-IP-001` | IPv4/v6 family mismatch, invalid literal/prefix width, unsound text/IP cast | 1) family match and checked parse; 2) corrected prefix; 3) typed address and socket constructor |
| `SPL-UNIT-001` | Legacy `newunit`; existing §4 warning schedule retained | Token-only rewrite to `unit`, no semantics change |
| `SPL-TYPE-001` | Existing primitive API numeric/unknown domain; preserve current ID and policy | Unit/enum/typed facade; note `SPL-BOOL-001` uses different more specific message to avoid duplicate warnings |

When a type is simultaneously a primitive and a semantic sink, give the *most specific* rule as the primary diagnosis with related notes, not two redundant warnings on the same type path. For `text`, classify the resolved API name, declared domain tags, parameter flow to known sinks and the actual public type graph; **do not** rely only on names like `path` or `sql` from raw source text. Flow analysis beyond resolved direct call edges is **CI/analysis mode only**; unknown cases in default mode can remain informational instead of confidently proposing the wrong wrapper.

### 18.2 Policy lifecycle (now → warning → error → later removal)

Use §4 `DiagnosticRulePolicy` and `DiagnosticV1` for all new rules. For **all** relevant `bool` public APIs, including apparently simple predicates, the desired final profile policy is `deny`; a permitted ABI exception must be explicit, scoped, owner-reviewed and time-bounded. For ordinary public `text`, there is **no universal deprecation deadline**; schedule **only** the cases with demonstrated domain and trust violations. Syntax `newunit` is a separate warning-to-error-to-removal lifecycle, not lumped together with raw-bool enforcement.

Suggested policy metadata additions (all dates after registration are **proposals** and must be ratified by release owner):

```sdn
diagnostic_policy:
    version: 2
    rules:
        SPL-BOOL-001:
            created_on: "2026-11-16"
            warn_since_date: "2026-11-16"
            warn_since_lang_version: "<first-shipping-version>"
            error_not_before_date: "<ratified-future-date>"
            error_since_lang_version: "<ratified-breaking-edition>"
            modes: {advisory: warn, moderate: warn, strict: deny, robust: deny, critical: deny, verified: deny}
            exceptions: {ffi: reviewed, wire: reviewed, private: allowed}
        SPL-TEXT-001:
            created_on: "2026-11-16"
            warn_since_lang_version: "<first-shipping-version>"
            error_since_lang_version: "<per-domain-approved-edition>"
            modes: {advisory: warn, moderate: warn, strict: warn, robust: deny, critical: deny, verified: deny}
            excludes: [ordinary_prose, diagnostic_message, serialized_text_data]
```

Placeholders above must **not** enter the shipping policy registry unchanged. Maintain two distinct dates: human-readable announcement/earliest eligible error date and selected version that actually turns the rule into an error. Build reproducibility and policy digest keys follow §4; don't make a compiler built yesterday turn red tonight just because the wall clock rolled over. `@allow`/HAL exceptions cannot bypass high-assurance publication gates without an explicitly audited boundary declaration.

### 18.3 Multiple actionable auto-fixes and clear errors

Shared `DiagnosticV1` extensions in §5 should include a **ranked list of actions** (`Safe`, `ReviewRequired`, `UnsafeNotAutomatic`) with editable spans, type/caller graph impact, precondition hashes and versioned `WorkspaceEdit`. Hide empty/no-op replacements and reject source edits if only whitespace/no type was changed. A fix that introduces `unit Flag: bool` is not complete if it fails to update constructor and call sites; the preview must show linked changes, not just the public signature.

Example (illustrative error format, **not observed current output**):

```text
src/lib/game2d/backend/trait.spl:19:5: warning[SPL-BOOL-001]
  public attribute `WindowConfig.vsync` exposes bare `bool`
  expected: named two-state `unit` or domain `enum` in exported API
  reason: `fullscreen` and `vsync` have independent semantic meanings
  fixes:
    [1 Safe/Review] use `VsyncEnabled: bool` and rewrite 7 known call sites
    [2 Review] use `VsyncMode {Enabled, Disabled}`
    [3 Manual] move raw flag to private native backend and expose typed accessor
  schedule: currently warn in compatibility mode; high-assurance mode is error
```

For `get(url: text)`, the top suggestion should be **reuse the existing `Url`**, with a compatibility overload that calls `Url.parse` once at ingress, not invent another `HttpUrl` class; if the parser can fail, return `Result` and update callers. For `EditorDiagnostic.severity:text`, propose enum extraction, while `message:text` remains unaffected. For `SqlQuery`, do not offer a confidence-ranked automatic transformation unless parameterization semantics can be proved. For `newunit`, token-local replacement is safe; for numeric `newtype`, give review-required operator migration when implicit arithmetic might be lost.

Same diagnostic ID, text, source location and severity policy must flow through compiler, interpreter, `simple lint`, LSP, CMM debugger, MD/SDN/SHS editor adapters and build/test runner reports. Output rendering differs by client, but **detection and decision do not**.

## 19. Implementation sequence by mdsoc+ layer and library family

Execute in small, SSPEC-backed batches. Do **not** mass-rewrite all `text` values as nominal types or create a parallel error framework. Preserve existing `Path`, `Url`, `IpAddr`, `ExternalText`, `TextSessionCodec`, and their public compatibility surfaces until callers are migrated.

| Phase / gate | Compiler + interpreter | Libraries/runtime/UI | Observable completion |
|---|---|---|---|
| **T0: inventory and failing reproductions** | Capture `simple check/build/lint` + REPL + LSP behavior for bare public bool, nominal bool, raw text URL, invalid string arithmetic; inspect exported graph and no-op EasyFix | Source inventory includes every `src/lib` class/struct/enum/method, re-export, __init__, generated API, all variants | Versioned baseline CSV/SDN/JSON inventory with counts and observed warning/missing-warning evidence |
| **T1: shared diagnostics P0** | Connect semantic API checker, fix duplicate lint and severity handling, `DiagnosticV1` adapter, policy schedule, no-op fix removal | Editor receives true code actions; CMM and MD adapters normalize severity/span; fix list survives | Same code+span+severity for identical finding in 5 entry paths; no duplicate/no-op warnings |
| **T2: single `unit` compiler representation** | One AST/HIR `UnitDecl`; deprecate `newunit`/relevant `newtype`; text-backed nominal metadata, bool-backed contextual condition, operator table, MIR preservation | Interpreter nominal identity, loader cache keys, C/LLVM/SFFI ABI proof, UTF-8/ownership correctness | Numeric/unit/bool/text SSPEC parity; GPU lexer grammar cost measured; zero-cost bool branch and no text copy regression |
| **T3: high-risk text security boundaries** | Semantic domain rule classifier, checked `text`→trusted type construction, contextual `Concat`/builder validation | Security audit, native tool authority, SQL/SQLCipher, shell/process, HTTP/TLS/browser URL and cookies, `Path`, net address, terminal output | SQL injection, path traversal, log forging, CRLF, XSS, cookie/hostname tests; no raw text added at trusted sink |
| **T4: typed streams and visible UI** | Generic directional capability checks without new grammar; consistent inferred value type | Reuse File/UDP/TCP/Process `TextSessionCodec`, `ExternalText`, and IO errors; `UiIn/UiOut`, `StreamIn/StreamOut`; editor diagnostics and game2d config | Encoding/async/backpressure/error tests; UI renderer no unsafe raw HTML escalation; existing codec unchanged |
| **T5: full public bool migration** | Enable `SPL-BOOL-001` emission in all profiles; staged ratified promotions | Enumerate and migrate `Config.enabled`, `WindowConfig.vsync/fullscreen`, `HttpClient.follow_redirects`, public `is_*` results, generated attrs, enum payloads; minimize wrappers where enums/Results better | Zero unowned, nonexempt public bool findings in robust/critical/verified; warning-only other profiles until ratified transition |
| **T6: library sweep and release** | Warm incremental cache, effect/ABI checks, per-rule version gates; release loader compatibility | All lib surfaces, OS/NVMe and build/test runners; source guide and migration cookbook | Full repo inventory coverage, caller compilation, SSPEC traceability, CI performance thresholds, release/branch compatibility |

### 19.1 Ownership map and no-duplicate rule

- **`00.common`**: `DiagnosticV1`, versioned policy registry and common semantic type representation IDs; data formats with canonical endian for cache metadata.
- **`10.frontend`**: legacy and unified unit parsing, `_ip` suffix compatibility, text/boolean literal typing, source-location mapping; syntax errors and expected-token suggestions.
- **`30.types`**: representation metadata, unit identity, resolved exported graph and domain operator proofs; compile-time constructor legality.
- **`35.semantics`**: **single** authoritative primitive/public Bool/text-domain lint and trust-boundary admission; separate cheap type gate for operators.
- **HIR/MIR/optimizers**: preserves semantic identity until validation is complete; then zero-cost representation lowering; prevents invalid concatenation and wrong ABI re-tagging. No separate MIR per MinGW/MSVC merely for a nominal text unit—use target ABI lowering as needed.
- **`80.driver` + interpreter**: same warning/error policy and diagnostic sink, robust admission/publication, no silent warning-phase downgrade of mandatory rules.
- **`90.tools` + LSP/CMM/Editor/CLI**: ranked code actions, versioned file edits, provenance, visual preview and one-click safe batches; never independently infer correctness from regex line snippets.
- **`std.common.encoding`, `std.io`**: existing `ExternalText` and text codecs remain the sole bytes/text bridge; directional wrappers are thin adapters, never duplicate decoder implementations.
- **`std.fs`, `std.net`, browser engine**: reuse and reconcile existing `Path`, `Url`, `IpAddr` and parsers; construct trusted sink-specific values only after validation.
- **SSPEC/build/test runner/SCV**: acceptance → unit → implementation links, per-rule policy snapshot in keys, revision-aware fixes, dependency-based incremental rechecks and regression gating.

### 19.2 Compatibility and migration of constructors

Keep legacy string signatures as explicitly deprecated *facades* for one migration window when feasible:

```simple
# Conceptual API direction. Adjust actual syntax to existing Simple grammar.
pub fn http_get(url: Url) -> Result<HttpResponse, HttpError>:
    ...

# Legacy compatibility facade: parse *once* at boundary; not a raw pass-through.
pub fn http_get_text(url: text) -> Result<HttpResponse, HttpError>:
    val parsed = Url.parse(url)?
    http_get(parsed)
```

When the existing Simple overload resolution cannot distinguish constructors ergonomically, use `parse_*` / `from_*` names rather than adding parser complexity. Public overloads must not leak unchecked nominal casts. Do not break encoded ABI or stored network protocols while wrapping fields; wire serialization must preserve exact layouts. For generated getters/setters, use one canonical metadata source for semantic fields and class/attribute policies, including the planned SoA/AoS and `NotInit<>` machinery.

## 20. Compile, memory, runtime and parser-performance constraints

| Concern | Design choice | Target / measurement |
|---|---|---|
| CPU/GPU lexer and LL(1) grammar | `unit` already lexical; semantic types are identifiers; no new token/keyword for text or bool | Parser/token throughput additional cost ≤1% goal on same corpus; malformed grammar fixtures included |
| Exported API graph traversal | Resolve each exposed signature/type path once; memoized structural graph visitor and exact visibility from `__init__` | O(V+E) first pass; only affected signature subgraph invalidated on edits; 3,000-symbol stress |
| Text-domain classification | **O(1)** or interned type-ID tests at known sink/call edges; expensive transitive taint/interpolation analysis only in analysis/CI | Hot compile checks avoid global string scans and per-line regex/JSON allocation |
| Unit arithmetic and contextual bool | Static type dispatch and constant-fold; bool-backed unit lowers to identical branch representation | Release mode no extra branches/allocations; generated MIR and assembly comparison |
| Text-backed unit | Reuse same text handle/ownership representation; constructors validate only at actual ingress/sink; move/borrow rather than clone where safe | Allocation/refcount benchmark vs raw text; false zero-copy assertions forbidden |
| String concat in rendering/logging | Domain-checked builder and buffer reserve; optional rope for repeated large edits | Test N-field concatenation scaling; no quadratic builder regression; record bytes copied |
| Unicode source/UI indices | UTF-8 core, UTF-16 per-line LSP conversion cache and on-demand grapheme mapping | O(affected lines) revision updates; check Korean/emoji/combining mark editing latency |
| Literal `_ip` | Validate at compile time with fixed-width storage; no runtime parse for constant | Steady-state zero allocations and bounded compiler literal-parse cost |
| Text transport | Existing decoder/encoder/limits; no second codec, no duplicate transcoding | Throughput/peak memory on file, UDP, TCP, process sessions; malformed byte test |
| Diagnostics and code actions | Lazy generation of fix candidates; one compact rule-index lookup, summary in normal compile | Prior §7 targets: cold compile ≤3% regression, warm/incremental ≤1% target, no synchronous cross-file editor stalls |
| Debug/CI analysis | Optional trust-flow, path reachability, secret/dataflow, SSPEC completeness, XRay/perf profiling | Heavier cost allowed only explicit analysis/inspection/CI profile; never silently in every key stroke |

All percentages are **planned acceptance budgets**, not measured results. Establish matched cold/warm baselines and test after each phase; report p50/p95 compiler time, peak RSS/allocations, cache-hit ratios, active parser tokens/s, generated code instruction counts, interpreter throughput, UTF-8/UTF-16 conversion latency, bytes copied by concatenation, and graphics/terminal presentation latency. Preserve the existing immutable AST→HIR→MIR→object cache and SCV invalidation model: a **private function body edit must not invalidate unrelated semantic-public API summaries**, while a changed public type or `__init__` export must. Cache policy digest and unit nominal ID; no duplicate pipeline storage of entire source strings.

## 21. Expanded SSPEC, matrix and deployment acceptance

### 21.1 Minimal positive/negative language tests

```simple
# SSPEC-style pseudocode, not assertions that current grammar accepts it.
unit AFlag: bool
unit BFlag: bool
unit LogText: text
unit UiText: text

val a: AFlag = AFlag.from_bool(true)
if a: pass                         # PASS, no @boolable
while a: break                     # PASS
if true: pass                      # PASS; built-in bool is still legal internally
if 3: pass                         # FAIL by default: numeric truthiness
if "hello": pass                   # FAIL: text truthiness

val b: BFlag = a                   # FAIL: nominal bool identity
val c: bool = a                    # FAIL: no general implicit erasure
val d = "a" + "b"                  # PASS: text concat
val e = "a" - "b"                  # FAIL: invalid operator
val f = "a" * "b"                  # FAIL: invalid operator
val g = "a" / "b"                  # FAIL: invalid operator
val h: LogText = "raw"            # FAIL unless constructor/check permits
val i = safe_html + "<img>"        # FAIL: unsafe concat
val j = SqlQuery.from_text(raw)    # FAIL unless trusted/validated restricted constructor
val k = path + "../etc"            # FAIL: use checked path join
```

Additional execution tests must prove a **public `bool` diagnostic** is produced once and correctly promoted in the chosen edition, while `fn private_is_ready()->bool` does not warn. Test nested `[bool]`, `Option<bool>`, generic maps carrying bool, enum payload bool, public get/set-generated attributes, re-exports, macros and parent/child `__init__` visibility. A file with 50 valid ordinary `text` messages should yield **zero text-domain warnings**. A file passing raw text as a TLS hostname, file path, SQL query, HTML sink or security authority digest should show precise typed-boundary suggestions without generating false-positive conversions.

### 21.2 Library and security SSPECs

| Group | Acceptance scenarios |
|---|---|
| `_ip` / network | IPv4 4 octets, IPv6 8×16-bit groups/`::`, mixed/compressed notation, embedded IPv4 as existing grammar permits, invalid overlong segments, family-specific prefix 32/128, link-local zone, canonical format/parse round trip, URL host:port bracket behavior, existing release literals |
| UI and Unicode | Korean syllables/jamo, Japanese CJK, emoji ZWJ, combining accents, bidi/control text, empty and multi-megabyte input, grapheme cursor vs UTF-16 LSP positions, IME composition; no implicit text truthiness |
| Logging | CRLF/log forging, tabs/ANSI control, long fields, redaction, multiline structured event, terminal vs file vs JSON context, secret never printed or emitted in diagnostics, severity enum preserved |
| SQL/HTML/cookie | Parameter binding, quote injection, identifiers, XSS in HTML text/attribute/JS/CSS/URL separately; encoded cookie lengths, header CRLF, domain/path validation, exact old cookie behavior for valid inputs |
| Paths/process | Absolute/relative mixes, traversal and symlink test, Windows UNC/drive, POSIX path, process argv with spaces/metacharacters, shell-only explicit capability, artifact/digest 64-hex normalization with binary hash comparison |
| TextSessionCodec | UTF-8/UTF-16 and BOM combinations already supported by codec, invalid sequences, strict byte limit, direction mix-up, cancellation, EOF, timeout and peer-address type, streaming backpressure; same result/error as old APIs |
| `bool` public migration | Window Vsync/Fullscreen, audit config, HTTP redirect policy, game2d key events, HTTP status, security predicates; no third state squeezed into a bool wrapper, no private-bool false positives |
| Compiler+interpreter | String `-/*` rejected consistently; unit text identity stable across HIR/MIR/REPL/loader serialization; C bool ABI and text ownership; nominal interpolation and formatting policy tested |
| Diagnostics | Compiler, check, lint, REPL, LSP, Editor, CMM and build runner same source rule; multiple ranked fixes, no empty edits, stale workspace edit denied, policy schedule reproducible, no duplicate complaint |

### 21.3 Exhaustive inventory gate (not yet run)

The actual full sweep must read all source files and generated public API manifests on `main` **and** `release/1.0.0`, not just sparse files. Enumerate `src/compiler`, `src/app/interpreter`, `src/lib`, UI/browser/game2d, `src/os`, NVMe firmware, common/net/security/crypto/SQL, and platform variants. Use resolved AST/HIR effective visibility to output:

`module, file, symbol-id, exported-type-path, underlying primitive, semantic domain, trust source/sink, text encoding, owner, FFI exemption, ranked fix, caller count, mode severity, first-warn version, planned-error version, status, acceptance-sspec, migration commit`.

Inventory must distinguish **actual exposed declarations** from grep matches and merge monomorphizations without double-counting. Add a report by domain and by layer; regression gate CI on new unreviewed public `bool` after T5 and on high-risk trusted sink leaks after T3. Test relative/absolute paths, internal source spans and active cfg/OS branch; don't silently omit platform variants from cross-target traceability.

### 21.4 Implementation exit checklist

- [ ] Confirm same source+revision in main/release branch; obtain complete blob and `_ip` implementation coverage; record exact commit IDs for acceptance.
- [ ] Failing repro for current primitive bool warnings, high-risk text not caught, no-op fix and `text -/*` inferred text; identify if a later checker already errors.
- [ ] One policy owner and one diagnostic owner wired; no no-op fixes; exact span, UTF-16 mapped offset, multiple ranked actions.
- [ ] `unit: bool` conditions and `unit: text` ownership fully tested, no new keywords, `newunit` warning preserved.
- [ ] Existing `Path`, `Url`, `IpAddr`, `ExternalText`, `TextSessionCodec` reused; no parallel incompatible API implementation.
- [ ] Public bare bool warn→error phases versioned; strong modes enforce error now; ordinary prose `text` remains legal in all modes.
- [ ] High-risk sink constructors validated; no implicit text upgrade; explicit concat/builder matrix is consistent in both execution engines.
- [ ] Full library/source inventory available in machine-readable form with exclusions and owners; each migrated API linked to SSPEC and callers.
- [ ] ABI/FFI layout, interpreter behavior, UTF-8/UTF-16 semantics, security tests, cache invalidation and compile/runtime budgets pass.
- [ ] Language guide, changelog, migration recipes, CI, LSP Editor/CMM/MD/SDN/SHS views updated in the *same release* as diagnostics.

## 22. Research and standards cross-check for the focused update

Primary sources informing **proposed design**, not evidence of current Simple implementation:

1. Unicode UAX #29, *Unicode Text Segmentation*: grapheme/word/sentence boundaries differ from bytes and code points. <https://www.unicode.org/reports/tr29/>
2. Unicode UAX #15, *Unicode Normalization Forms*: normalization must be explicit when required by the domain; it is not a universal display-string transformation. <https://www.unicode.org/reports/tr15/>
3. OWASP, *Cross Site Scripting Prevention Cheat Sheet*: context-specific HTML/attribute/JS/CSS/URL encoding, supporting distinct trusted output types. <https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html>
4. OWASP, *SQL Injection Prevention Cheat Sheet*: prepared statements/parameterized queries, not escaped concatenated SQL. <https://cheatsheetseries.owasp.org/cheatsheets/SQL_Injection_Prevention_Cheat_Sheet.html>
5. OWASP, *Logging Cheat Sheet*: log injection/sanitization and sensitive data considerations. <https://cheatsheetseries.owasp.org/cheatsheets/Logging_Cheat_Sheet.html>
6. OpenTelemetry, *Logs Data Model*: structured log attributes are richer than a formatted message; justification for `LogEvent` separate from `LogText`. <https://opentelemetry.io/docs/specs/otel/logs/data-model/>
7. RFC 4291, *IPv6 Addressing Architecture*: 128-bit addresses; RFC 5952 canonical IPv6 *text representation*; RFC 4007 scoped IPv6 addresses. <https://www.rfc-editor.org/rfc/rfc4291> · <https://www.rfc-editor.org/rfc/rfc5952> · <https://www.rfc-editor.org/rfc/rfc4007>
8. Rust std `IpAddr` tagged V4/V6 as precedent for family-sensitive address type. <https://doc.rust-lang.org/std/net/enum.IpAddr.html>
9. Ada reference manual Boolean types and C++ contextual conversion to bool illustrate that **condition convertibility** is narrower than indiscriminate implicit type equivalence; this report's exact `unit` rules are an original Simple design decision, not a copy of those languages. <https://www.adaic.org/resources/add_content/standards/12rm/html/RM-3-5-3.html> · <https://en.cppreference.com/w/cpp/language/implicit_conversion.html>

**Final scope statement (2026-11-16):** This is **one consolidated implementation and documentation plan** covering the previous numerical/unit/primitive/error infrastructure work *and* newly source-audited `text`, custom Boolean, IP, UI, streams, logs, security and full-library migration. It updates the plan, not the Simple implementation. Source observations are separated from planned behavior, and incomplete sparse-branch coverage, warning enforcement, measured performance and actual fixes remain implementation/verification gates.
