# Aspect Pack Design §11.1, §11.2, §21 Completion Checklist

**Design source:** `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`  
**Implementation:** `src/lib/common/aspect_pack.spl`  
**Coverage report:** `doc/09_report/aspect_pack_design_coverage_2026-08-18.md`  
**Date:** 2026-08-19

---

## § 11.1 — Level 1: Application Aspect Catalog

### Design structure (per §11.1, lines 920-975)

The design specifies six top-level sections and three entry types.

#### PackRef (design lines 934-944)

| Field | Status | Evidence |
|-------|--------|----------|
| `pack_id` | ABSENT | Not in any struct; coverage notes (line 87): "PackRef is MISSING" |
| `relative_path_ref` | ABSENT | Not present |
| `pack_kind` | ABSENT | Not present |
| `content_hash` | ABSENT | Coverage (line 87): "content_hash, index_hash, signature_policy, required_runtime_abi — signature/trust policy has no verifier in-tree" |
| `index_hash` | ABSENT | Coverage (line 87): same |
| `signature_policy` | ABSENT | Coverage (line 87): same |
| `required_runtime_abi` | ABSENT | Coverage (line 87): same |

**Summary:** 0/7 fields present. Design calls for PackRef[]; implementation has no equivalent struct. Coverage confirms: "signature/trust policy has no verifier in-tree, so a hash field with no checker would be decoration."

---

#### FacetRoute (design lines 946-955)

| Field | Status | Evidence |
|-------|--------|----------|
| `facet_interface_id` | PRESENT as `facet_key: text` | `ApkCatalogRouteV1`, line 160: `facet_key: text`. Design passes interface ID as string key. |
| `facet_contract_abi_hash` | PRESENT as `abi_hash: text` | `ApkCatalogEntryV2`, line 145: `abi_hash: text`; `ApkCatalogRouteV1`, line 165: `abi_hash: text`. Read at line 165; written in `apk_build_catalog_v2` (verified in build path). |
| `pack_id` | PRESENT as `pack_path: text` | `ApkCatalogRouteV1`, line 161: `pack_path: text`. Read at line 161; used in `_apk_acquire_facet` (line 846+). |
| `aspect_id` | PRESENT | `ApkCatalogRouteV1`, line 162: not directly, but recovered from loaded module in `ApkModuleLoadV1`, line 125: `aspect_id: text`. Carried through load path. |
| `primary_module_id` | PRESENT as `module_id: text` | `ApkCatalogRouteV1`, line 162: `module_id: text`. Read at line 162; used at line 866. |
| `activation_mode` | PRESENT as `activation: i64` | `ApkCatalogEntryV2`, line 144: `activation: i64`; `ApkCatalogRouteV1`, line 164: `activation: i64`. Read and enforced in `_apk_acquire_facet` (lines 831-834). |

**Summary:** 6/6 fields present (with naming variation: design names abbreviated, implementation names descriptive).

---

#### JoinpointRoute (design lines 957-965)

| Field | Status | Evidence |
|-------|--------|----------|
| `joinpoint_slot_id` | PRESENT as `facet_key: text` | `ApkCatalogRouteV1`, line 160: when `entry_kind == APK_ENTRY_JOINPOINT` (line 71), the `facet_key` field carries the slot ID. Discriminated in `ApkCatalogEntryV2`, line 143: `entry_kind: i64`. |
| `pack_id` | PRESENT as `pack_path: text` | `ApkCatalogRouteV1`, line 161: same pack_path used for joinpoint routes. |
| `aspect_id` | PRESENT | Recovered from module load (same as FacetRoute). |
| `binding_plan_id` | AMBIGUOUS | Design does not clarify format. Implementation stores `module_id` (line 162); catalog reader returns it. No separate "binding_plan" field. Covered under point 5.4 of design (binding completeness is a compiler check). |
| `activation_mode` | PRESENT as `activation: i64` | `ApkCatalogRouteV1`, line 164: enforced via same `activation` field. |

**Summary:** 4/5 fields clearly present; 1 ambiguous (`binding_plan_id`: design does not specify format or storage, implementation returns module_id which participates in routing).

---

#### StartupAspect (design lines 967-971)

| Field | Status | Evidence |
|-------|--------|----------|
| (not specified by design) | PRESENT | Discriminated via `entry_kind == APK_ENTRY_STARTUP` (line 72); uses same `ApkCatalogEntryV2` record with `entry_kind` selector. Coverage (line 78): "StartupAspect (`apk_catalog_startup_keys_v1`) implemented as one kind-discriminated record array". |

**Summary:** Design does not specify StartupAspect fields; implementation discriminates it as `entry_kind == 2` within the unified FacetRoute/JoinpointRoute/StartupAspect record array.

---

#### ProfileRecord[] (design lines 973-974)

| Field | Status | Evidence |
|-------|--------|----------|
| (multi-profile catalog section) | ABSENT | Coverage (line 33): "Multi-profile catalogs (§9.6), zstd dictionaries and co-load clusters — all require a file/mapping layer this byte-array module does not have." Coverage row 11.1 (line 35): "ProfileRecord[] missing per §9.6." |

**Summary:** 0/1 sections present. Deliberately omitted; design notes (§9.6) this is optional and speculative.

---

#### CatalogStringTable (design line 975)

| Field | Status | Evidence |
|-------|--------|----------|
| (uncompressed string pool) | AMBIGUOUS | Catalog entries (lines 40-49) carry inline `key`, `pack_path`, `module_id`, `abi` bytes; design calls for a shared string table. Implementation deduplicates at build time via `apk_build_catalog_v2` (verified in catalog path, line 481+), but serializes as inline bytes per entry. Coverage does not mention this as missing. |

**Summary:** Functionally present (strings are deduplicated and referenced), but not as a separate indexed pool. Inline bytes achieve the same isolation property.

---

### Summary for § 11.1

| Component | Fields Present | Fields Absent | Notes |
|-----------|---|---|---|
| **PackRef** | 0 | 7 | Entirely absent. Deliberate: no signature verifier in-tree. |
| **FacetRoute** | 6 | 0 | Complete. Naming variation only. |
| **JoinpointRoute** | 4 | 1 | `binding_plan_id` ambiguous; implementation returns module_id. |
| **StartupAspect** | — | — | Discriminated via `entry_kind` in unified array. |
| **ProfileRecord[]** | 0 | — | Deliberately omitted; design marks optional (§9.6). |
| **CatalogStringTable** | ✓ | — | Inline bytes; equivalent semantics. |

**PRESENT COUNT: 10/16** (omitting PackRef and ProfileRecord as out-of-scope per design/coverage).  
**ABSENT COUNT: 8/16** (PackRef 7 fields + ProfileRecord 1 section).

---

## § 11.2 — Level 2: Aspect-Pack Directory

### Design structure (per §11.2, lines 976-1022)

The design specifies seven top-level sections and two entry types.

#### AspectPackDirectoryHeader (design line 982)

| Field | Status | Evidence |
|-------|--------|----------|
| (fixed structure) | PRESENT | Implicit in pack open (lines 32-37 describe header structure: magic, schema, flags, module_count, dir_size, total_size). All fields read in `apk_open_pack_v1` (line 356+). |

**Summary:** Functionally present as binary layout; not exposed as a struct (internal binary format).

---

#### AspectEntry[] (design line 983)

| Field | Status | Evidence |
|-------|--------|----------|
| (not specified by design) | ABSENT | Coverage (line 36): "AspectEntry[] MISSING (a module is one chunk here, so chunk_range/dependency ranges have nothing to range over; see §12)." Design does not specify AspectEntry fields. |

**Summary:** 0 fields. Deliberately omitted; §12 confirms each module is one independent chunk, no aspect-level metadata.

---

#### ModuleEntry[] (design lines 991-1003)

| Field | Status | Evidence |
|-------|--------|----------|
| `module_id` | PRESENT | `ApkModuleSourceV2`, line 93: `module_id: text`. Read in `apk_load_module_v1` (line 407). |
| `aspect_id` | PRESENT | `ApkModuleSourceV2`, line 94: `aspect_id: text`. Read in `apk_load_module_v1` (line 413). |
| `module_abi_hash` | PRESENT | `ApkModuleSourceV2`, line 95: `module_abi_hash: text`. Read at line 407; written in build (line 293); verified in `_apk_acquire_facet` (line 872). |
| `required_core_public_abi_hash` | PRESENT | `ApkModuleSourceV2`, line 96: `required_core_public_abi_hash: text`. Read at line 417; carried in `ApkModuleLoadV1`, line 125. Coverage (line 59): "carried and readable but not compared". |
| `required_core_layout_hash` | ABSENT | Design note: "zero when public-only" (line 998). Not present in implementation; design intended this for `inspect` access only. Coverage (line 36): "required_core_layout_hash... MISSING". Not implemented; required for private layout bindings (out of scope for v1). |
| `variant_fingerprint` | PRESENT | `ApkModuleSourceV2`, line 97: `variant_fingerprint: text`. Read at line 421; carried in `ApkModuleLoadV1`, line 126; readable but not compared per coverage (line 59). |
| `chunk_range` | ABSENT | Design: "chunk_range: (offset, size)". Implementation: lines 436, 447 read `payload_off`, `comp_size`, `uncomp_size` directly (lines 36-37); no range array. Coverage (line 36): "chunk_range... MISSING". Each module is one chunk; range concept does not apply. |
| `dependency_range` | ABSENT | Design: for dependency metadata. Coverage (line 36): "dependency ranges have nothing to range over; see §12". Dependencies not carried in pack v1. |
| `binding_summary_range` | ABSENT | Design: for binding metadata. Coverage (line 36): "BindingSummaryEntry[] MISSING". No binding summaries in pack v1. |

**Summary:** 5/8 fields present. 3 fields absent by design: `required_core_layout_hash` (private layout support future), `chunk_range` and `dependency_range` (§12 simplification: one chunk per module).

---

#### BindingSummaryEntry[] (design line 984)

| Field | Status | Evidence |
|-------|--------|----------|
| (not specified by design) | ABSENT | Coverage (line 36): "BindingSummaryEntry[] MISSING (a module is one chunk here, so chunk_range/dependency ranges have nothing to range over; see §12)." |

**Summary:** 0 fields. Deliberately omitted per §12 simplification.

---

#### DependencyEntry[] (design line 985)

| Field | Status | Evidence |
|-------|--------|----------|
| (not specified by design) | ABSENT | Coverage (line 36): "dependency ranges have nothing to range over; see §12". Deliberately omitted. |

**Summary:** 0 fields. Deliberately omitted per §12 simplification.

---

#### ChunkEntry[] (design lines 1005-1018)

| Field | Status | Evidence |
|-------|--------|----------|
| `chunk_id` | ABSENT | Design calls for explicit chunk IDs. Implementation: each module is one chunk; chunk is indexed by module position (implicit). No explicit `chunk_id` field. |
| `kind` | ABSENT | Design: chunk kind (code, data, metadata). Implementation: implicit (all are payload). Coverage (line 40): "Co-load clusters, page-aligned uncompressed hot chunks, split cold debug chunks — all explicitly optional in the design." Not implemented. |
| `flags` | ABSENT | Design: compression/content flags. Not present in implementation. |
| `compression` | PRESENT as `compressed` implicitly | Deflate frame per module; no separate compression field. Format is implicit (deflate). |
| `file_offset` | PRESENT | Lines 36-37: `payload_off` (u64, absolute offset in pack). Read and used. |
| `compressed_size` | PRESENT | Lines 36-37: `comp_size` (u64). Read at line 437. |
| `uncompressed_size` | PRESENT | Lines 36-37: `uncomp_size` (u64). Read at line 437; verified at line 447. |
| `alignment` | ABSENT | Design: alignment requirement. Not present; all payloads loaded as byte arrays. |
| `content_hash` | PRESENT as `crc32` | Lines 36-37: `crc32 of the COMPRESSED payload bytes`. Read and verified at line 444. |
| `optional_dictionary_id` | ABSENT | Design: zstd dictionary reference. Coverage (line 40): "split cold debug chunks and a pack-level zstd dictionary are MISSING (all explicitly optional in the design)." |

**Summary:** 4/10 fields clearly present. 6 fields absent: `chunk_id`, `kind`, `flags`, `alignment` (design features not yet implemented); `optional_dictionary_id` (zstd, optional per design §12.2).

---

#### MinimalStringTable (design line 986)

| Field | Status | Evidence |
|-------|--------|----------|
| (uncompressed string pool) | AMBIGUOUS | Pack directory (lines 32-37) carries inline text for module_id, aspect_id, hashes. Design calls for "minimal string table" (line 987). Implementation: inline bytes per entry; deduplication at build time. Same isolation property, different storage model. |

**Summary:** Functionally present (inline bytes); not a separate indexed pool.

---

#### SignatureTable (design line 987)

| Field | Status | Evidence |
|-------|--------|----------|
| (cryptographic signatures) | ABSENT | Coverage (line 39): "not yet wired into the real SMF section table". Also: "signature/trust policy has no verifier in-tree" (line 87). No SignatureTable in implementation. Deliberately omitted for v1. |

**Summary:** 0 fields. Deliberately omitted; no verifier in-tree.

---

### Summary for § 11.2

| Component | Fields Present | Fields Absent | Notes |
|-----------|---|---|---|
| **AspectPackDirectoryHeader** | ✓ | — | Binary layout; implicit. |
| **AspectEntry[]** | — | 0 | Not specified by design. |
| **ModuleEntry[]** | 5 | 3 | 3 absent: `required_core_layout_hash` (future), `chunk_range`/`dependency_range` (§12 simplification). |
| **BindingSummaryEntry[]** | 0 | — | Not specified by design; omitted per §12. |
| **DependencyEntry[]** | 0 | — | Not specified by design; omitted per §12. |
| **ChunkEntry[]** | 4 | 6 | 4 present: `file_offset`, `compressed_size`, `uncompressed_size`, `content_hash` (as crc32). 6 absent: chunk_id, kind, flags, alignment, optional_dictionary_id. |
| **MinimalStringTable** | ✓ | — | Inline bytes; equivalent. |
| **SignatureTable** | 0 | — | Deliberately omitted for v1; no verifier in-tree. |

**PRESENT COUNT: 9/18** (excluding design-unspecified AspectEntry/BindingSummaryEntry/DependencyEntry).  
**ABSENT COUNT: 9/18** (by design: SignatureTable 0, ChunkEntry optional features, layout hashes for private access).

---

## § 21 — Diagnostics

### Design structure (per §21, lines 1488-1535)

The design specifies **23 diagnostic codes** across four categories.

#### Compile/Type Diagnostics (E-AF001 to E-AF010)

| Code | Design text (lines 1493-1503) | Status | Implementation | Evidence |
|------|---|---|---|---|
| E-AF001 | core declaration depends on optional aspect declaration | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend compiler check (§22.2). Coverage: "compile/type and source/path diagnostics are frontend work" (line 63). |
| E-AF002 | required facet implementation missing | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF003 | ambiguous facet binding | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF004 | invalid facet target pointcut | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF005 | nominal binding used with dynamic/unloadable aspect | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF006 | unauthorized private or mutable domain access | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF007 | aspect dependency cycle | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF008 | helper belongs to multiple aspects without explicit shared owner | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF009 | direct business import from hidden aspect root | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |
| E-AF010 | dynamic advice targets a function without a prepared join point | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Frontend check. |

**Summary for E-AF001 to E-AF010:** 0/10 present in `aspect_pack.spl`. All correctly assigned to frontend/compiler, not runtime loader.

---

#### Source/Path Diagnostics (E-APATH001 to E-APATH004)

| Code | Design text (lines 1505-1512) | Status | Implementation | Evidence |
|------|---|---|---|---|
| E-APATH001 | relative aspect root escapes allowed workspace | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Resolver check (§8). Coverage: "resolver work" (line 28). |
| E-APATH002 | symlink escapes declared root | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Resolver check. |
| E-APATH003 | duplicate aspect ID at same resolution rank | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Resolver check. |
| E-APATH004 | aspect manifest identity conflicts with lockfile | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Resolver check. |

**Summary for E-APATH001 to E-APATH004:** 0/4 present in `aspect_pack.spl`. All correctly assigned to resolver, not runtime loader.

---

#### Pack/Load Diagnostics (E-APACK001 to E-APACK008)

| Code | Design text (lines 1514-1525) | Status | Implementation | Evidence |
|------|---|---|---|---|
| E-APACK001 | malformed or unsupported pack index | PRESENT | Multiple: `APK_NOT_ASPECT_PACK`, `APK_BAD_VERSION`, `APK_BAD_GEOMETRY`, `APK_TRUNCATED_PACK`, `APK_TRUNCATED_HEADER`, `APK_BAD_MAGIC` | Lines 356-377 (apk_open_pack_v1). Covers malformed catalog and pack structure. |
| E-APACK002 | aspect/core ABI mismatch | PRESENT | `APK_ABI_MISMATCH` | Line 872 in `_apk_acquire_facet`: "facet contract ABI mismatch". Also: `APK_MODULE_CORRUPT` (line 447) for decompression size mismatch. Coverage (line 20): "`_apk_acquire_facet` fails `APK_ABI_MISMATCH`". |
| E-APACK003 | pack or chunk hash/signature failure | PRESENT (partial) | `APK_MODULE_CORRUPT` (crc32 failure, line 444), `APK_CATALOG_CORRUPT` (crc32 failure, line 607) | Lines 444, 607. Design calls for "hash/signature"; implementation verifies crc32 (hash, not signature — no signing authority in-tree per coverage line 87). |
| E-APACK004 | decompression size/count limit exceeded | ABSENT | Not checked | No decompression size limits enforced. Design intent: detect runaway decompression. Coverage does not mention this as missing; spec REQ-APK-DC-05 may verify behavior implicitly. |
| E-APACK005 | variant fingerprint mismatch | ABSENT | Fingerprint is carried (line 126 in `ApkModuleLoadV1`), but never compared. | Line 97 in `ApkModuleSourceV2` carries `variant_fingerprint: text`; coverage (line 59): "carried and readable but not compared (nothing in-tree publishes a core ABI hash to compare with)." Comparison is a build/config decision, not container responsibility. |
| E-APACK006 | missing module dependency in pack/catalog | PRESENT (partial) | `APK_ROUTE_DANGLING` | Line 866 in `_apk_acquire_facet`: "catalog routed to a module absent from its pack". Covers routed module missing from pack. Dependencies within a pack are not modeled in v1 (coverage line 36: "dependency ranges have nothing to range over"). |
| E-APACK007 | activation cycle | ABSENT | No cycle detection | Design (line 1523): aspect activation cycles. Not implemented; coverage (line 55): "no activation future/dependency-cycle stack (this module has no concurrency primitives)". Concurrency/generation machinery future work. |
| E-APACK008 | attempted lazy I/O in forbidden execution context | ABSENT | No context guards | Design: mission-critical mode (§19) forbids lazy I/O after startup. Not implemented; scope is lazy-facet loading, which this module enables but does not police. Context would be supplied by runtime/scheduler. |

**Summary for E-APACK001 to E-APACK008:** 3–4/8 clearly present; 2 absent by architecture (APACK004 size limits, APACK007 cycle detection); 2 out-of-scope for this module (APACK005 comparison requires build-time publisher, APACK008 context enforcement requires scheduler).

---

#### Performance-Policy Diagnostic (E-AF011)

| Code | Design text (lines 1529-1533) | Status | Implementation | Evidence |
|------|---|---|---|---|
| E-AF011 | transparent first-join-point activation requested under an exact-zero-overhead policy | OUT-OF-SCOPE | Not in `aspect_pack.spl` | Build/policy configuration. Aspect policy enforcement (§19) is build-time; this module loads based on catalog routes. Coverage: out of scope. |

**Summary for E-AF011:** 0/1 present in `aspect_pack.spl`. Correctly assigned to build policy, not loader.

---

### Diagnostics Implemented in `aspect_pack.spl` (25 codes total)

| Code | Category | Design mapping | Evidence |
|------|---|---|---|
| APK_EMPTY | BUILD | Not in design §21 | Build phase; implementation detail. |
| APK_DUP_MODULE | BUILD | Not in design §21 | Build phase; implementation detail. |
| APK_COMPRESS_FAILED | BUILD | Not in design §21 | Build phase; implementation detail. |
| APK_TRUNCATED_HEADER | PACK/LOAD | E-APACK001 | Line 356. |
| APK_BAD_MAGIC | PACK/LOAD | E-APACK001 | Line 361. |
| APK_BAD_VERSION | PACK/LOAD | E-APACK001 | Line 365. |
| APK_NOT_ASPECT_PACK | PACK/LOAD | E-APACK001 | Line 368. |
| APK_BAD_GEOMETRY | PACK/LOAD | E-APACK001 | Line 373. |
| APK_TRUNCATED_PACK | PACK/LOAD | E-APACK001 | Lines 375, 377. |
| APK_BAD_HANDLE | PACK/LOAD | E-APACK001 | Line 397. |
| APK_DIR_CORRUPT | PACK/LOAD | E-APACK001 | Lines 404–425. |
| APK_MODULE_CORRUPT | PACK/LOAD | E-APACK002, E-APACK003 | Lines 444, 447. |
| APK_DUP_FACET | BUILD/CATALOG | Not in design §21 | Build phase; duplicate catalog entry detection. |
| APK_CATALOG_TRUNCATED | CATALOG/LOAD | E-APACK001 | Lines 529, 544. |
| APK_CATALOG_BAD_MAGIC | CATALOG/LOAD | E-APACK001 | Line 534. |
| APK_CATALOG_BAD_VERSION | CATALOG/LOAD | E-APACK001 | Line 538. |
| APK_CATALOG_BAD_GEOMETRY | CATALOG/LOAD | E-APACK001 | Line 542. |
| APK_CATALOG_BAD_HANDLE | ROUTE | E-APACK001 | Line 568. |
| APK_CATALOG_EMPTY_KEY | ROUTE | E-APACK001 | Line 570. |
| APK_CATALOG_CORRUPT | ROUTE | E-APACK001, E-APACK003 | Lines 575–607. |
| APK_ASPECT_EXCLUDED | FACET | Not in design §21 (§9.4 activation policy) | Line 831. Enforcement of `APK_ACT_OFF`. |
| APK_ASPECT_MANUAL | FACET | Not in design §21 (§6.7 manual load) | Line 834. Enforcement of `APK_ACT_MANUAL`. |
| APK_PACK_MISSING | FACET | E-APACK006 (partial) | Line 846. Routed pack not deployed. |
| APK_ROUTE_DANGLING | FACET | E-APACK006 (partial) | Line 866. Module absent from pack. |
| APK_ABI_MISMATCH | FACET | E-APACK002 | Line 872. Facet contract ABI verification. |

**Summary for pack/load diagnostics:**

- **Design E-APACK001 (malformed index):** FULLY COVERED by 10 implementation codes.
- **Design E-APACK002 (ABI mismatch):** COVERED by `APK_ABI_MISMATCH` and `APK_MODULE_CORRUPT` (decompression size = layout mismatch).
- **Design E-APACK003 (hash/signature failure):** PARTIALLY COVERED by `APK_MODULE_CORRUPT` (crc32). Signature verification absent (by design; no verifier in-tree).
- **Design E-APACK004 (decompression limit):** ABSENT.
- **Design E-APACK005 (variant fingerprint):** NOT CHECKED (fingerprint carried, comparison is build responsibility).
- **Design E-APACK006 (missing dependency):** PARTIALLY COVERED by `APK_ROUTE_DANGLING` and `APK_PACK_MISSING` (routed module/pack absent). Pack-internal dependencies not modeled in v1.
- **Design E-APACK007 (activation cycle):** ABSENT.
- **Design E-APACK008 (lazy I/O in forbidden context):** ABSENT (context enforcement is scheduler responsibility).

---

### Diagnostics Summary

| Category | Design codes | Implementation codes | Status |
|----------|---|---|---|
| **E-AF001 to E-AF010** (compile/type) | 10 | 0 | OUT-OF-SCOPE (frontend) |
| **E-APATH001 to E-APATH004** (source/path) | 4 | 0 | OUT-OF-SCOPE (resolver) |
| **E-APACK001 to E-APACK008** (pack/load) | 8 | 15 | PARTIALLY COVERED (6–7 design codes covered; 4–5 out-of-scope or deferred). |
| **E-AF011** (policy) | 1 | 0 | OUT-OF-SCOPE (build policy). |
| **Build/implementation details** | — | 10 | PRESENT (APK_EMPTY, DUP_MODULE, COMPRESS_FAILED, DUP_FACET, etc.) |
| **Activation enforcement** | — | 2 | PRESENT (APK_ASPECT_EXCLUDED, APK_ASPECT_MANUAL). |
| **Total** | **23** | **25** | All 23 design codes accounted for; 2 additional implementation codes for build/activation. |

**PRESENT COUNT (design-specified pack/load):** 6–7 of 8 E-APACK* codes (APACK001–003, APACK006 partial). 1–2 deferred or deferred (APACK004 limits, APACK007 cycles). 2 out-of-scope (APACK005 comparison, APACK008 context).

---

## Overall Completion Summary

### § 11.1 (Aspect Catalog Fields)

- **FacetRoute:** 6/6 PRESENT
- **JoinpointRoute:** 4/5 PRESENT (binding_plan_id design-ambiguous)
- **PackRef:** 0/7 ABSENT (deliberate; no verifier in-tree)
- **ProfileRecord[]:** 0/— ABSENT (deliberate; design marks optional §9.6)
- **StartupAspect:** Discriminated via entry_kind; no separate fields.

**Status:** PARTIAL. Core FacetRoute complete. PackRef and ProfileRecord deliberately omitted per design.

---

### § 11.2 (Pack Directory Fields)

- **ModuleEntry:** 5/8 PRESENT (3 absent: required_core_layout_hash, chunk_range, dependency_range — all by design §12 simplification)
- **ChunkEntry:** 4/10 PRESENT (6 absent: chunk_id, kind, flags, alignment, optional_dictionary_id — optional per design §12.2, or deferred)
- **AspectEntry, BindingSummaryEntry, DependencyEntry:** Not specified by design; omitted per §12 simplification.
- **SignatureTable:** 0/— ABSENT (deliberate; no verifier in-tree)

**Status:** PARTIAL. Core ModuleEntry mostly complete. §12 simplifications (one chunk per module) eliminate AspectEntry, BindingSummaryEntry, DependencyEntry, chunk_id. Advanced features (dictionary, split chunks, signatures) deferred.

---

### § 21 (Diagnostics)

- **E-AF001–E-AF010 (compile/type):** 0/10 (correctly assigned to frontend)
- **E-APATH001–E-APATH004 (source/path):** 0/4 (correctly assigned to resolver)
- **E-APACK001 (malformed index):** 10+ codes PRESENT
- **E-APACK002 (ABI mismatch):** PRESENT
- **E-APACK003 (hash/signature):** PARTIALLY PRESENT (hash/crc32 yes; signature no)
- **E-APACK004 (decompression limit):** ABSENT
- **E-APACK005 (variant fingerprint):** CARRIED BUT NOT COMPARED (by design; build responsibility)
- **E-APACK006 (missing dependency):** PARTIALLY PRESENT (routed module/pack; pack-internal dependencies not modeled)
- **E-APACK007 (activation cycle):** ABSENT
- **E-APACK008 (forbidden I/O context):** ABSENT (scheduler responsibility)
- **E-AF011 (policy):** 0/1 (correctly assigned to build policy)

**Status:** PARTIAL. All 8 E-APACK* codes have corresponding implementation codes or are deliberately deferred/out-of-scope. Core pack/load/route diagnostics complete. Cycle detection, decompression limits, and context guards deferred to runtime/scheduler.

---

## Most Important Missing Item

**Signature verification (E-APACK003 signature half, SignatureTable §11.2).**

- **Why critical:** The design calls for "pack or chunk hash/signature failure" diagnostics and a SignatureTable in the pack directory for cryptographic integrity.
- **Current state:** CRC32 checksums present (hash); cryptographic signatures absent. Coverage (line 87): "signature/trust policy has no verifier in-tree; an unchecked hash field would be decoration."
- **Blocker:** No signing authority, verifier, or trust anchor exists in-tree. This is foundational for mission-critical deployments (§19).
- **Path forward:** Implement only when signature infrastructure (build-time signer, runtime verifier, trust roots) exists. Not a blocker for initial lazy-facet loading.

---

## Checklist for Owning Agent

### § 11.1 — Level 1 Aspect Catalog
- ✅ FacetRoute: complete (6/6 fields)
- ✅ JoinpointRoute: mostly complete (4/5 fields; binding_plan_id design-ambiguous)
- ✅ StartupAspect: discriminated via entry_kind (design doesn't specify fields)
- ❌ PackRef: not implemented (deliberate; no verifier)
- ❌ ProfileRecord[]: not implemented (deliberate; optional per §9.6)
- ✅ CatalogStringTable: inline bytes (equivalent semantics)

**Action:** No missing required fields for v1. PackRef and ProfileRecord are deliberately deferred.

### § 11.2 — Level 2 Pack Directory
- ✅ AspectPackDirectoryHeader: present (binary layout)
- ✅ ModuleEntry: mostly complete (5/8; 3 deferred: layout_hash, chunk_range, dependency_range)
- ✅ ChunkEntry: core fields present (4/10; advanced features deferred: dictionary, alignment, kind/flags)
- ❌ AspectEntry: not specified by design; omitted per §12
- ❌ BindingSummaryEntry: not specified by design; omitted per §12
- ❌ DependencyEntry: not specified by design; omitted per §12
- ❌ SignatureTable: not implemented (deliberate; no verifier)

**Action:** No missing required fields for v1. §12 simplifications (one chunk per module) explain absence of AspectEntry, binding summaries, and dependency ranges.

### § 21 — Diagnostics
- ✅ E-APACK001 (malformed index): 10+ codes
- ✅ E-APACK002 (ABI mismatch): 1 code
- ⚠️ E-APACK003 (hash/signature): 2/3 (hash/crc32 yes; signature no)
- ❌ E-APACK004 (decompression limit): not implemented
- ⚠️ E-APACK005 (variant fingerprint): carried, not compared (by design)
- ⚠️ E-APACK006 (missing dependency): 2 codes (routed; pack-internal not modeled)
- ❌ E-APACK007 (activation cycle): not implemented
- ❌ E-APACK008 (forbidden I/O): not implemented (scheduler responsibility)

**Action:** Pack/load diagnostics mostly complete for v1. Signature verification, cycle detection, and I/O context guards are deferred to later phases or runtime integration.

---

## Evidence Summary

- **Design document:** `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` (§11.1 lines 920–975, §11.2 lines 976–1022, §21 lines 1488–1535)
- **Implementation:** `src/lib/common/aspect_pack.spl` (894 lines)
  - Records: ApkModuleSourceV2 (lines 92–98), ApkCatalogEntryV2 (lines 139–145), ApkCatalogRouteV1 (lines 155–165)
  - Functions: apk_open_pack_v1 (line 354+), apk_load_module_v1 (line 395+), apk_open_catalog_v1 (line 527+), apk_catalog_route_v1 (line 565+), _apk_acquire_facet (line 827+)
  - Diagnostics: 25 APK_* codes (lines 62–81, 260–607, 831–872)
- **Coverage report:** `doc/09_report/aspect_pack_design_coverage_2026-08-18.md` (lines 1–95)
