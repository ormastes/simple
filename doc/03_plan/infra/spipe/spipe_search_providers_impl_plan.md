# SPipe Search Providers — Implementation Plan (pure Simple)

**Date:** 2026-08-31
**Design:** `doc/05_design/infra/spipe/spipe_knowledge_compiler_search_providers.md` (2455 lines)
**Precedent:** `doc/03_plan/infra/spipe/spipe_knowledge_compiler_refined_plan.md` (slice 1, landed 2026-08-31)
**Status:** plan only — no code written by this document.

Section references like §14.10 are to the DESIGN. This plan does not restate
design schemas except where it is itself the freeze (§5 below). When this plan
and the design disagree on a schema, the design wins; when they disagree on
what EXISTS on disk, this plan wins (it was measured 2026-08-31).

---

## 1. GROUND TRUTH (measured 2026-08-31)

The design's §15 "implementation evidence checkpoint" is **badly stale**. It says
the analyzer candidate is `FAIL` with admissible files `[]`, the Unicode-17
prerequisite is "absent on `main`", and only `ranking.spl` was accepted. All
three statements are false against the current tree. Far more is landed than the
design believes — and some of what is landed is exactly the code §15 rejected.

### 1.1 `src/lib/common/search/` — 3798 lines, 19 modules

| Module | Lines | State |
|---|---:|---|
| `ranking.spl` | 714 | **REAL.** Full §14.10 chain: `_bm25_term_trace_checked` (ratio L317, norm L322, denom L328, tf_scaled L333, unweighted L339, weighted L342), `_idf_fixed_checked` L247, `internal_total` L464/481, `public_score_milli` L485. `fixed_ln_checked` L198 = 7-term atanh (3→13 step 2), `LN2_FIXED=693147` L40, `SCALE=1000000` L36. Weights 4000/4000/2500/2000/1000 at L411-419; `_bm25_field_ordinal` L397 = the five closed field names. **No i128** (L23: "This runtime has no i128") — checked i64 via `_checked_mul_nonnegative`/`_checked_add_i64`/`_checked_div_nonnegative`. This is the slice accepted at `2b9f25f8604`. |
| `generated/unicode_17_0_0.spl` | 230 | **REAL generated UCD 17.0.0 tables** (~112 KB; alphabetic/decimal/mark/cased/case-ignorable ranges, CCC, decomposition, composition, lowercase + conditional lowercase). Exports `unicode_normalize_nfc`, `unicode_default_lowercase`, `unicode_is_token_code_point`, `unicode_table_version`, `unicode_table_generator_sha256`. |
| `analyzer.spl` | 106 | **FACADE, contract-thin.** Genuinely routes through UCD 17 (imports L2, used L55/L82/L91) and iterates `text_codepoints` (L83) — no byte/char bug. Stop set at L77 is exactly `[a,an,and,of,the,to]`. But it exposes `analyze_text -> [text]` / `analyze_positioned -> [AnalyzedToken]`: **bare arrays, no limits, no `Result`**. |
| `document.spl` | 108 | `SearchDocumentV1`, `SearchScopeV1` (10 fields), `ScopedFieldV1`, `ScopedFacetV1`, `ScopedSearchDocumentV1` all present. `SearchHit` is `{document_id, score, rank}` — **no `source_rank`, no `matched_fields`** (§14.12 `SearchHitV1`). |
| `explain.spl` | 43 | `SearchExplanationV1`/`FieldExplanationV1` present WITH decimal-string intermediates (`average_length_scaled: text`, `field_total: text`, `internal_total: text`), `tie_key_utf8_hex`. **`TermContributionV1` absent** — no per-term breakdown, so §14.14 recomputability cannot be checked. |
| `snapshot.spl` | 132 | Has `IndexOperationV1`, `IndexApplyRequestV1`, `IndexCandidateV1`, `IndexPublishRequestV1`, `IndexPublishResultV1`, `OperationReceiptV1`, `ReplayRecordV1`. **Missing `CandidateRecordV1`, `PublicationRecordV1`, `DurableTerminalErrorV1`, `CandidateExpiryReceiptV1`, `QueryReceiptV1`** (§14.16/§14.17). |
| `provider.spl` | 51 | `trait LexicalSearchPort` (4 methods — narrower than §3.6: no `create`/`seal`/`explain`/`stats`), `trait SearchProvider` (10 methods, close to §4.3), `SearchCapabilities`, `SearchStatsV1`, `CancelResultV1`, `ShutdownResultV1`. |
| `query.spl` / `top_k.spl` / `corpus_stats.spl` | 50/55/33 | `SearchQueryV1`, `EqualityFilterV1`, `SearchPageV1{logical_root,hits,next_cursor,exhausted}`, `TermCorpusStat`, `CorpusStats`. **No per-field `FieldStatsV1`.** `text_top_k` is a scorer-agnostic ordering helper, not the §3.1 exhaustive oracle. |
| `inverted_index.spl` | 261 | Pre-existing append-only positional index (`IndexedDoc`, `InvertedIndex`). Design §3.1 says keep it and do not weaken its strictly-increasing-ID invariant. |
| `exact/multi/prefilter/simd_scan/roaring/ann/types` | 1787 | Pre-existing Phase-1/2 assets, unrelated to this slice except `types.spl`'s `Score`/`PostingList`/`Embedding`. |

**Genuinely absent modules from §3.1:** `segment.spl`, `fingerprint.spl`,
`similarity.spl`, `candidate_bucket.spl`, `semantic_provider.spl`, `wand.spl`,
`block_max_wand.spl`.

**Existing specs** (`test/01_unit/lib/common/search/`): `ranking_spec.spl` (508),
`unicode_17_0_0_spec.spl` (154), `analyzer_contract_spec.spl` (56),
`explain_contract` (46), `document_contract` (26), `snapshot_contract` (31),
`provider_contract` (14), `top_k_contract` (11), `knowledge_contract` (88), plus
the Phase-1/2 suites. The `*_contract` specs at 11–46 lines are shape assertions,
not oracles.

### 1.2 `src/app/spipe_knowledge_provider/` — 39 files, ~9,700 lines. Mostly REAL.

The design (§4, §12 stage 7) treats the provider executable as future work. It is
largely built:

- **Framing (§14.5):** `frame_encoder.spl:14/19` emits 8 lowercase hex nibbles;
  `protocol.spl:26/38/47`; `frame_decoder.spl:48 ProviderFrameDecoderV1`;
  `main.spl:107` enforces `header.len()==8` and the 1 MiB cap.
- **Canonical JSON (§14.9):** `canonical_json_decoder.spl:84` — NFC enforced
  (`:328`, rejects non-NFC strings), keys must be **strictly** UTF-8-increasing
  (`:24/:332`, which rejects duplicates and misordering in one test), safe-integer
  bound `:13`. Emitter `canonical_json_emitter.spl:159`.
- **Dispatch (§4.3):** `wire_dispatch.spl:70` routes all eleven operations
  including `duplicate_candidates` and `symbols_snapshot`. Capabilities at
  `wire_core.spl:209` advertise `duplicate:false, symbols:false, phrase:false,
  regex:false, wildcard:false, semantic:false` — and **`cancel:false`**, which
  contradicts §14.20's `cancel:true`.
- **Real scoring:** `lexical.spl:4` imports `std.common.search.ranking.
  {bm25_term_checked_trace}`, used at `:195` (score) and `:481` (explain), emitting
  `bm25-fixed-v1` / `public_score_milli` (`:495`). Not a stub.
- **Receipts:** real Ed25519 — `lifecycle.spl:3` imports
  `std.common.crypto.ed25519`; `lifecycle.spl:539 PureEd25519ReceiptAuthorityV1`
  (sign `:564`, verify `:577`, `key_id = "ed25519:"+sha256(pubkey)`). But the
  local class is `OperationReceiptBindingV1` (`lifecycle.spl:347`) — **no symbol
  named `OperationReceiptV1` or `QueryReceiptV1` exists in that package**, so the
  provider's receipt shape is not the frozen wire record.
- **Host loop:** `main.spl:127 provider_host_entry` — real `Stdin`/`Stdout`,
  `read_exact(8)` + `read_exact(len)`, dispatch, write, flush.
- Durability/lifecycle: `durable_records.spl` (723), `lifecycle.spl` (763),
  `service.spl` (798), `wire_core.spl` (770), `wire_query.spl` (680),
  `request_control.spl`, `service_deadline.spl`, `generation_quarantine.spl`.

### 1.3 The frozen JS package — `examples/05_stdlib/spipe/`

- `src/provider/js_fixed_point.js:9 JsFixedPointSearchProvider` — exists.
- `src/provider/adapter.js:4 InProcessSearchProviderAdapter` — exists **in JS only**.
- `src/index/{analyzer,bm25,contracts,document,exact,fusion,logical_index,unicode_17}.js` —
  the fusion + exact-identity logic exists **only here**.
- `src/search/generated/unicode_17_0_0.js` — present.
- `tools/unicode/generate_unicode_tables.mjs` + `UNICODE-LICENSE.txt` + all seven
  UCD 17.0.0 source files — present. **The §15.3 "14-file Unicode bundle" is
  complete on disk.**
- `test/fixture/wave4_search/` — 13 fixtures present, including
  `provider_protocol_vectors.json` (4905 B), `golden_corpus.json`,
  `golden_results.json`, `fusion_results.json`, `bm25_intermediates.json`,
  `canonical_json_vectors.json`, `unicode_17_0_0_manifest.json`,
  `authorization_scope_vectors.json`, `operation_receipt_vector.json`.
- **Absent anywhere in the repo:** `benchmark_operation_plan_v1.json`,
  `qualified_search_profile_v1.json`, `measure_qualified_search.mjs` (§14.6).

### 1.4 Database adapters

| Target | State |
|---|---|
| DBFS `src/lib/nogc_sync_mut/db/dbfs_engine/fts/` | 8 files (1050 lines). `bm25.spl:9` imports `std.common.search.ranking.{bm25_score_default}`, but also carries a **local `fts_bm25_score_fixed` (`bm25.spl:26`)** — a second scoring path, integer not f64. `wave4_compatibility.spl` (227) is the bundle §15.1 rejected as "a duplicate fixture scorer rather than a facade": it is still on disk. `inverted_index.spl:44 me fn index_document`, `:119 me fn contains_document`, `:125 me fn doc_length`. |
| PureDatabase `.../pure_sql/_PureDatabase/` | `row_value_helpers.spl:763 fn _bm25_score(...) -> f64` — **the f64 duplicate the design orders removed**, called at `:794`. `pure_database.spl:1587 bm25_search`, `:1590 fts5_search`. Cache key at `pure_database.spl:1464`: `table + "\|" + query + "\|" + limit` — exactly the insufficient key §5.1 names. |
| Textual DB `src/lib/nogc_sync_mut/database/fts.spl` | 124 lines, trigram-overlap only (`fts_build:38`, `fts_search:58`, `fts_update:104`). **No BM25, and no `contains_fuzzy`** — the design's claim that the trigram index "remains `contains_fuzzy`" names a function that does not exist. |
| DB server `src/lib/nogc_sync_mut/database/server/` | **Zero occurrences of "search"** across all 7 files. No `SearchCapsule`. |
| duplicate_check `src/compiler/90.tools/duplicate_check/` | 20 files. Has `SimpleToken`/`tokenize` (`tokenizer.spl:6/15/50`), `DuplicationConfig` (`config.spl:7`), cosine (`features.spl:57`, `math_utils.spl:12/33`), `extract_token_frequencies` (`features.spl:17`). **No minhash, no simhash, no shingle anywhere** — those §7 primitives must be written, not extracted. |

### 1.5 Slice-1 SPipe code (`src/app/spipe/`, 2033 lines)

`model/types.spl` (frozen records), `model/canonical.spl` (the ONE slice-1
canonical encoder: `CanonicalValue{CText,CInt,CList,CDict}`, byte-sorted keys via
`_key_less` on `.bytes()`), `model/uid.spl`, `model/edge.spl`, `scan/`,
`graph/reverse_index.spl`, `refactor/`, `balance/`, `diagnostics/`,
`admission/verdict.spl`, `main.spl`. 73/73 specs green.

**No fusion, no identity registry, no search anything.** `rrf`, `rrf-fixed-v1`,
`FusionExplanation`, `IdentityExplanation` have zero `.spl` hits repo-wide;
`match_tier` / `exact_identity` appear only as strings in
`spipe_knowledge_provider/{response_plan,wire_query}.spl`.

---

## 2. CORRECTIONS to the design

1. **§15.2 / §15.3 are stale.** The Unicode 17 bundle is complete on disk and the
   analyzer imports it. Do NOT re-derive UCD tables. The remaining Unicode work is
   the §15.3 static defects (spec calling `rt_file_read_text` directly instead of a
   facade; orphaned `REQ-SPK-SEARCH-UNICODE-001`; wrong license path in the
   generated JS; weak `Case_Ignorable` final-sigma matrix) plus a real Simple
   parity run — repair, not regeneration.

2. **"Analyzer FAIL, admissible `[]`" is not the current state.** `analyzer.spl`
   is landed and correct in its algorithm. What is missing is the §15.2 *seam*:
   `analyze_field_v1`, `analyze_query_v1`, `AnalyzedTextV1`, `AnalyzedQueryV1`,
   `AnalyzerLimitsV1`, `AnalyzerIdentityV1`, `AnalyzerErrorV1`,
   `SearchFieldIdentityV1`, `unsigned_utf8_less` — **zero hits repo-wide**. Treat
   this as "add the bounded `Result` seam over a working algorithm", not a rewrite.

3. **The provider executable is ~80% built, not future work.** §12 stage 7 and §4
   read as greenfield. Framing, canonical JSON, dispatch, BM25, Ed25519 receipts,
   and the stdio host loop all exist (§1.2). Plan the provider lane as *gap
   closure and conformance*, not construction.

4. **§14.20 vs. reality: `cancel`.** §14.20 freezes `ProviderCapabilitiesV1.cancel:true`;
   `wire_core.spl:209` advertises `cancel:false`. One of them must move. The design
   is normative → the provider lane fixes the advertisement and must make
   §14.19's `pending -> cancelled` CAS real, or file the divergence.

5. **Receipt records are named differently in the provider.** `OperationReceiptV1`
   exists in `src/lib/common/search/snapshot.spl` but the provider signs
   `OperationReceiptBindingV1`. `QueryReceiptV1` exists nowhere. Both wire records
   must land once, in `std.common.search`, and the provider must adopt them —
   otherwise there are two receipt shapes and §14.16 byte-exact echo validation
   cannot hold.

6. **§7 "extract only pure reusable facilities" over-promises.** MinHash, SimHash,
   and shingling do not exist in `duplicate_check` (§1.4). They are new code in
   `common/search`, and the "old CLI results remain equivalent" gate applies to the
   cosine/token-frequency path that *is* being extracted, not to new fingerprints.

7. **`contains_fuzzy` does not exist** (§6.3). The textual DB's trigram API is
   `fts_build`/`fts_search`/`fts_update`. Read §6.3 as "do not change `fts_search`
   semantics; add `search_lexical` alongside".

8. **`i128` is not available.** §14.10 says intermediates are conceptually i128 and
   an implementation without it must prove i64 identity per operation.
   `ranking.spl` already does exactly this (L23 comment + the `_checked_*` family).
   That is the pattern; no lane may introduce a fake i128.

9. **Slice-1 `model/canonical.spl` is NOT `spipe-canonical-json-v1`.** It has no
   NFC key normalization, no duplicate-key rejection, and no schema integer
   bounds. It must never be used for logical roots, payload hashes, or receipt
   preimages. §14.9 hashing is owned by the provider's
   `canonical_json_emitter`/`_decoder` pair (which does enforce all three), lifted
   into a shared module by Package 0. Slice 1 just finished collapsing two
   canonical encoders into one (refined plan §8.1); do not create a third.

10. **The design's Wave-4 evidence bar cannot be met on this host.** §14.6.2 says
    W4-SRCH-09 is `NOT EVIDENCE` until an admitted Stage 4 binary exists, and
    `.claude/rules/vcs.md` records all four tracked stage binaries currently SEGV.
    The perf harness is in scope to BUILD; a PASS verdict on it is not achievable
    in this slice and must not be claimed.

---

## 3. SCOPE — sequenced, not cut

The goal is "implement fully". Nothing the design mandates for Wave 4 is dropped.
What follows is the design's OWN deferral structure, made explicit.

### 3.1 IN — must exist for the contract to hold

- §15.2 analyzer seam (bounded, `Result`-returning, identity-bearing).
- §14.3/§14.10 checked BM25 — already landed; extended with per-field statistics
  and the §14.14 `TermContributionV1` explanation records so explanations recompute.
- §14.4 logical root + `IndexDeltaV1`; §3.6 index semantics (idempotent
  add/replace/delete, seal, snapshot, exhaustive `query`, `explain`, `stats`).
- §3.1 `segment.spl` + `snapshot.spl` completion: `CandidateRecordV1`,
  `PublicationRecordV1`, `DurableTerminalErrorV1`, `CandidateExpiryReceiptV1`,
  `QueryReceiptV1`; §14.17 candidate lifecycle; §14.19 cancel/deadline/shutdown.
- §3.5 `rrf-fixed-v1` fusion **and** the exact-identity dominance tier — in Simple,
  under `src/app/spipe/`. Currently JS-only.
- §14.8 `SearchScopeV1` authorization partitioning and `scope_digest` binding
  (behavior owned by **P2** — `scope_digest` inside the logical root, statistics
  computed solely from authorized documents/fields, redaction removing a field
  before analysis; cross-scope fixture assertions owned by **P11** against
  `wave4_search/authorization_scope_vectors.json`).
- §14.9 canonical JSON as a shared module with golden byte vectors.
- The `SearchProviderAdapter` role in Simple:
  `InProcessSearchProviderAdapter` + `ProcessSearchProviderAdapter`, §14.5 state
  machine, response distrust validation (§4.3), single fallback with root parity.
- §4.1 provider launch hardening (allowlist, digest, canonical non-symlink path,
  no shell, minimal env, process group, bounded stderr ring).
- §6.1–§6.3 DBFS / PureDatabase / textual-DB adapters and facades.
- §7 duplicate primitives (`fingerprint.spl`, `similarity.spl`,
  `candidate_bucket.spl`) with pinned CLI parity.
- §10.1–§10.4 golden conformance across every implementation, driven by the
  already-checked-in `wave4_search` fixtures.
- §14.6 perf harness *artifacts* (profile, operation plan, collector, journal
  schema) — built, wired, and honestly reported as `NOT EVIDENCE` per §14.6.2.

### 3.2 DEFERRED — the design defers these itself

| Deferred | Design's own justification |
|---|---|
| WAND, Block-Max WAND | §1: "later execution strategies that must produce the same ordered top-k result as the exhaustive oracle"; §12 stage 9 "one at a time… exact exhaustive parity plus measured benefit". `wand.spl`/`block_max_wand.spl` stay unwritten until the oracle is green. |
| ANN / semantic source / sharding | §1 and §12 stage 9, same clause. §3.5: "`semantic` may be absent." |
| `duplicate_candidates` wire success | §14.12: "no Wave 4 success schema; capability is false and the bound response is `unsupported_capability`". The operation stays in the closed vocabulary returning that bound error. The §7 *library primitives* remain in scope (P10) — only the wire success schema is not. |
| §8 source-symbol provider, **entirely** | Same §14.12 clause for `symbols_snapshot`, plus §14.20's frozen `ProviderCapabilitiesV1.symbols:false`. With no Wave-4 success schema and the capability frozen false, the export record has no consumer this slice. Deferred whole — no package owns it, and none should invent one. Revisit when a wave admits `symbols:true`. |
| Database-server search / `SearchCapsule` | §6.4 + §12: only after capability, snapshot, durability, cancellation and bounded-result contracts exist; §12 assigns it stage 8, and §12's closing paragraph puts server execution strategies in research-plan Wave 10. |
| Phrase / regex / wildcard queries | §14.2: "Phrase evaluation is not implemented or advertised… Later phrase support requires a new query/analyzer contract." |
| A PASS on W4-SRCH-09 | §14.6.2: impossible without an admitted Stage 4 executable. |
| Tier variants (async/GC) of the textual DB | §6.3: "Do not hand-copy behavior into async/GC tiers without the canonical facade strategy." |

---

## 4. PARALLELIZATION MAP

**The binding lesson from slice 1 (refined plan §8.2):** *"The day-one-types
sequencing partly failed… Overlapping the model package with its dependents does
not work. Next slice: land the model package alone, confirm it on disk, then fan
out."* One package (S1-B) designed around absent types and never imported them.

So: **Package 0 lands ALONE and is confirmed green on disk before any other
package starts.** No exceptions, no "start against the spec text in parallel".

Merge-owned shared files, each owned by exactly one package:
`src/lib/common/search/__init__.spl` → **P0 only**.
`src/lib/common/search/ranking.spl` → **P0 only** (it is the accepted
`2b9f25f8604` slice; other lanes request changes, they do not edit it).
No other file appears in two packages.

### Package 0 — Frozen types and contracts (SOLO, blocking)

Owns:
- `src/lib/common/search/analyzer_contract.spl` *(new — §5.1 seam types only, no algorithm)*
- `src/lib/common/search/document.spl` *(extend: `SearchHitV1`)*
- `src/lib/common/search/explain.spl` *(extend: `TermContributionV1`)*
- `src/lib/common/search/corpus_stats.spl` *(extend: `FieldStatsV1`)*
- `src/lib/common/search/snapshot.spl` *(extend: the 5 missing records)*
- `src/lib/common/search/provider.spl` *(widen `LexicalSearchPort` to §3.6 — see the implementer check below)*
- `src/lib/common/search/fusion_types.spl` *(new — §5.2/§5.5)*
- `src/lib/common/search/canonical_json.spl` *(new — §14.9 shared encoder seam)*
- `src/lib/common/search/__init__.spl` *(exports)*
- `test/01_unit/lib/common/search/frozen_contract_v2_spec.spl`

Contract: declarations only — structs, enums, trait signatures, contract-ID
constants. **Zero algorithm.** Every §5 type below appears here verbatim.
`canonical_json.spl` is a thin re-export/seam over the provider's
`canonical_json_emitter`/`_decoder` (§1.2) — it must NOT reimplement, and must NOT
delegate to `src/app/spipe/model/canonical.spl` (correction §2.9).

**Trait-widening check (do this first).** Widening `LexicalSearchPort` from 4 to
the §3.6 surface is a breaking signature change for any implementer, and P0 owns
none of the files an implementer would live in. Measured 2026-08-31:
`/usr/bin/grep -rn "LexicalSearchPort" src/ --include=*.spl` returns **only the
declaration in `provider.spl`** — zero implementers — so widening in place is
safe. Re-run that grep before editing; if it returns any implementer, do NOT
widen in place: land the §3.6 surface as an additive second trait (P2 composes
it) and record the divergence in §7. The same rule applies to adding fields to
`SearchCapabilities`.

Acceptance: `bin/simple test test/01_unit/lib/common/search/frozen_contract_v2_spec.spl`
green, **and** every existing spec in `test/01_unit/lib/common/search/` still green.

**Gate before fan-out:** P0's files exist on disk, the command above passes, and a
grep confirms zero re-declaration of any P0 type outside P0's files.

---

Packages 1–8 start together, only after the P0 gate.

### P1 — Analyzer seam (`spipe-unicode-lex-v1`)
Owns `src/lib/common/search/analyzer.spl`,
`test/01_unit/lib/common/search/analyzer_contract_spec.spl`,
`test/01_unit/lib/common/search/analyzer_limits_spec.spl` (new).
Contract: implement `analyze_field_v1`/`analyze_query_v1`/`unsigned_utf8_less`
over the existing UCD-17 algorithm; enforce §15.2 limits
(`AnalyzerLimitsV1(4096,4096,4096,128,128)` for queries; 1,048,576-byte field
ceiling, ≤524,288 tokens); positions one-based assigned BEFORE stop-word removal;
`Identifier` appends the untrimmed normalized value at position zero, deduplicated;
stop-word SHA-256 `6f0a7c26…10bf` asserted, not assumed. Keep `analyze_text`/
`analyze_positioned` as compatibility wrappers (`lexical.spl` and DBFS import them).
Byte-for-byte parity against `examples/05_stdlib/spipe/test/fixture/wave4_search/unicode_golden_outputs.json`.
Accept: `bin/simple test test/01_unit/lib/common/search/analyzer_contract_spec.spl test/01_unit/lib/common/search/analyzer_limits_spec.spl`

### P2 — Common index, segments, snapshot lifecycle
Owns `src/lib/common/search/segment.spl` (new), `.../index_engine.spl` (new),
`.../top_k.spl` (extend: exhaustive oracle), `.../candidate_lifecycle.spl` (new),
`test/01_unit/lib/common/search/index_engine_spec.spl`,
`.../snapshot_lifecycle_spec.spl`.
Contract: §3.6 + §14.4 + §14.17. Idempotent `replace` by `(id, revision)`; delete
of absent ID is a no-op; §14.12's null/null vs non-null/non-null delete
precondition tagged choice; logical root = sha256 of canonical JSON over
`ScopedSearchDocumentV1` sorted by unsigned UTF-8 ID; clean rebuild ≡ every
equivalent delta history. Exhaustive top-k is the oracle every later strategy
must match.
Accept: `bin/simple test test/01_unit/lib/common/search/index_engine_spec.spl test/01_unit/lib/common/search/snapshot_lifecycle_spec.spl`

### P3 — Explanation completion + per-field statistics
Owns `src/lib/common/search/explain_build.spl` (new),
`.../field_stats.spl` (new),
`test/01_unit/lib/common/search/explain_recompute_spec.spl`.
Contract: §14.14. Build `TermContributionV1` records from
`Bm25TermTrace` (already produced by `bm25_term_checked_trace`), absent-term
records carrying the exact zeros/nulls, terms in ascending UTF-8 order, fields in
canonical authorized order. The spec must **recompute** each explanation back to
the returned `public_score_milli` and compare `tie_key_utf8_hex` to the hex of the
document ID. Validate against `wave4_search/bm25_intermediates.json`.
Accept: `bin/simple test test/01_unit/lib/common/search/explain_recompute_spec.spl`

### P4 — RRF fusion + exact-identity dominance (SPipe-owned)
Owns `src/app/spipe/fusion/rrf.spl`, `.../fusion/adjustments.spl`,
`.../fusion/explanation.spl`, `src/app/spipe/identity/registry.spl`,
`.../identity/resolve.spl`, `test/01_unit/app/spipe/fusion_rrf_spec.spl`,
`.../identity_dominance_spec.spl`.
Contract: §3.5. Fixed-point `1/(k+rank)`, `k=60` default, `k ∈ [1,10000]`,
`source_k` default/max 1000, sources `lexical, graph, semantic`, duplicate source
IDs rejected. Identity tier is **outside** RRF: `resolve(value)` short-circuits
with no provider call; `search(query)` pins one unambiguous authorized match at
final rank 1, removes its ID from every source list, and fused ranks begin at 2.
The pinned artifact gets `IdentityExplanation`, never `FusionExplanation`. Bounded
adjustments capped at 25% of max `rrf_raw`; penalties cannot go below zero.
**Seam flag:** slice 1 has no identity/alias registry — P4 owns creating the
minimal one (UID/key/accepted-alias → artifact, with alias authority + status +
registry generation). Port the ordering from `examples/05_stdlib/spipe/src/index/fusion.js`
and `exact.js`; validate against `wave4_search/fusion_results.json`.
Accept: `bin/simple test test/01_unit/app/spipe/fusion_rrf_spec.spl test/01_unit/app/spipe/identity_dominance_spec.spl`

### P5 — SearchProviderAdapter (Simple)
Owns `src/app/spipe/search/adapter.spl`, `.../search/in_process_adapter.spl`,
`.../search/process_adapter.spl`, `.../search/launch_policy.spl`,
`.../search/response_validation.spl`, `.../search/cache_key.spl`,
`test/01_unit/app/spipe/search_adapter_spec.spl`,
`.../search_response_distrust_spec.spl`, `.../search_launch_policy_spec.spl`.
Contract: §4.1 launch hardening, §4.3 response distrust (one outstanding request
per correlation ID; verify workspace/snapshot/scope/score contract/analyzer/query
receipt; ranks unique+contiguous+ordered; explanations schema-bounded and
escaped; navigation targets reconstructed from SPipe's own graph, never accepted
from the provider), §14.5 state machine
`new → initializing → healthy → quarantined|unavailable → closed` with exactly one
fallback after proving logical-root parity, §5.1 full cache key.
**Language note:** in pure-Simple composition `InProcessSearchProviderAdapter`
cannot literally wrap `JsFixedPointSearchProvider` — that is JavaScript. The
in-process adapter wraps the **P2 common index engine** behind the same
`SearchProvider` trait; JS parity is exercised only through the JS test harness
and the shared golden fixtures (P11). Do not stall trying to embed the JS
provider.
Accept: `bin/simple test test/01_unit/app/spipe/search_adapter_spec.spl test/01_unit/app/spipe/search_response_distrust_spec.spl test/01_unit/app/spipe/search_launch_policy_spec.spl`

### P6 — Provider executable gap closure
Owns everything under `src/app/spipe_knowledge_provider/` plus
`test/01_unit/app/spipe_knowledge_provider/provider_wire_vectors_spec.spl` (new)
and `.../provider_capability_spec.spl` (new).
Contract: adopt P0's `QueryReceiptV1`/`OperationReceiptV1` (replacing
`OperationReceiptBindingV1` as the wire shape); fix `cancel:false` →
§14.19-real `cancel:true` or file the divergence (correction §2.4); assert the
§14.17.1 wire vectors byte-for-byte against `wave4_search/provider_protocol_vectors.json`
(payload bytes, `000000b0`-style headers, SHA-256s, the `cand-4adcb8c9…` UID); the
`TransportDiagnosticV1` vs `ProviderErrorV1` split (§14.18) — `invalid_utf8` and
`frame_too_large` must close silently and never become a response.
Accept: `bin/simple test test/01_unit/app/spipe_knowledge_provider/`

### P7 — DBFS facade (re-attempt of the §15.1 rejection)
Owns `src/lib/nogc_sync_mut/db/dbfs_engine/fts/*`,
`test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl`.
Contract: §6.1. Delete the duplicate `fts_bm25_score_fixed` and
`wave4_compatibility.spl`'s fixture scorer; `fts_bm25_score` becomes a pure
compatibility facade over `std.common.search.ranking`. Exact `doc_length` +
fixed-point corpus average; `index_document` an idempotent upsert; deterministic
public-ID ties. **The §15.1 rejection reasons are acceptance criteria:** rebuild
and write back value-semantic child copies (no nested-field mutation through
aliases), commit the engine transaction atomically (lexical must not commit
before trigram/content), correct the `contains_document` `me fn` ABI, and the spec
must assert intermediate statistics/averages, independent clean-corpus
statistics, contains/absent behavior, exact result-order equality, legacy success,
and checked-upsert failure/no-change. Advertise `explain:false` until explanation
lands.
Accept: `bin/simple test test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl test/02_integration/storage/dbfs/fts_engine_spec.spl`

### P8 — PureDatabase adapter + cache-key repair
Owns `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/*`,
`test/02_integration/storage/dbfs/{pure_db_spec.spl, pure_db_sql_extended_spec.spl,
db_cache_invalidation_spec.spl}` (verified 2026-08-31 — these three live under
`storage/dbfs/`, not a database directory; `test/integration/storage/dbfs/` is the
diverged mirror tree and is NOT owned by this package).
Contract: §6.2. Repair the `pure_database.spl:1464` key FIRST (add DB instance,
table identity, ordered selected columns, algorithm, MVCC snapshot, FTS
generation) — before touching scoring. Then route BM25 through the common scorer
and delete `row_value_helpers.spl:763 _bm25_score` (f64) only after proving its
callers gone. Keep `Contains`/`TermFrequency`/`Bm25` distinct; preserve
`bm25_search`/`fts5_search` facades; prove insert/update/delete/rollback/reopen
invalidation parity.
Accept: `bin/simple test test/02_integration/storage/dbfs/pure_db_spec.spl test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl test/02_integration/storage/dbfs/db_cache_invalidation_spec.spl`

### P9 — Textual DB BM25 side-index
Owns `src/lib/nogc_sync_mut/database/fts.spl`, `.../fts_lexical.spl` (new),
`test/.../textual_fts_lexical_spec.spl`.
Contract: §6.3. `fts_search` semantics unchanged (trigram); add `search_lexical`
on a separate BM25 side-index. Row/WAL mutation and lexical delta are one logical
transaction; recovery replays the row log then validates-or-rebuilds the
side-index generation. Derived index never becomes the row source of truth. No
async/GC tier copies.
Accept: `bin/simple test test/01_unit/lib/database/textual_fts_lexical_spec.spl`

### P10 — Duplicate primitives
Owns `src/lib/common/search/fingerprint.spl`, `.../similarity.spl`,
`.../candidate_bucket.spl`, and the adaptation edits in
`src/compiler/90.tools/duplicate_check/{features,math_utils,semantic}.spl`,
plus `test/01_unit/lib/common/search/fingerprint_spec.spl`,
`.../candidate_bucket_spec.spl`.
Contract: §7. Write MinHash/SimHash/shingle hashes (they do not exist —
correction §2.6); move cosine + sparse token-frequency vectors into
`similarity.spl` and have the tool call in; bounded candidate bucketing, never
all-pairs. Pair ordering `score desc, left ID asc, right ID asc`. Pinned CLI
report/exit-code parity is the gate. `DuplicationConfig`, `SimpleToken`, FS
collection, Ollama HTTP, formatters, CLI parsing stay in the tool.
Accept: `bin/simple test test/01_unit/lib/common/search/fingerprint_spec.spl` **and** the existing duplicate-check suites still green.

### P11 — Golden conformance + perf harness scaffolding
Owns `test/02_integration/spipe/search_golden_conformance_spec.spl` (new),
`test/02_integration/spipe/fusion_golden_spec.spl` (new),
`examples/05_stdlib/spipe/test/fixture/wave4_search/{benchmark_operation_plan_v1.json,
qualified_search_profile_v1.json}` (new),
`examples/05_stdlib/spipe/test/perf/measure_qualified_search.mjs` (new).
Contract: §10.1 one corpus drives common scorer, DBFS facade, PureDatabase
adapter, textual adapter, `JsFixedPointSearchProvider`, and the Simple provider —
ordered IDs and integer scores, never approximate floats. §14.6.1/§14.6.2
artifacts built to schema; the collector must emit `not_evidence` and write no
receipt on this host, and the plan says so up front (correction §2.10).
Starts after P2+P3 land (it needs the oracle); its fixture-authoring half can
start at the P0 gate.
Accept: `bin/simple test test/02_integration/spipe/`

### Dependency order

```
P0 (SOLO, gated on disk)
   ├─ P1 analyzer ─┐
   ├─ P2 index ────┼─> P11 conformance + perf harness
   ├─ P3 explain ──┘
   ├─ P4 fusion + identity ─┐
   ├─ P5 adapter ───────────┴─> integration (adapter drives provider)
   ├─ P6 provider
   ├─ P7 DBFS   ├─ P8 PureDatabase   ├─ P9 textual
   └─ P10 duplicate primitives
```

---

## 5. FROZEN INTERFACES

Package 0 declares these verbatim. No other package re-declares any of them.
Where the design gives a schema, the design's field list is authoritative; the
Simple spellings below are the freeze.

### 5.1 Analyzer identity and seam (§15.2)

```simple
pub enum SearchFieldIdentityV1:
    Identifier
    Title
    Heading
    Classification
    Body

pub enum AnalyzerErrorV1:
    InvalidLimits
    InvalidFieldIdentity
    InputLimitExceeded
    InvalidUtf8
    NormalizedLimitExceeded
    TokenBytesLimitExceeded
    TokenCountLimitExceeded
    DistinctTermLimitExceeded

pub struct AnalyzerIdentityV1:
    analyzer_id: text              # "spipe-unicode-lex-v1"
    unicode_version: text          # "17.0.0"
    unicode_manifest_sha256: text
    normalization_id: text
    lowercase_id: text
    tokenizer_id: text
    stop_words_id: text            # "en-basic-v1"
    stop_words_sha256: text        # 6f0a7c26d3d0e3d06a2fbbbeaa1843294f83c3be26baf1c04651191e011510bf
    stemming_id: text              # "none"
    field_schema_id: text
    limits_schema_id: text

pub struct AnalyzerLimitsV1:
    max_input_bytes: i64
    max_normalized_bytes: i64
    max_token_bytes: i64
    max_tokens: i64
    max_distinct_terms: i64

pub struct AnalyzedTokenV1:
    value: text
    position: i64                  # one-based, assigned BEFORE stop-word removal
    exact_identifier: bool

pub struct AnalyzedTextV1:
    normalized: text
    tokens: [AnalyzedTokenV1]

pub struct AnalyzedQueryTermV1:
    value: text
    qtf: i64                       # explanation-only; never affects scoring

pub struct AnalyzedQueryV1:
    normalized: text
    terms: [AnalyzedQueryTermV1]   # distinct, sorted by unsigned UTF-8 bytes
```

Functions (P1 implements; P0 declares nothing executable):
`analyze_field_v1(input: text, field: SearchFieldIdentityV1, identity: AnalyzerIdentityV1, limits: AnalyzerLimitsV1) -> Result<AnalyzedTextV1, AnalyzerErrorV1>`,
`analyze_query_v1(input: text, identity: AnalyzerIdentityV1, limits: AnalyzerLimitsV1) -> Result<AnalyzedQueryV1, AnalyzerErrorV1>`,
`unsigned_utf8_less(left: text, right: text) -> bool`.

Query limits are exactly `AnalyzerLimitsV1(4096, 4096, 4096, 128, 128)`.

### 5.2 Score contract `bm25-fixed-v1` (§14.3, §14.10)

Already landed in `ranking.spl`. P0 freezes only the identity constants and the
public tuple; it does not re-declare arithmetic.

```simple
pub val BM25_FIXED_V1_ID: text = "bm25-fixed-v1"
pub val BM25_SCALE: i64      = 1000000
pub val BM25_K1: i64         = 1200000
pub val BM25_B: i64          =  750000
pub val BM25_LN2: i64        =  693147

# Closed field order + contract weights (§14.1). Ordinal is the array position.
pub val BM25_FIELD_NAMES: [text]   = ["identifier","title","heading","classification","body"]
pub val BM25_FIELD_WEIGHTS: [i64]  = [4000, 4000, 2500, 2000, 1000]

pub struct FieldStatsV1:
    field: text                    # one of BM25_FIELD_NAMES
    num_docs: i64                  # N, live documents in this field corpus
    total_length: i64
    average_length_scaled: i64     # floor(total_length * BM25_SCALE / N)
```

Arithmetic rule (correction §2.8): all intermediates are checked i64 via
`ranking.spl`'s `_checked_*` helpers; any operation that cannot be proven exact
returns `score_overflow`. Division truncates toward zero. Conversion to public
`Score` milli happens exactly once, after all weighted field contributions
accumulate. Ties: score descending, then ascending unsigned UTF-8 bytes of the
public document ID.

### 5.3 Source records for fusion (§3.5, §4.3)

```simple
pub enum FusionSourceV1:
    Lexical
    Graph
    Semantic

pub struct SourceCandidateV1:
    document_id: text
    source_rank: i64               # one-based, unique, contiguous within a source
    source_score_milli: i64        # diagnostic only; RRF never reads it

pub struct SourceRankingV1:
    source: FusionSourceV1
    source_contract: text          # "bm25-fixed-v1" | graph contract | model identity
    snapshot_id: text
    scope_digest: text
    candidates: [SourceCandidateV1]  # <= source_k; duplicate IDs are an error
    complete: bool
    source_digest: text
```

### 5.4 Lexical hit and wire envelope (§14.11, §14.12)

```simple
pub struct SearchHitV1:
    document_id: text
    score_milli: i64
    source_rank: i64                       # [1, 1000]
    matched_fields: [text]                 # subset of BM25_FIELD_NAMES, max 5
    explanation: SearchExplanationV1?      # non-null iff requested

pub struct ProviderErrorV1:
    code: text                             # closed set, §14.18
    message: text
    retryable: bool

pub struct RequestEnvelopeV1:
    request_id: text
    operation: text                        # closed vocabulary, §4.3
    protocol_major: i64                    # always 1
    protocol_minor: i64                    # always 0
    provider_generation: text              # "pg-" + 32 lowercase hex
    workspace: text                        # WS- UID, <= 128 bytes
    snapshot: text                         # spks1- UID, <= 128 bytes
    scope_digest: text                     # "sha256:" + 64 hex
    query_receipt: QueryReceiptV1?
    operation_receipt: OperationReceiptV1?
    deadline_ms: i64                       # [1, 30000]
```

`SuccessResponseV1` / `ErrorResponseV1` carry the same binding fields plus
exactly one of `result` / `error`. `PreBindingErrorResponseV1` is the ONLY shape
that may omit them, and only for `initialize` rejection or `handshake_required`
(§14.11). `TransportDiagnosticV1{code, byte_count}` with `code ∈
{invalid_utf8, frame_too_large}` is local evidence and is **never serialized as a
response** (§14.18).

### 5.5 Fusion `rrf-fixed-v1` and the dominance tier (§3.5)

```simple
pub val RRF_FIXED_V1_ID: text  = "rrf-fixed-v1"
pub val RRF_DEFAULT_K: i64     = 60         # configurable in [1, 10000]
pub val RRF_DEFAULT_SOURCE_K: i64 = 1000    # also the maximum
pub val RRF_MAX_POOL: i64      = 3000       # internal pool before the 1000-hit public limit
pub val RRF_BOOST_CAP_PERMILLE: i64 = 250   # total positive boost <= 25% of max rrf_raw

pub enum MatchTierV1:
    ExactIdentity        # rank 1, outside RRF, no fused rank or score
    Fused                # ranks begin at 2 when an identity is pinned

pub struct FusedHitV1:
    document_id: text
    match_tier: MatchTierV1
    final_rank: i64
    rrf_raw_scaled: i64
    rrf_adjusted_scaled: i64

pub struct IdentityExplanationV1:
    resolved_uid: text
    matched_key: text
    alias_authority: text
    alias_status: text
    registry_generation: i64
    visibility_decision: text
    pinned_rank: i64                       # always 1

pub struct FusionExplanationV1:
    contract: text                         # RRF_FIXED_V1_ID
    k: i64
    source_k: i64
    source_names: [text]                   # ordered; affects rendering only, never the sum
    source_ranks: [i64]                    # -1 encodes "source absent for this document"
    source_contributions_scaled: [i64]
    adjustments: [text]
    adjustment_caps_scaled: [i64]
    raw_sum_scaled: i64
    adjusted_sum_scaled: i64
    tie_break_document_id: text
```

Invariants P4 must enforce: `rrf_raw = Σ 1/(k + source_rank)` in fixed point, no
binary floating point anywhere; the pinned identity has **no** RRF rank,
contribution, raw score, or adjusted score, so nothing can tie or displace it;
final ordering is adjusted desc → raw desc → document ID ascending.

### 5.6 Analyzer/score/index identity constants (§14.1)

```simple
pub val PROVIDER_CONTRACT_ID: text      = "spipe-search-provider/1.0"
pub val ANALYZER_CONTRACT_ID: text      = "spipe-unicode-lex-v1"
pub val SCORE_CONTRACT_ID: text         = "bm25-fixed-v1"
pub val EXPLANATION_CONTRACT_ID: text   = "bm25-explain-v1"
pub val LOGICAL_INDEX_CONTRACT_ID: text = "spipe-lexical-snapshot-v1"
pub val FUSION_CONTRACT_ID: text        = "rrf-fixed-v1"
pub val CANONICAL_JSON_ID: text         = "spipe-canonical-json-v1"
```

---

## 6. HAZARDS

**Simple-language (binding on every package; carried forward from refined plan §3.5):**

1. **Fixed point, never `f64`.** The design freezes BM25 as fixed point precisely
   for cross-implementation determinism. Independently, native codegen still has an
   open **`f64`-value `Dict.get()` miss** gap (`doc/07_guide/language/dict_native_pitfalls.md`).
   A postings or statistics map keyed to `f64` is a correctness bug on two axes.
   Every score, contribution, ratio, and boost cap in this slice is a scaled
   integer. P8 deleting `row_value_helpers.spl:763 _bm25_score` is the single
   largest `f64` removal in the slice.

2. **`text.len()` is BYTES; `s[i]` indexes CHARS.** This matters more here than
   anywhere in slice 1: the analyzer is the one component whose entire job is
   non-ASCII text. `analyzer.spl` currently gets this right by converting via
   `text_codepoints` (L83) and indexing the codepoint array — **P1 must preserve
   that shape**. A `while i < s.len()` + `s[i]` loop anywhere in P1, P3, or P10 is
   a defect even when the fixture passes, because the fixtures include astral and
   combining-mark cases. Byte offsets and codepoint indices must never be mixed in
   one expression.

3. **COW alias mutation.** Postings lists, per-field statistics tables, segment
   tombstone sets, and the RRF candidate pool are exactly the shape that
   value-semantics copy-on-write destroys: `val t = self.postings; t.push(x);
   self.postings = t` is O(n) per insert, invisible on a 5-document fixture and
   catastrophic on the 50,000-artifact qualification corpus. Mutate through the
   single owner (`self.postings[term].push(id)`) and hoist `.keys()`/`.values()`
   above loops. Ratcheted by `scripts/check/check-cow-alias-hotpath.shs`. §15.1
   already rejected one DBFS bundle for precisely this — P7 is re-attempting under
   that finding.

4. **`Result<T,E>` + `?` only — no try/catch.** Candidate lifecycle recovery,
   replay, quarantine, and deadline expiry are typed states and typed errors, not
   exception unwinding. The §14.18 error vocabulary is a closed enum-shaped set;
   do not collapse codes into a generic failure.

5. **No inheritance; generics `<>`.** Traits + composition. `LexicalSearchPort`,
   `SearchProvider`, `SearchProviderAdapter` are traits/structs, never a base class.

6. **SSpec: `describe` inside `fn main` exits 1 despite 0 failures** — end every
   spec with `return ()`. Every spec ships pass **and** mutation-red evidence
   (inject the bug, watch it fail, restore, re-verify byte-identical).

7. **Nested closures read but do not modify outer vars**; **chained methods on
   erased (dict/ANY) receivers fail mid-chain** — bind a typed intermediate `val`
   before chaining. The index engine pulling `IndexedDoc` out of a dict hits this.

8. **Do not lint `src/lib/common/search/generated/`.** That file has single lines
   of 15,369 bytes and lint cost is superlinear in declaration content
   (`.claude/rules/commands.md`). Exclude it from lint/fix passes explicitly.

**Design-specific:**

9. **Three canonical encoders is one too many.** `src/app/spipe/model/canonical.spl`
   (slice 1) is NOT §14.9-compliant. `spipe_knowledge_provider/canonical_json_*`
   IS. P0's `canonical_json.spl` is a seam over the latter. Any logical root,
   payload hash, receipt preimage, or candidate UID computed with the slice-1
   encoder is silently wrong. Slice 1 just spent a whole seam collapsing two
   encoders (refined plan §8.1) — do not regress it.

10. **Explanation intermediates are decimal STRINGS (`I128Decimal`), never JSON
    numbers** (§14.13). `explain.spl` already types them `text`; P3 must keep that
    and never "improve" a field to an integer because the value happens to fit.
    Mixing number and string for the same field is explicitly forbidden.

11. **Exact identity is not a score boost.** §3.4's last bullet and §3.5 both say
    it: the dominance tier sits outside RRF and is never encoded as IDF or a
    provider score bump. A P4 implementation that pins by adding a large constant
    is wrong even if the output ordering matches the fixture.

12. **The provider is untrusted after verification.** §4.3: every response field is
    re-validated, hit IDs re-checked against the visible snapshot and visibility
    policy, and navigation targets reconstructed from SPipe's own graph. A poisoned
    explanation **discards the whole page and quarantines the snapshot** — it is
    never shown with the explanation stripped, because that hides a compromise.

13. **Perf numbers are not evidence without a receipt** (§14.6). Do not report a
    latency figure as PASS. W4-SRCH-09 is mechanically `NOT EVIDENCE` on this host
    (correction §2.10). Functional parity, bounds, and absence of per-query
    spawning are hard gates independent of timing — those are reportable.

14. **No optimization before the oracle.** WAND/BMW/ANN must return byte-identical
    ordered IDs and scores to exhaustive, including ties and deletes. They are not
    in this slice; a package that adds a "fast path" has failed its contract.

---

## 7. RECORDED DEBT

1. Design §15.2/§15.3 evidence checkpoints are stale (correction §2.1/§2.2). The
   design should be amended, or a dated note added, so the next reader does not
   redo the Unicode bundle.
2. `wire_core.spl:209` `cancel:false` vs §14.20 `cancel:true` — P6 resolves or files.
3. Provider receipt shape divergence (`OperationReceiptBindingV1` vs the frozen
   `OperationReceiptV1`; no `QueryReceiptV1` at all).
4. DBFS carries two scoring paths (`fts_bm25_score_fixed` local + the shared
   import) — P7 removes one.
5. `contains_fuzzy` named by §6.3 does not exist (correction §2.7).
6. MinHash/SimHash/shingling described as "extract" are actually new code (§2.6).
7. `benchmark_operation_plan_v1.json`, `qualified_search_profile_v1.json`, and
   `measure_qualified_search.mjs` are absent; §14.6.2 names them as the sole
   collection entry point.
8. Slice-1 seam still open (refined plan §8.1 item 2): S1-A's reverse index is not
   consumed by S1-B. P4's graph source needs the accepted typed edge graph — if it
   depends on that wiring, it is a real prerequisite, not a rename.
9. `src/app/spipe/balance/config.sdn` remains documentation-only while
   `config.spl` hardcodes the same numbers (refined plan §8.1 item 4).
