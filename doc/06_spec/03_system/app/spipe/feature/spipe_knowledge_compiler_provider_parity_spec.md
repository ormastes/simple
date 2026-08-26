# SPipe Knowledge Compiler Provider Parity — Authored Design Scaffold

> **Not generated and not PASS evidence.** The acceptance harness requires
> exactly one closed `SPIPE_WAVE4_CONFORMANCE=` JSON record from each executed
> Simple/DBFS producer. Focused spec verdicts remain insufficient; neither
> producer yet emits all canonical roots, scores, order, statistics,
> explanations, and deltas. The executable spec therefore fails closed.

**Source:** `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl`  
**Generation command:** `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl --output doc/06_spec --no-index`

## REQ/NFR map

- Exact/BM25/RRF: REQ-SPKC-011..014; NFR-SPKC-001..003, 012..013.
- DB/symbol/trace: REQ-SPKC-015..018; NFR-SPKC-006, 020..022.
- Privacy/bounds/performance: NFR-SPKC-007, 011, 014..016.

## Operator flow

Search and trace artifacts against one locked corpus/snapshot, comparing exact
scores, document ordering, explanations, incremental parity, exhaustive/WAND
top-k, and strict trace authority. A malicious/crashed provider must be
contained and reported as `provider_unavailable` or `incompatible_contract`;
lexical fallback must not be mislabeled semantic or Simple-native evidence.

## Fixed query limits

Frame 1 MiB; normalized query 4,096 bytes; tokens 128; Boolean clauses 64;
depth 8; phrase terms 32/phrase and 64 total; expansions 256; filters 32;
values/filter 64; hits 1,000; explanation terms 128/hit, fields 32/hit, bytes
64 KiB/hit and 512 KiB/page; delta documents 1,000; fields/document 64; field
value 1 MiB; duplicate candidates 1,000 total/100 per document; symbols 1,000;
deadline 50 ms minimum and 30 s maximum. Regex and leading unbounded wildcards
are unsupported. One-over returns `frame_too_large`, `limit_exceeded`,
`deadline_exceeded`, or `invalid_request` without truncating semantics.

## Evidence limitation

Retain compact text/protocol receipts without prompts, document content, or
credentials. The exact envelope and delta keys are locked by
`examples/05_stdlib/spipe/test/fixture/wave4_search/conformance_evidence_schema.json`.
The current helper raises `NOT-EVIDENCE`; no parity or performance PASS is
claimed.

## Producer closure still required

The Simple producer must compute (rather than accept) the canonical five-field
logical root, return non-empty per-field statistics, emit the locked query hit
and explanation records, and expose mixed-delta plus clean-rebuild roots.

The DBFS compatibility producer needs an explicit five-field adapter with field
weights/statistics/explanations and deterministic logical-root/delta reporting.
Its process lifecycle rows remain not applicable; the adapter must not invent
receipts, cancellation, or candidate publication support.
