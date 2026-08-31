# Golden query→score pipeline is not yet assembled (P11)

**Filed:** 2026-08-31 · **Status:** OPEN · **Severity:** informational (scope gap, not a defect)

## Summary

`examples/05_stdlib/spipe/test/fixture/wave4_search/golden_results.json` gives
exact expected `score_milli`, `matched_fields`, `source_rank`, and
`explanation_hash` per query against the golden corpus
(`golden_corpus.json`), per design doc §10.1: "one corpus drives the common
Simple exhaustive scorer... Assertions compare ordered IDs and integer
scores, not approximate floats."

As of this session (P0-P5 landed independently in parallel), there is no
single callable entry point that:

1. tokenizes a query and each document field with the frozen
   `spipe-unicode-lex-v1` analyzer (`src/lib/common/search/analyzer.spl`),
2. builds per-field term/document-frequency postings over an `IndexEngine`
   snapshot (`src/lib/common/search/index_engine.spl`, `segment.spl`),
3. feeds those into `ranking.spl`'s `bm25_fixed_v1_score_checked` per
   candidate document, and
4. assembles ordered `SearchHitV1` results with `explain_build.spl`.

Each piece exists in isolation (P1 analyzer, P2 index/segment, P3
explain/field_stats, P0 ranking) but no P0-P5 module wires them together into
one "run this query against this corpus" function. `bm25_intermediates.json`
in the same fixture directory is itself a placeholder
(`"status": "not_evidence_until_js_simple_dbfs_compute_identical_vectors"`),
confirming the gap is tracked at the design level, not merely missed by this
session.

## What P11 verified instead

`test/02_integration/spipe/search_golden_conformance_spec.spl` verifies the
mechanically-available surface against the real golden corpus content:
`IndexEngine` document-count/contains/find and rebuild-determinism
(`logical_root` parity across rebuild + reordering), and `field_stats.spl`
aggregation arithmetic against lengths taken from the same corpus documents.
It does **not** assert score_milli/explanation_hash parity against
`golden_results.json`'s query fixtures — that remains unverified pending the
orchestrator described above.

## Unblock condition

A P5/adapter-level (or new orchestrator) module that, given an `IndexEngine`
and a `SearchQueryV1`, returns ordered `SearchHitV1` results by running the
full analyze→postings→bm25_fixed_v1_score_checked→explain chain. Once that
exists, extend `search_golden_conformance_spec.spl` to assert exact
`score_milli`/`matched_fields`/`source_rank` parity per query in
`golden_results.json`, and regenerate `bm25_intermediates.json` with real
vectors instead of its current placeholder status.

## Owner

Unassigned — next P-checkpoint that adds the query orchestrator should close
this alongside its own acceptance criteria.
