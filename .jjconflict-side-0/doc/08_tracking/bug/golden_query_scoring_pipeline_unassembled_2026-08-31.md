# Golden query→score pipeline is not yet assembled (P11)

**Filed:** 2026-08-31 · **Status:** RESOLVED (2026-09-02) · **Severity:** informational (scope gap, not a defect)

> **RESOLVED 2026-09-02 — the header was stale, not the body.** This record's own
> "Update 2026-08-31 (later same day) — CLOSED" section (below) already describes
> the landed orchestrator; only the status line still said OPEN.
> Re-verified by source inspection of `origin/main` @ `1b76db1d6c3`:
> `src/lib/common/search/query_exec.spl:300` defines `pub fn run_query_v1(...)`;
> `src/lib/common/search/index_engine.spl:43` defines the additive `documents()`
> accessor; `test/02_integration/spipe/search_golden_query_parity_spec.spl` is
> present and asserts the golden `score_milli`/`explanation_hash` parity.
> Nothing in the unblock condition remains unmet.

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

## Update 2026-08-31 (later same day) — CLOSED

`src/lib/common/search/query_exec.spl` is the orchestrator (`run_query_v1`):
analyzer.spl -> per-document/per-field postings -> `ranking.spl`'s
`bm25_fixed_v1_score_checked` -> `top_k.spl`'s `exhaustive_top_k_v1`, with a
`build_explanation` (`explain_build.spl`) self-consistency check on every
scored hit. `IndexEngine` gained one additive accessor, `documents()`
(`index_engine.spl`), since nothing previously enumerated a corpus's full
document set.

`test/02_integration/spipe/search_golden_query_parity_spec.spl` asserts EXACT
`score_milli`/`matched_fields`/`source_rank`/`explanation_hash` parity against
every query in `golden_results.json` (`alpha-search`, `identifier`,
`public-filter`) — all pass. Verified as a real (non-vacuous) check: flipping
`ranking.spl`'s `K1_DEFAULT` by one digit turns all 3 query assertions RED
with a clear score/hash mismatch, and reverting turns them green again.

Two things intentionally were NOT forced to match bit-for-bit, both already
documented as deliberate elsewhere in this tree, so the spec supplies them as
explicit parameters rather than deriving them from a module whose docstring
already disclaims exact parity:
- `IndexEngine.logical_root()` / `Segment.logical_root` (`segment.spl`) uses
  a documented INTERIM delimited-text digest, not canonical JSON, so it does
  not equal the oracle's canonical-JSON logical root. `run_query_v1` takes
  `logical_root` as a caller-supplied parameter (used only inside the
  explanation hash) instead of assuming engine parity.
- The oracle's ad hoc JS explanation object (`examples/05_stdlib/spipe/src/
  index/bm25.js` `finalizeExplanation` + `logical_index.js`
  `explainDocument`) uses different field names/shape than
  `explain_build.spl`'s frozen `SearchExplanationV1` (`N` vs
  `document_count`, extra per-term `qtf`/`length_ratio_scaled`/
  `norm_scaled`/`denominator_scaled`/`idf_argument_scaled`). `query_exec.spl`
  hashes a hand-assembled oracle-shape canonical JSON built from the same
  checked `Bm25TermTrace` values (`bm25_term_checked_trace`) for the hash
  comparison, while still calling `build_explanation` on every hit to prove
  the frozen contract's own `public_score_milli` reconciles independently
  (`explanation_reconciliation_mismatch` fails closed if it doesn't).

No golden vector was skipped or weakened to reach green.
