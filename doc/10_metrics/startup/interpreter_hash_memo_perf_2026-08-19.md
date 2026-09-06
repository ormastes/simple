# Interpreter Identifier-Hash Memo Performance — 2026-08-19

## Verdict

**BLOCKED pending a source-matched admitted pure-Simple Stage4 full CLI.** No
performance improvement is claimed from the repository Rust seed. The former
N=7 seed-hosted before/after table is withdrawn as claim-bearing evidence: it
measured a bootstrap host that explicitly says it is not the production tool,
did not bind exact binary/source/harness/tool/host identities, did not
interleave variants, and omitted miss-heavy and product-shaped workloads.

## Safety disposition

`compiler.core.interpreter.hashmap.hm_hash_text` is stateless again. The three
unsynchronized mutable module globals were removed. Optional memoization now
uses an `InterpreterHashMemo` class supplied explicitly to
`hm_hash_text_memoized`; its keys, values, replacement cursor, capacity, hits,
and misses belong to that caller/session object. A zero-capacity object retains
nothing. The legacy `hm_hash_text(text)` API and exact FNV-1a result are
unchanged, so existing interpreter environment paths keep their semantics and
do not acquire shared mutable state.

No production environment lookup is silently switched to the memo. Integration
must wait for an interpreter/session owner whose lifetime and execution domain
are explicit; the performance harness below determines whether that later
integration is justified on Stage4.

## Workloads

- Hot repeated identifiers: stateless and explicit-memo variants, 25,000 loops
  over `eval_current_decl_id`, `frame_locals`, `module_loader_cache`, and a UTF-8
  identifier.
- High-cardinality miss-heavy: stateless and eight-entry explicit-memo variants,
  4,096 distinct identifiers. The memo must retain exactly eight entries, report
  4,096 misses and zero hits, and match the stateless checksum.
- Product-shaped LOAD_FAST: parameters and resolved locals with interpreter
  identifiers plus the explicit memo.
- Product-shaped slow environment: module/global reads with the same identifier
  family plus the explicit memo.

The semantic fixtures all return exact fixed checksums. The miss-heavy Stage4
gate allows at most 12500 basis points (25%) p50 and p95 memo/stateless overhead;
the hot memo must not regress either percentile.

## Claim-bearing evidence contract

Run only with the exact admitted Stage4 executable and its adjacent provenance:

```sh
SIMPLE_BINARY=/absolute/path/to/stage4/simple \
SIMPLE_COMPILER_PROVENANCE=/absolute/path/to/stage4/simple.provenance.env \
sh scripts/check/check-interpreter-hash-memo-perf.shs
```

The collector rejects Rust-seed identity, missing or invalid adjacent Stage4
provenance, source mismatch, any identity race, or `N < 7` before publishing a
performance row. Samples alternate forward/reverse order within every sample.
The immutable `interpreter-hash-memo-perf-evidence-v1` receipt binds:

- exact binary path/SHA-256 and adjacent provenance path/SHA-256;
- admitted content source revision and subject-source SHA-256;
- fixture-manifest and harness SHA-256;
- timing-tool path/SHA-256;
- hostname, uname, CPU text, and their identity SHA-256;
- exact interleave order;
- raw elapsed milliseconds, max RSS KiB, stdout SHA-256, and stderr SHA-256 for
  every hot-stateless, hot-memo, miss-stateless, miss-memo, LOAD_FAST, and
  slow-environment sample;
- N, p50, p95, and memo/stateless ratios.

Current fail-closed result:

```text
STATUS: BLOCKED interpreter-hash-memo performance not measured: Rust seed rejected; an admitted source-matched pure-Simple Stage4 CLI is required
```

## Correctness and detector evidence

- `interpreter_hash_text_correctness_spec.spl`: 4 examples passed, including
  byte-for-byte ASCII/UTF-8 parity, 999 explicit-owner cache hits, 4,096 distinct
  miss-heavy identifiers bounded to eight entries, and absence of the former
  module-global cache variables.
- `interpreter_hash_memo_evidence_contract_spec.spl`: 3 examples passed,
  including exact receipt-field coverage, deliberate `N=6` rejection, and Rust
  seed rejection without a receipt or PASS.
- All six fixtures returned their exact checksum/counter verdicts. These were
  correctness executions under the seed and are not performance evidence.
