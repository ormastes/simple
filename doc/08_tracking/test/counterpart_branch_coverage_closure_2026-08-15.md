# Counterpart line-coverage closure — 2026-08-15

Scope: `src/lib/nogc_sync_mut/spec/evidence/counterpart/**` driven by
`test/01_unit/infra/counterpart/**`. Method: per-spec
`SIMPLE_COVERAGE=1 bin/simple test --coverage <spec> --no-session-daemon` with
`SIMPLE_COVERAGE_OUTPUT` dumps; uncovered lines recomputed with the exact
recordable-line heuristic of `test_runner_single.spl:_cov_report_for_file`
(verified to reproduce the runner's hit/total for every module).
`chrome_dom_snapshot_provider` and `compress_gzip_provider` were verified green
earlier and deliberately untouched.

Collector artifacts (excluded-by-tooling, per the standing collector rule):
top-level `pub val` initializers and `match` statement heads are never
recorded by the interpreter collector even when executed.

## Closure table (covered + excluded = total for every module)

| Module | Recordable | Covered | Artifact-excluded (lines) | Unreachable-excluded (lines) |
|---|---|---|---|---|
| provider_registry | 65 | 65 | — | — |
| cipher_sha256_provider | 18 | 14 | 52,53,54,58 (pub val) | — |
| converter_registry | 58 | 56 | 58,59 (pub val) | — |
| converter_graph | 116 | 113 | 63,64,65 (pub val) | — |
| package_registry | 213 | 205 | 47,49,50,51 (pub val); 95,104,118 (match heads) | 542 (proof P1) |
| relation_engine | 78 | 76 | 336,357 (match heads) | — |
| matrix_compare | 93 | 91 | 68 (pub val); 92 (match head) | — |
| dynlib_provider | 36 | 33 | 51 (pub val) | 92 (P2); 159 (P3) |
| process_provider | 14 | 12 | 60 (pub val); 111 (match head) | — |
| provider_runner | 41 | 39 | 180,222 (match heads) | — |
| artifact_store | 50 | 47 | 31 (pub val) | 118 (P4); 146 (P5) |
| worker_provider | 126 | 117 | 43,44,45 (pub val); 104,112,120,290,345 (match heads) | 217 (P6) |

Attribution spec per module: provider_registry/process_provider/provider_runner
← provider_registry_spec; cipher ← cipher_counterpart_compare_spec;
converter_registry/converter_graph ← converter_graph_spec; package_registry ←
package_registry_spec; relation_engine/matrix_compare ← relation_matrix_spec;
dynlib ← dynlib_load_compare_spec; artifact_store ← artifact_store_spec;
worker_provider ← worker_receipt_spec.

## New examples added (this closure)

- `dynlib_load_compare_spec.spl` — "returns the empty digest when the output
  buffer cannot be allocated": `dynlib_call_digest3(..., out_len: 0)`;
  `rt_alloc(size <= 0)` returns NULL by contract
  (`src/runtime/runtime_memory.c:260`), covering `dynlib_provider.spl:79` with
  a real allocation failure, no fault injection.
- `dynlib_load_compare_spec.spl` — "reports unavailable when the dlopen'd
  soname is shadowed by an EMPTY file in cwd": plants a zero-byte
  `libcrypto.so.3` in cwd (loader resolves the real one; the artifact re-read
  hits the empty shadow), asserting the fail-closed unavailable outcome.
- `worker_receipt_spec.spl` — "keeps a blank numeric field (no value at all) a
  sentinel, never a zero": `invocation: ` with nothing after the colon covers
  `worker_provider.spl:229` (`parse_decimal` empty-body sentinel).

## Unreachable proofs

- **P1** `package_registry.spl:542` (`return digest` when `digest.len() <= 32`):
  `sha256_text` (`src/lib/common/crypto/sha256.spl:197`) returns hex of a
  32-byte digest (64 chars) on the runtime path and falls back to
  `sha256_u8_hex` (also a 64-char hex of a 32-byte result) otherwise; no path
  returns ≤32 chars. Reaching 542 requires fault-injecting sha256 itself.
- **P2** `dynlib_provider.spl:92` (short read after the call):
  `rt_bytes_from_raw` (`runtime/src/value/sffi/file_io/file_ops.rs:1006`)
  returns exactly `len` bytes whenever `ptr != 0 && len > 0`; at this site
  `out_ptr != 0` (checked line 78) and `out_len > 0` (else returned at 79).
- **P3** `dynlib_provider.spl:159` (zero-length library file after a
  successful read): measured with the planted empty-file example — the
  zero-byte `rt_file_read_bytes` result fails the `.?` gate at line 155
  (empty array reads as absent), so control takes 156; the decision probe at
  line 158 records `true_count = 0` across the whole suite including that
  example. No input can reach 159 without patching the runtime.
- **P4** `artifact_store.spl:118` (runtime returns non-sha256 digest):
  `rt_file_write_text(staging, ...)` returned true at line 112, so the staging
  file exists and is readable by the same uid; `rt_file_hash_sha256`
  (`file_ops.rs:491`) then returns `format!("{:x}", Sha256)` — always 64
  lowercase hex — so `is_sha256_ref(digest)` cannot fail. Requires a
  concurrent unlink/chmod between lines 112 and 115 (fault injection).
- **P5** `artifact_store.spl:146` (read-back hash mismatch): line 137 writes
  exactly the bytes hashed at line 115; line 144 re-hashes the same path in
  the same call. A mismatch requires external concurrent mutation of
  `final_path` between lines 137 and 144 — pure race, fault injection only.
  (The mid-put corruption branch at 128-130 IS covered by
  `artifact_store_spec` via a pre-planted wrong-content blob.)
- **P6** `worker_provider.spl:217` (`hex_pair` length guard): sole caller is
  `unquote` line 192, `hex_pair(body.slice(index + 2, index + 4))` under the
  guard `index + 3 < body.len()` — the slice is always exactly 2 chars, so
  `pair.len() != 2` never holds.

## Verdicts (all touched/owning specs green)

- `PASS test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl` — Results: 8 total, 8 passed, 0 failed
- `PASS test/01_unit/infra/counterpart/worker_receipt_spec.spl` — Results: 18 total, 18 passed, 0 failed
- `PASS` (unchanged, from the same session's coverage batch):
  artifact_store_spec, contract_model_spec, converter_graph_spec,
  package_registry_spec, provider_registry_spec, relation_matrix_spec,
  evidence_projection_spec, cipher_counterpart_compare_spec.

Pre-existing, out of scope: `counterpart_abi_spec.spl` FAILs on the seed
binary (`unknown extern function: rt_counterpart_probe_abi` /
`rt_counterpart_open`) — not a counterpart-module regression and untouched by
this closure.
