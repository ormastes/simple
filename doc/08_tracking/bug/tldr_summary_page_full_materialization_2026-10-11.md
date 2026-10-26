# TLDR summary pages materialize the full rendered summary

Status: source-confirmed repeated work; proposed patch unapplied. Runtime
performance and full-store regression qualification are blocked/unrun.

## Owner and call chain

`src/compiler/80.driver/cache/summary/summary_store_v1.spl`:

- `VirtualSourceStoreAdapterV1.stat` calls `_rendered_bytes_v1(value).len()`
  solely to obtain the byte size.
- `read` and `page` call `SummaryStoreV1.row` on every bounded request. That
  function decodes the complete canonical summary, verifies its identities,
  hashes its rendered text, and regenerates the rendered projection. Those
  checks protect the rebuildable DB against corruption and must remain.
- After validation, `_rendered_bytes_v1` converts **all** rendered text into
  a `[u8]` array. Only then do `read` and `page` slice the requested bytes.

For N rendered UTF-8 bytes and K bounded requests, the final conversion alone
visits/materializes K*N bytes before selecting the windows. This is source
operation counting, not measured allocated bytes or CPU attribution. The
same row's full validation is an additional repeated cost with a separate
authority/lifetime problem; do not remove it under this patch.

Compiler CLI, MCP, LSP MCP and SPipe expose the virtual-source adapter. These
facts do not establish that Phase3 invokes it or that it caused Phase3 RSS.

## Minimal candidate

An unapplied review patch and source pin are retained in
`build/native_probe/phase3-memory-perf-review-20261011/`:
`summary-store-candidate.patch`, `summary_store_v1.before.spl`,
`summary_store_v1.candidate.spl`, and `summary-store-source-pin.json`.

The candidate obtains size from text byte length, copies only the requested
range with `byte_at`, and keeps `bytes_to_text` at the page boundary. It keeps
all row validation, authentication, continuation checks, digests and public
interfaces. End calculation uses `offset + min(length - offset, max_bytes)`
after validating offset and limit, avoiding an overflowing addition.

Pure runtime `src/runtime/simple_core/core_string.spl:655` implements string
length from its stored byte length or raw C-string byte length; `byte_at` at
line 885 loads a byte. Raw-pointer text rescans for length in each `byte_at`,
so its time cost must also be measured. Array push mutation and runtime
representation equivalence remain executable proof obligations.

## Bounded baseline attempts

The existing b580 native Hello producer and pinned 382-file runtime capture
were reused. Only an isolated one-module byte-boundary fixture was compiled;
the compiler itself was not rebuilt. Windows Job collection enforced 2 GiB
per compile, a 23 GiB Phase3 RAM reserve plus the task allowance, 8 GiB free
disk reserve and bounded logs. All three attempts are terminal/quiescent.

| Attempt | Result | Inclusive wall | Peak process-tree RSS |
|---|---|---:|---:|
| baseline | SCV inventory admission missing; no fixture compilation | 1.023 s | 31,292 KiB |
| baseline-cycle2 | HIR aggregate failure; one failed module | 6.738 s | 283,572 KiB |
| baseline-cycle3 | Direct HIR diagnostic: unresolved `min` at fixture lines 16/33 | 6.093 s | 263,836 KiB |

The last attempt used supported `SIMPLE_HIR_SHARDING=0` to expose the error;
HIR caching and semantic validation remained enabled. The missing standalone
minimum helper was a fixture omission, not proof of a compiler defect. The
prepared fixtures now define their own `bounded_min`; the three immutable
failed captures remain unchanged. No fourth attempt was launched. No fixture
executable was produced and no baseline/candidate runtime comparison exists.

## Reproduction and prevention

Prepared native fixtures: `bounded_bytes_baseline.spl` and
`bounded_bytes_candidate.spl` in the evidence directory above. Their assertions
cover empty and ASCII input, multibyte UTF-8, embedded NUL, every slice of the
small inputs (including inside codepoints), byte-size parity, page conversion
parity, negative/zero limits, out-of-range offsets and maximum-i64 rejection.
The workload requests 128 64-byte windows from a 65,536-byte rendered value and
checks the actual result checksum. These exercise the extracted boundary,
not the full DB-backed summary store.

`run_boundary_probe.py` records exact compiler arguments, producer/source
identities, binary hash if emitted, wall time, peak RSS and bounded child logs.
Its consumed baseline output directories are create-once; the three-attempt
cap deliberately prevents a same-session rerun. In a new scoped session,
review the corrected fixtures, pin them in fresh output locations, and use
the recorded native-build and collector arguments. Do not use `simple test`
or `simple run` on b580: its captured bootstrap dispatcher supports neither
as a public command, and do not substitute the Rust seed.

After the baseline executes, run the same boundary fixture against the
candidate, measure elapsed/RSS together, then run the real
`test/01_unit/compiler/cache/summary_store_v1_spec.spl` plus full-store boundary
regressions with an admitted test-capable pure producer. Verify paged/full
reads and snapshot/auth/token/corruption rejection before applying the patch.
Candidate compilation, full-store tests, p50/p95, steady RSS and optimizer
analysis are all **UNRUN**. There is no optimization or verification PASS.
