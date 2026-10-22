# First completed-HIR archive consumer adapter

Status: private source implementation and native acceptance fixture prepared;
uncompiled and unexecuted. No ordinary streaming, monomorphization, validator,
or MIR route is enabled by this change. It is a prerequisite for the completed
body lease design, not an established full CLI RSS repair.

## Actual consumer and retained route compatibility

`hir_typecheck_consumer_v1.spl` now has one shared implementation of the
existing per-module HM inference, HIR frontend rules, and visibility walk:
`collect_module_typecheck_receipt_v1`. The ordinary `run_typecheck_warn_pass`
continues iterating the same module keys and resolving severity once. It
appends each receipt's diagnostic messages in the previous order and publishes
warnings/errors through the existing `CompileContext` methods, preserving the
error count and error dump. No typecheck pass receipt/counter existed here and
none is removed. Advisory remains log-only; Warn publishes HM/visibility
warnings; Deny publishes HM/visibility errors. Frontend findings remain warnings
under both Warn and Deny, with the existing frontend feature policy intact.

The dedicated consumer does not import CompileContext, CompilerDriver,
monomorphization or driver orchestration. Its structured type-error formatter
is the existing implementation moved to `30.types/type_infer/format_error.spl`;
the original public source-loading API forwards to that same implementation.
The existing source-shape regression follows the new formatter owner while
also checking the preserved forwarding API. This avoids pulling unused
aggregate driver consumers into the independently executable lease fixture.

The new `cache/hir_body_typecheck_lease_v1.spl` calls that same complete-body
consumer after the existing owned-scope cache decoder. It does not use a
parallel simplified checker, a callback, signatures-only body placeholders,
or fabricated provider return values. All other configured validators and
aggregate consumers remain on their existing paths. This adapter is not a
reason to bypass the remaining whole-graph gates documented in the completed
HIR lease compatibility design.

## Archive identity and authority

An input records source path, the full frozen closure digest, entry ownership,
logical module name, current HIR header (codec plus compiler/source scope),
the exact supported `lowered-unresolved-v1` stage, and the selected canonical
runtime/provider authority receipt path and SHA256. Before every store or
lease the receipt is read as a bounded regular file without following links;
its actual bytes must match the pinned hash. Source bytes are rehashed through
the existing `hir_cache_key`; changed source, closure, producer, runtime
receipt, logical owner or semantic stage rejects rather than yielding a hit.

This does not replace authority admission. For bootstrap, the caller must first
use the existing stage2 admission and `phase2-runtime-capsule.shs` verification
of the sealed runtime authority and actual linked artifacts, and pass that
exact selected capsule receipt. An ordinary configured caller must use its
existing environment-variant/provider authority owner. A self-authored text
file or environment label is not positive runtime authority. The local hash
check protects the selected, already admitted receipt's immutable binding;
it does not independently authenticate every artifact named in that receipt.

Archive filenames additionally bind the encoded *complete* HIR digest and a
framed lowering-warning digest. Different bodies or warning sequences therefore
cannot overwrite the same content identity. The existing cache checksum,
stable decode, self-check and atomic publication gates remain in force. The
reader verifies decoded module path/name and the exact complete-body and
warning digests before running HM. No transformed body is written into the
pre-resolution namespace. Missing/corrupt frames are errors for this API, with
no automatic source fallback or partial success.

## Lifetime and failure edges

The archive writer owns a fresh encoding/publication scope. The input HIR is
borrowed and is neither promoted nor freed by that writer. Its only new escape
roots are source key, archive key, body digest, warning digest, and the cache's retained
diagnostic reason. The latter matters because an I/O error can construct a
dynamic `io-*` string. Scalar cache counters and fixed-size reject counters
do not allocate. The descriptor itself is constructed after scope end.

The reader initializes the persistent frontend identity outside scratch, refuses an occupied cache warning
owner, and refuses a nested scope. Complete decoded HIR, HM contexts, types,
symbols, frontend findings and visibility checker state remain scratch-owned.
File-backed identity reads and temporary hashes run inside the owned scope as
well, so a no-GC caller does not retain one authority receipt per lease.
The exhaustive success escape set is the diagnostic receipt's three text
arrays, cached lowering-warning text array, and retained cache diagnostic
reason. The result contains only those values, a scalar function count and the
already persistent body digest. Diagnostic spans/types are rendered before
promotion; no HIR graph, source parser, symbol table or inference context is
returned. The cache warning alias is cleared while paused before reclamation.

Misses and identity mismatches still close scratch. Scope pause/end or promotion
failure panics after cleanup and publishes no result. Promotion results are
collected separately so short-circuit evaluation does not skip a root. A
previous consumer's nonempty cache warning owner is not silently overwritten.
The consumer does not mutate a persistent CompileContext while scratch is live;
ordinary publication happens through the existing methods after collection,
and lease publication must happen after the transaction has returned.

This proves only the interface boundary by source inspection. Native promotion
of the concrete receipt representation remains an acceptance gate. The writer
does not reclaim previously promoted producer HIR. Full phase1 body release,
minimal declaration catalogs, aggregate validation adapters, advice mutation
persistence, disk-backed generic specialization worklists and MIR provider
adapters remain unfinished architecture work.

## Prepared native acceptance

`test/fixtures/compiler/hir_body_typecheck_lease/main.spl` has 31 counted positive
checks and distinct failure exits, with no SSpec objects inside a scope. It
parses/lowers an actual declared-bool function whose complete body returns text,
compares lease diagnostics to the ordinary shared consumer, checks Advisory,
Warn and Deny behavior, and reads diagnostic/warning values after scope end
and a second scope's 64 allocations. It checks real source-byte mutation and
restoration, producer/runtime/closure/stage mismatch, scope-theft refusal,
eight repeated leases, corrupt frames and absent complete-body archives.

The imported generic provider returns 43 for both i64 and text callers before
and after a completed lease. Its entire parsed/lowered generic module is
archived; the decoder must reproduce the full codec digest and actual function
count, not merely a declaration digest. These checks are not a leased
cross-module monomorphizer: that consumer still needs its own adapter. Their
native execution, including exact output `HIR body typecheck lease: 31 checks
passed` and exit0, is pending a parent-authorized serialized slot.

The fixture must run from its source repository root with a private cache and
the selected sealed authority already verified. Required runtime identity:
`SIMPLE_HIR_LEASE_RUNTIME_PROVIDER_RECEIPT` names that exact admitted receipt;
`SIMPLE_HIR_LEASE_RUNTIME_PROVIDER_DIGEST` is SHA256 of its real bytes. The
`SIMPLE_HIR_LEASE_CLOSURE_DIGEST` must be the recorded actual frozen full source
closure digest, never a hash of a fixture label. The
frontend cache scope must bind the actual executing fixture implementation
and source identity, and evidence must separately record the compiler producer
and fixture executable hashes. No seed/interpreter acceptance fallback is
permitted. No runtime or RSS improvement is claimed from source checks.
