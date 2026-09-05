<!-- codex-research -->
# Compiler loader script cross-language performance: local research

## Scope and current evidence

This lane joins three related boundaries: pure-Simple module resolution,
interpreter packed-byte semantics/foreign calls, and the retained
cross-language performance harness. It does not treat Rust-seed execution as
self-hosted compiler evidence and it does not turn a source-contract audit into
a latency or RSS measurement.

The executable system contract is
`test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`; its manual mirror
is `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md`. The
current mirror is intentionally marked as a hand-maintained blocked summary,
not fresh docgen output.

## Code paths

### Loader resolution

`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` owns the
pure-Simple resolver caches. It uses a module-only fast cache for roots whose
resolution is caller-independent and a `(module_name, current_file)` cache for
relative imports. `module_resolve_cache_reset()` clears both caches and the
uncached counter. Failed-probe measurement stays below this layer at the
`rt_file_exists` facade so the resolver cannot mislabel probes as syscalls.

The Rust interpreter has the corresponding resolver in
`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`. The two
implementations need behavioral parity, but only the deployed pure-Simple path
can satisfy self-hosted performance admission.

### Failed-probe providers

`src/runtime/runtime.c` and `src/runtime/runtime_native.c` implement the native
generation/lease protocol. The runtime header exposes test-only counter seeding
under `SIMPLE_RUNTIME_TESTING`. The Rust provider is in
`src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs`, while the
pure-Simple interpreter adapter is in
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`.

The contract counts facade calls that return false. It is not an operating
system syscall count. A measurement window admits calls before filesystem work,
closes before draining them, rejects stale generations, and packs total/failed
counts into one nonnegative `i64`.

### Packed bytes and foreign boundaries

The interpreter represents byte-typed arrays as `Value::ByteArray` or
`Value::FrozenByteArray`; generic arrays remain boxed. Collection behavior is
distributed across `interpreter_helpers/patterns.rs`, `interpreter/place.rs`,
`interpreter_method/collections.rs`, and value clone/equality owners.
`interpreter_extern/sffi_array.rs` is the typed array boundary. The evidence
record `doc/08_tracking/bug/compiler_loader_packed_byte_evidence_gaps_2026-08-14.md`
records the now-closed concat/clone/equality and projected-place cases and the
remaining foreign capability lifetime/escape blocker.

The important invariant is representation transparency: index, slice,
iteration, concat, clone, equality, freezing, and byte-valued mutation must
behave like the language-level array contract while retaining packed storage.
Insertion of a non-byte value may widen once to the generic representation.
Foreign pointer access must be descriptor-bounded, input-only unless an
explicit output contract exists, scoped to one call, and unable to escape.

### Performance harness

`scripts/check/check-cross-language-perf.shs` owns compiler identity admission,
bounded subprocess execution, semantic receipts, retained samples, and report
schema. The peer implementations must perform equivalent work and checksums;
unavailable tools stay unavailable. The byte fixture is
`test/05_perf/bytes_push_1mib.spl`. Independent contract scripts under
`test/05_perf/profile_scripts/` check compile failure, provenance, retained
byte evidence, and report schema without claiming live performance.

## Existing evidence and gaps

- The C failed-probe lifecycle/selfcheck and retained harness source contracts
  have independent passing receipts recorded by the canonical plan.
- Focused packed-byte identifier/COW/removed/frozen, concat/clone/equality, and
  projected-place interpreter cases pass. PBL-03 remains incomplete because
  the pointer-returning foreign ABI cannot enforce call-scoped non-escape.
- A preserved admitted Stage 2 compiled the compiler tree; Build11 Stage 3
  currently exits 139 after parsing, so no self-hosted runtime row is admitted.
- Research and decision-ready architecture now exist. Selected requirements,
  selected NFRs, and accepted post-selection architecture remain absent;
  options are provided separately and require explicit user selection.

## Conclusions

Keep semantic owners separate: resolution/cache policy at the loader, probe
accounting at the file facade, packed representation at interpreter collection
owners, capability lifetime at the SFFI call boundary, and admission/reporting
in the harness. Evidence must name its layer. Stage 2/3 bootstrap diagnostics
can prove bootstrap progress, but cannot substitute for a later deployed CLI
performance measurement.
