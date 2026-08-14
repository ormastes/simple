# Compiler, loader, script, and cross-language performance detail design

## Report lifecycle and failure schema

The cross-language harness claims its report path before invoking any compiler,
replacing stale evidence with `profile_status: running`. Installed compiler and
Simple native/SMF invocations are bounded by `RUN_TIMEOUT`. Any post-init
failure preserves the original process status and appends exactly one terminal
receipt containing phase, tool, lane, numeric status, and `timeout` only for
status 124. Known Simple compilation failures stop immediately after the full
report header, before artifact or timing sections. `profile_status: success` is
written only after compilation, measurements, and the success-schema contract.

The shell harness keeps the existing retained-table schema. Byte execution is
`/usr/bin/time -f %M -o receipt timeout RUN_TIMEOUT env PERF_BYTE_SIZE executable`.
GNU time's Linux wait4 accounting over `timeout` is contract-tested for positive
fast-exit RSS, a known allocating child above a threshold, and nonzero bounded
timeout expiry. The command status, semantic receipt, and fixture timing are
checked before a row can be admitted; no PID polling is used.

`validate_samples_file` accepts exactly the requested number of positive
numeric lines and rejects every malformed or extra line. Byte fixture timing is
checked from its integer `elapsed_ms` receipt (`<1000` for 1 MiB and `<30000`
for 32 MiB); outer process wall samples remain in `wall_samples_ms` for p50/p95
comparison.

Resolver tests reset the existing cache, exercise repeated and caller-sensitive
misses, revisit both callers, and reset again. The failed-existence-probe gate
adds a deterministic 100 uncached versus 1000 retained comparison without a
timing counter. The baseline resets before every resolution and must report
100 uncached resolutions; the retained path resets once and must report one.
Both paths must resolve identically, baseline failed probes must be positive,
and `cached * 100 <= baseline * 10` is required.

`rt_file_exists_probe_begin()` exclusively acquires the idle gate, advances a
monotonic 63-bit generation (never wraps; overflow returns `-3`), resets
total/failed facade counters, and publishes accepting. `rt_file_exists()` first
admits an in-flight lease and captures that generation before touching the
filesystem; it records only under that lease after the facade result is known.
The disabled source path has one relaxed gate load; this is not an assembly or
cycle-count claim. `end(token)` validates the generation, atomically clears
accepting, drains admitted leases, and returns nonnegative `(total << 32) |
failed` (`failed <= total <= 0x7fffffff`). Negative values are errors. The
instrumented boundary is the facade only: this is explicitly
labelled **failed existence probes**, never syscall counts.

C and Rust native providers share that atomic protocol. The pure-Simple
interpreter provider is documented single-thread, fail-closed compatibility:
it uses the same pre-facade lease and captured-generation accounting, rejects
overlapping/stale windows with negative errors, and does not claim native atomic
or disabled-assembly performance.

The direct facade fixture is `/tmp` plus the current process ID and is rejected
if it already exists; the contract does not delete paths to manufacture a miss.
Pure-Simple default compiler routes mirror the i64 probe ABI in the text-extern
registry, LLVM declaration emitter and library translator, minimal SFFI, and
interpreter-call router.

## Packed-byte collection and capability design

Packed byte arrays are a representation specialization of the language array
contract, not a separate public collection. Index, slice, iteration, concat,
clone, equality, freeze, and byte-valued mutation retain packed storage.
Mutation is routed through the receiver/place owner: bare identifiers preserve
copy-on-write aliases, projected places rebuild and write back the root, and
frozen receivers reject mutation. A non-byte insertion widens exactly once to
the generic array representation.

The foreign boundary accepts packed bytes only through a descriptor carrying a
base pointer, byte length, and input-only access. The adapter holds the backing
value alive for the duration of the foreign call, validates offset/length before
exposure, scopes nested adapters independently, and invalidates the capability
when the call returns. No raw pointer is returned as a Simple value or stored in
process-lifetime state. Writable/output behavior requires a separate explicit
contract and is outside the current design.

## Module interactions and errors

The resolver owns cache keys and invalidation; `rt_file_exists` owns probe
accounting; collection/place owners own language mutation; the SFFI adapter
owns capability lifetime; the harness owns admission and measurement. Negative
probe results, frozen mutation, invalid descriptors, stale probe generations,
timeouts, provenance mismatch, checksum mismatch, and malformed samples all
fail closed at their owning boundary.

The architecture common to the requirement options is recorded in
`doc/04_architecture/compiler_loader_script_crosslang_perf.md`. It remains
decision-ready rather than accepted until the mandatory feature and NFR option
selection occurs.
