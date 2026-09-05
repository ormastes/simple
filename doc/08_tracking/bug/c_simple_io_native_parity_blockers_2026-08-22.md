# C/Pure-Simple native I/O parity blockers (2026-08-22)

## Scope

The canonical harness is
`test/05_perf/io_parity/run_io_parity_benchmarks.shs`. It compares identical
4 MiB fixtures and iteration counts for whole-file text reads, mmap-to-text
reads, and explicit-offset 4 KiB writes. Every measured sample must match byte
counts and checksums; append samples must also match the output SHA-256. Seven
alternating warm samples are configured to report p50, nearest-rank p95, and
maximum RSS. The harness never falls back to interpreted execution.

## Current blocker

The final host attempt used:

```sh
SIMPLE_BIN=bin/simple IO_PARITY_MIB=4 IO_PARITY_ITERS=8 \
IO_PARITY_SAMPLES=7 \
bash test/05_perf/io_parity/run_io_parity_benchmarks.shs
```

It failed closed before sampling. The deployed compiler identifies itself as a
Rust bootstrap seed. Its direct native compiler rejects 32 transitive functions
from the typed `FileHandle`, environment, mmap, and string surfaces as requiring
the interpreter (`TryOperator`, `PatternMatch`, or `CollectionOps`). The
Pure-Simple `native-build` path was also tried once after narrowing the source
closure from 40 modules to 13; it fails in the current compiler on missing
`module_surface_projected_type_shape`. Neither failure is a benchmark-source
diagnostic, and neither may be converted into an interpreter performance row.

Consequently there is no post-change native p50/p95/max-RSS row and no native
performance-parity claim. Re-run the exact command above only after the admitted
Pure-Simple Stage 4 compiler is deployed and the missing projected-type-shape
owner is present.

## Correctness evidence available on this host

Rust-seed interpreter execution matched the C oracle for all observable fields:

- contract: missing-file rejection, 11-byte partial read, EOF, exact read, and
  exact-short rejection;
- `read_text`: 8,388,608 bytes and checksum 690,333,126 for two 4 MiB reads;
- `mmap_text`: 8,388,608 bytes and checksum 690,333,126;
- `append_at`: 8,192 bytes, checksum 674,762, and identical output SHA-256
  `4377811194051e9cfa41699dbdd48da7665a7c2114861992a763dd6e81d74547`.

The isolated C policy denominator is nonzero and complete: one decision, six
conditions, 12 compiler branches, 100% executed and 100% taken at least once.
The Simple seed records the policy decision at 100% but emits no condition rows,
so the requested six-condition percentage remains unavailable on this binary.
The mutation overlay does bite: changing the accepted partial length from 11 to
12 makes the dedicated scenario fail.

## Allocation/work model

- `read_text`: both implementations open, allocate one full-file result, read,
  checksum every byte, and close per iteration.
- `mmap_text`: C maps, copies to a heap text buffer, checksums, unmaps, and
  closes. The typed Simple owner maps into managed text and `.bytes()` creates a
  byte array for the same checksum. This extra managed conversion is retained
  and must be visible in native latency/RSS rather than hidden by a byte-count
  shortcut.
- `append_at`: both implementations build one 4 KiB chunk and loop explicit
  offset writes. The prior Simple-only bulk-repeat runtime primitive is gone.

The typed Simple surface allocates managed results while C uses explicit heap or
stack storage. That is language/runtime cost, not identical allocator behavior;
the harness claims identical observable work and reports RSS rather than
describing the paths as raw-syscall parity.
