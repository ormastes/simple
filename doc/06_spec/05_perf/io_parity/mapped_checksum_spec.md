# I/O parity mapped checksum

This performance contract verifies that the Simple mmap benchmark sums the
same bytes as its scalar oracle while reducing calls through the canonical raw
pointer boundary.

## Preconditions

- A current pure-Simple Stage 4 test runner is required for accepted execution.
- Hosted raw allocation and aligned `i64` plus byte reads must be available.
- The production benchmark fixture is 16 MiB and runs 64 iterations.

## Workflow

1. Allocate a 32-byte aligned buffer and fill four eight-byte regions with
   distinct repeated byte values.
2. Confirm invalid addresses and empty inputs return zero.
3. Check lengths 0 through 17 from offsets 0 through 7, covering empty input,
   every unaligned prefix, aligned word reads, and every possible tail.
4. Check the deterministic raw-read call counts for aligned and unaligned
   inputs.
5. Confirm the production fixture drops from 1,073,741,824 scalar boundary
   reads to 134,217,728 packed reads, an exact 8x reduction.

## Expected results

- All 144 offset/length combinations match the independent byte-sum oracle.
- Aligned eight-byte regions require one raw read each.
- Unaligned prefixes and short tails use byte reads only where required.
- No C or Rust implementation replaces the Simple checksum logic.

## Limitations

The call-count reduction is structural evidence, not a runtime speed claim.
Cold/warm latency, throughput, and RSS remain blocked until the canonical I/O
parity runner is executed with a current admitted Stage 4 compiler.

## Executable source

`test/05_perf/io_parity/mapped_checksum_spec.spl`
