# Binary-size parity receipt accepts unchecked metrics

Status: source fixed; live qualifying receipt pending

`binary-size-go-parity` currently uses the generic external receipt validator.
A trusted signature authenticates its PASS labels, but no registry-owned code
loads the measured binaries, recomputes their hashes and exact byte counts, or
checks `Simple <= Go`. Malformed or contradictory numeric claims can therefore
reach the signature boundary without a lane-specific metric verdict.

The retained cross-language profiler is not substitute evidence: its relevant
outputs are not stripped, sizes are humanized, artifact hashes and semantic
oracle binding are absent, and its Go hello size row reuses the Fibonacci
artifact. This gate remains TODO until a fresh qualifying bundle is produced.

Acceptance requires a narrow validator over committed stripped binaries,
semantic sources/oracle, admitted pure-Simple Stage 4 compile trace, canonical
positive integers, matching ELF identity, and an independently recomputed
`simple_bytes <= go_bytes` result. Rust-seed paths/processes, compressors,
malformed numbers, identity drift, or summary-only PASS claims must fail.

The source fix adds a registry-owned validator that recomputes the committed
binary hashes, exact bytes, ELF identity, semantic bindings, and parity result.
The compiler and canonical provenance copies must match a live absolute
release candidate on the producer host, where the complete canonical
`stage4_verify_candidate_provenance` chain is executed. A signed fixture that
labels `/bin/true` as Stage 4 is rejected. The gate intentionally remains TODO
until a real admitted candidate produces the complete receipt.

Focused evidence on 2026-08-24 reached the new rejection case but the overall
shell contract stopped later in its malformed-number mutation loop because the
fixture used `/` as both replacement data and `sed` delimiter. That harness
defect is corrected to use `|`. The three-cycle session cap prevented another
full rerun; final verification therefore remains pending rather than inferred.
