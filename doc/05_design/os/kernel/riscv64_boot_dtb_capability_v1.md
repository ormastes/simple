# RV64 Boot DTB Capability V1 Detail Design

## Contract

- Input boundary: scoped loan `(observed_hart, dtb_physical_address)`.
- Owner: `os.kernel.boot.riscv_noalloc_dtb_capability`.
- Commit: bounded copied scalars only; fallback is initialized before parsing.
- Consumers: `hal_smp` and `hal_cache` expose constant-time reads.
- No allocator, text construction, dynamic arrays, `Option`, `Result`, raw
  runtime alias, C, or Rust is used by the production capability.

## Admission rules

The header must be FDT v17+ with compatible version <=17, use non-overflowing
physical arithmetic, remain within 40 bytes..2 MiB, and have in-range,
non-overlapping structure and strings blocks. Only known FDT tokens are
admitted; the single root must close before `FDT_END`; nesting is capped at
32. The reservation list must reach a bounded zero/zero terminator without
overlapping metadata. `/cpus` must declare address cells 1 or 2 and size cells
0 exactly once before CPU children. Each enabled immediate `cpu*` child
must have a correctly sized unique `reg`, and capacity must not exceed 32.
Logical 0 is swapped to the hart ID observed by the boot entry; absence of that
hart rejects the census.

Status and ISA properties require one terminating NUL and no embedded NUL.
Zicbom is enabled only if every enabled CPU has the exact underscore-delimited
`zicbom` token and every such CPU reports the same nonzero power-of-two block
size. Disabled CPUs do not participate in either intersection.

## Failure and coverage

Any malformed range, token, depth-zero property, missing/duplicate/late cell
width, duplicate relevant CPU property, missing/duplicate hart, capacity
overflow, overlap, missing root/END, malformed property string, missing observed
hart, token mismatch, or invalid/inconsistent stride
returns the precommitted one-hart fallback. Encoded-DTB tests cover positive and
negative decisions, including independent truth-value changes for enabled
status, exact-token boundaries, uniqueness, power-of-two, consistency, and
malformed header conditions. Source-level review covers fixed storage, bounded
loops, and prohibited allocation/runtime surfaces. These are simulated-MMIO and
source decision checks; live SBI/CLINT execution is not claimed here.
