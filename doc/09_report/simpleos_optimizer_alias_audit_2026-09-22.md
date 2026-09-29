# SimpleOS optimizer alias preservation audit — 2026-09-22

## Verdict

**OPEN / target proof blocked.** The Dict-based optimizer implementation remains
enabled and its production MIR analyzer passes the restored alias/count scale
guard. A hosted run does not reproduce the old implementation's SimpleOS-only
tagged-nil failure, and the live filesystem compiler QEMU workflow is not wired.

## Immutable inputs

- candidate tree: `4b6aec391bfdfbf5b43bfbb056ff28e8cfef6a7d`
- old implementation tree: `001200cade2` (`5d614ae9904^`)
- executing compiler: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
- executable SHA-256: `11a4cb54e47f29da3a39eda169c656af856221f1f965792a411a0ac95b05c6b3`
- test: `test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl`

## Behavioral evidence

Both trees executed 21 examples with zero failures. The restored case calls
`analyze_var_reassign_blocks` directly on 768 real MIR instructions: 256 first
definitions, 256 aliasing copies, and 256 redefinitions. Both implementations
returned `reassignment_count=256`, safe SSA decisions, and identical ordered
JIT facts. Therefore this is output-equivalence and scale coverage, not a
red-before crash reproducer.

## Diagnostic resource samples

| tree | wall time | host max RSS | result |
|---|---:|---:|---|
| old implementation | 6.48 s | 302,960 KiB | 21/21 pass |
| Dict candidate | 2.25 s | 350,760 KiB | 21/21 pass |

These are one-shot whole-test-process observations with different source
closures. They are not an admitted performance pair and support no regression
or improvement claim. Host process RSS is also not SimpleOS guest compiler RSS.

## Required target A/B

Use identical 12-vCPU, fixed-memory QEMU envelopes and immutable parent and
candidate guest images. In each guest, run the filesystem compiler route
`compile --emit-llvm /HELLO.SPL -o /HELLO.LL`; bind image, compiler, source, and
artifact digests; reject serial `local_count_index` or `CR2=0x8`; and verify the
produced program prints exactly `Hello from SimpleOS`. Collect guest compile
latency and guest high-water memory separately from host QEMU RSS, with a warmup
and seven measured samples.

Current blocker: `check-simpleos-compiler-filesystem-qemu.shs --arch=x86_64`
exits 3 with `x86_64-compiler-filesystem-guest-workflow-not-wired`.
