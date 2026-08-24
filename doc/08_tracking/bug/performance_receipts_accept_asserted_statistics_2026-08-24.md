# Performance receipts accept asserted statistics

Status: fail-closed; lane validators pending

`interpreter-startup-parity` and `rust-go-benchmark-parity` were routed through
the generic signed external-receipt validator. A signature authenticated the
reviewer, but no registry-owned code loaded raw timing samples, recomputed
statistics, proved equivalent work, or derived the threshold verdict. A
schema-correct signed file could therefore assert every acceptance marker.

The generic validator now rejects both gates explicitly. They remain textual
TODO rows and cannot be promoted until dedicated semantic validators exist.
Those validators must require canonical Stage 4 compiler authority, committed
semantic fixtures and oracles, complete raw samples, controlled environment
identity, independently recomputed order statistics, and a repository-defined
comparison rule.

For interpreter startup, cold and warm must both measure process launch—not
recursive-Fibonacci throughput—and must include Simple interpreter, Python,
Bun, and Go on the same host/run. Every timed Simple process needs exactly one
`requested=interpreter actual=interpreter fallback=false` receipt.

For Rust/Go benchmark parity, all three programs need runtime-fed equivalent
inputs and equal optimization barriers. Missing toolchains, too few samples,
mutable Markdown tables, self-reported percentiles, or checksum-only constant
work are not admissible evidence.
