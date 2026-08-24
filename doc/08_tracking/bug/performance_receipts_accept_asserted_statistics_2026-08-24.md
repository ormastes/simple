# Performance receipts accept asserted statistics

Status: startup source fixed; Rust/Go lane validator pending

`interpreter-startup-parity` and `rust-go-benchmark-parity` were routed through
the generic signed external-receipt validator. A signature authenticated the
reviewer, but no registry-owned code loaded raw timing samples, recomputed
statistics, proved equivalent work, or derived the threshold verdict. A
schema-correct signed file could therefore assert every acceptance marker.

The generic validator rejects Rust/Go benchmark parity explicitly. Interpreter
startup is routed through its dedicated raw-sample and canonical Stage 4
validators. Both remain textual TODO rows until real qualifying evidence is
produced; neither can be promoted by generic PASS labels.
Those validators must require canonical Stage 4 compiler authority, committed
semantic fixtures and oracles, complete raw samples, controlled environment
identity, independently recomputed order statistics, and a repository-defined
comparison rule.

For interpreter startup, `check-interpreter-startup-samples.shs` makes one
linear pass over 400–8000 ordered raw rows, then performs eight fixed-width
lexical sorts. It recomputes nearest-rank p50/p95 and requires Simple to be
strictly below Python, Bun, and Go for both fresh-before-prime and warmed
process launches. Every timed Simple process has exactly one
`requested=interpreter actual=interpreter fallback=false` receipt. The outer
checker binds the exact committed compiler/provenance copies to a live release
candidate and runs the complete canonical Stage 3/4 verifier.

For Rust/Go benchmark parity, all three programs need runtime-fed equivalent
inputs and equal optimization barriers. Missing toolchains, too few samples,
mutable Markdown tables, self-reported percentiles, or checksum-only constant
work are not admissible evidence.

Focused startup-oracle evidence passed three implementation cycles; the final
cycle was 4.69 seconds wall time with 4.75 MiB peak RSS. Subsequent independent
review found that mutually consistent output hashes were not yet tied to the
committed oracle bytes. The source now enforces that binding and adds the exact
forgery regression. The mandatory three-cycle cap prevented a fourth full
rerun, so post-review source checks and reviewer PASS are retained while that
new mutation remains pending its next-session execution.
