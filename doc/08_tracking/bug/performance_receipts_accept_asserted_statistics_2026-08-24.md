# Performance receipts accept asserted statistics

Status: source fixed; qualifying measurements pending

`interpreter-startup-parity` and `rust-go-benchmark-parity` were routed through
the generic signed external-receipt validator. A signature authenticated the
reviewer, but no registry-owned code loaded raw timing samples, recomputed
statistics, proved equivalent work, or derived the threshold verdict. A
schema-correct signed file could therefore assert every acceptance marker.

Both gates are routed through dedicated raw-sample and canonical Stage 4
validators. They remain textual TODO rows until real qualifying evidence is
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

For Rust/Go benchmark parity, the committed Simple/Rust/Go programs read the
same input file at runtime and retain an observable black-box result after
100,000 identical LCG operations. The oracle requires 50–1000 rotated,
trial-interleaved samples per language, exact output/input/operation receipts,
fixed-width timing and RSS, recomputed p50/p95/max-RSS, and `Simple <= Rust &&
Simple <= Go` at both latency quantiles. The production wrapper binds the exact
committed compiler/provenance to a live canonical Stage 4 chain. Missing
toolchains, mutable Markdown tables, self-reported percentiles, or
checksum-only constant work are not admissible evidence.

The Rust/Go focused oracle passed its third cycle in 2.89 seconds with 4.75 MiB
peak RSS. Final identity review then separated the Stage 4 compiler hash from
the timed Simple executable and added exact committed Simple/Rust/Go executable
blobs plus ELF target matching, including binding ELF class and machine to the
declared environment architecture. The session cap prevents a fourth full
rerun; that post-cycle binding is source-reviewed and remains pending
next-session execution rather than being inferred green. Rust and Go fixture
programs compiled and produced the oracle output. The dedicated sparse
worktree contained neither `bin/simple` nor a release Simple executable, so the
Simple fixture check and Simple OptimizerPlugin pass were not run; no Rust-seed
fallback was used. Those checks remain pending with the qualifying Stage 4
measurement rather than being claimed from unavailable tooling.

Focused startup-oracle evidence passed three implementation cycles; the final
cycle was 4.69 seconds wall time with 4.75 MiB peak RSS. Subsequent independent
review found that mutually consistent output hashes were not yet tied to the
committed oracle bytes. The source now enforces that binding and adds the exact
forgery regression. The mandatory three-cycle cap prevented a fourth full
rerun, so post-review source checks and reviewer PASS are retained while that
new mutation remains pending its next-session execution.
