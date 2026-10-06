# Static conditions and dependency pruning: external prior art

Researched 2026-10-06. The user-supplied Simple proposal is the selected design;
these sources inform boundaries and tests, not a replacement requirement choice.

## Configuration predicates before compilation

Rust documents configuration predicates and conditional source inclusion with
`cfg`/`cfg_attr`, alongside `cfg!` for obtaining a Boolean value. This distinction
is useful when reviewing Simple's structural `@when` versus ordinary runtime
`if`: a Boolean expression alone must not be assumed to exclude dependency
resolution. Simple's typed domains, Boolable semantics and unknown-member
diagnostics remain its own selected contract.

Source: [Rust Reference: conditional compilation](https://doc.rust-lang.org/reference/conditional-compilation.html).

## Configuration-dependent dependency edges

Bazel's configurable attributes select attribute values using configuration
conditions. Configuration-aware queries are relevant to understanding selected
dependencies. For Simple, this supports retaining the symbolic dependency graph
separately from a target-selected closure. Cache identities and diagnostic traces
must distinguish those two artifacts rather than treating one host's selected
graph as a portable summary.

Source: [Bazel: configurable build attributes](https://bazel.build/configure/attributes).

## Cheap file-level exclusion

Go build constraints provide declarative Boolean conditions controlling file
participation. This is useful prior art for an inexpensive file gate. Simple's
symbol-level TLDR dependency extraction, AOP/coherence roots and condition phase
checking go beyond file selection and need their own completeness proofs and
tests. Go's build speed is not evidence of Simple's future performance.

Source: [Go command: build constraints](https://pkg.go.dev/cmd/go#hdr-Build_constraints).

## Resulting review obligations

Keep target configuration distinct from the host running the build; preserve
portable symbolic guards; separate structural exclusion from value evaluation;
test that false guarded imports cause zero resolver probes; retain uncertain
dependency/effect coverage; and measure actual avoided work, latency and memory.
These are inferences for this design, not claims that the cited systems provide
Simple's proposed typed-domain or TLDR contracts.
