# Domain Research — Demand-Driven Compilation

## Go

Go compiles one package at a time and emits object/archive data containing exported type information. Its unified export representation is indexed so imported declarations can be decoded lazily; downstream packages normally consume direct-import compiled outputs rather than dependency source trees. Generic and inlineable bodies are included only where downstream compilation may need them.

Design implication: SMF package metadata should be indexed by symbol and section, support direct random access, and provide sufficient summaries for direct importers without opening source.

## Ninja

Ninja obtains speed by persisting a simple dependency/action graph, moving policy decisions into graph generation, running independent edges in parallel, recording command identity, compacting discovered dependencies, supporting dynamic dependencies, and limiting expensive work with pools.

Design implication: the Simple scheduler should consume a precomputed package/action graph, update dynamic import edges after header parsing, and avoid policy/search work on warm builds.

## ccache and Go build cache

Compiler caches key outputs by compiler inputs and options, support concurrent processes, and separate cache correctness from a persistent daemon. A daemon may coordinate work but must not be the only owner of reusable results.

Design implication: action IDs include compiler/target/options/SMF schema/snapshot/dependency interface digests. Published SMFs and objects are immutable; daemon memory is disposable.

## LLVM ORC

ORC models lazy definitions as materialization units. Symbol lookup triggers compilation, concurrent requests synchronize through the lookup, and temporary stubs are replaced after materialization.

Design implication: Simple may expose a virtual import/symbol wrapper, but the wrapper is an explicit state machine and synchronization point. It may enter MIR only after successful materialization.

## CPU and GPU parsing

Lexing benefits from chunked reads, ASCII classification tables, vector delimiter/newline scanning, and parallel parsing of independent files. GPU transfer and dispatch overhead usually makes ordinary source parsing unsuitable unless very large generated inputs demonstrate a measured crossover.

## Sources

- Go compiler README and unified export-data design: https://go.dev/src/cmd/compile/README
- Go package compiler contract: https://go.dev/src/cmd/compile/doc.go
- Ninja manual: https://ninja-build.org/manual.html
- ccache manual: https://ccache.dev/manual/latest.html
- LLVM ORC v2 lazy materialization: https://llvm.org/docs/ORCv2.html
