# Cross-Language Startup and Compile Profile — 2026-09-03

## Authority

This is diagnostic macOS arm64 evidence. The candidate Simple executable is
pure-Simple but has no source-matched Stage 3/4 provenance receipt, so the fair
matrix correctly reports all Simple compile lanes as unavailable. No peer
number is used as proof of Simple parity.

## Fresh measurements

The fail-closed matrix ran five interleaved measured rounds after one warmup.
Times are p50 microseconds.

| Language | Process floor | Parse/check | Object/SMF | Native executable |
|---|---:|---:|---:|---:|
| Simple | unavailable | unavailable | unavailable | unavailable |
| C | 250000 | 250000 | 390000 | 410000 |
| Rust | 300000 | 440000 | 430000 | 470000 |
| Go | 240000 | 400000 | 380000 | 470000 |
| Python | 250000 | 240000 | n/a | n/a |

The exact raw samples, commands, hashes, versions, and RSS rows are retained
under `.simple/storage/evidence/perf/cross-language-compile/20260903T121440Z-82848/`.

An independent direct diagnostic of the existing Simple executable measured
`simple --version` at 72.081 ms p50 and 120.514 ms maximum across seven samples.
`/usr/bin/time -l` observed 10,813,440 bytes maximum RSS and approximately
146.5 million retired instructions. The same binary failed both `run` and
`compile` for the tiny fixture with generic errors, so no compile-time number
is accepted from it.

## Bottleneck decision

The current source fixes the wrapper delegation and lost-error defect, but the
binary predates that fix. Separate diagnostic native-build evidence reports a
1.32 second tiny build with approximately 1.3 seconds in linking. That artifact
contained unresolved stubs and is not correctness evidence, but its phase split
is sufficient to prioritize exact-identity linker/runtime reuse over rule-level
lint micro-optimization.

## Next valid comparison

Rebuild an admitted source-matched Stage 3/4 executable, then rerun:

```sh
SIMPLE_COMPILER=/path/to/simple \
SIMPLE_COMPILER_PROVENANCE=/path/to/simple.provenance.env \
sh scripts/check/profile-cross-language-compile.shs
```

Only complete rows from that run may support Go, Rust, C, or Python parity
claims.
