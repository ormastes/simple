# slang

vLLM-like LLM serving engine for Simple / SimpleOS.

This repository is the **product** wrapping of slang — the service binary,
deployment configs, and integration tests. The reusable library logic
lives in the main [`simple`](https://github.com/ormastes/simple) repo
under `src/lib/gc_async_mut/slang/` and is pulled in when this repo is
checked out as a submodule at `examples/slang/` in the main tree.

## Status

**Resident serial engine through S3 request ownership.** The reusable engine can
hold one model, generate through separately owned request contexts, and reuse a
bounded set of exact-token prefix snapshots. Request handles are generation
checked and teardown refuses active requests. Execution is still advanced by
one serial owner: paged KV, continuous batching, spill/transport, and parallel
request advancement are not implemented.

## Layout

```
src/bin/slang.spl      # product service entry point
test/02_integration/      # TTFT / throughput benchmarks (A6+)
doc/                   # runbooks, deployment notes
```

## Design docs

Canonical design lives in the main `simple` repo:

- `doc/05_design/slang/slang_master_plan.md` — phased roadmap
- `doc/05_design/nvfs/slang_requirements.md` — filesystem contract slang asks for

## Build & run

From the main `simple` repo, once this is checked out as a submodule:

```sh
cd examples/slang
bin/simple run src/bin/slang.spl
```

## License

MIT — see [LICENSE](LICENSE).
