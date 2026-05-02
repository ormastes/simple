# svllm

vLLM-like LLM serving engine for Simple / SimpleOS.

This repository is the **product** wrapping of svllm — the service binary,
deployment configs, and integration tests. The reusable library logic
lives in the main [`simple`](https://github.com/ormastes/simple) repo
under `src/lib/gc_async_mut/svllm/` and is pulled in when this repo is
checked out as a submodule at `examples/svllm/` in the main tree.

## Status

**Phase A1 — Model-loader baseline.** Stub only. The binary prints help
and exits. The real serving pipeline (KV cache, scheduler, batcher,
OpenAI-compatible API) lands in Phases A4–A6.

## Layout

```
src/bin/svllm.spl      # service entry point (A1: stub)
test/integration/      # TTFT / throughput benchmarks (A6+)
doc/                   # runbooks, deployment notes
```

## Design docs

Canonical design lives in the main `simple` repo:

- `doc/05_design/svllm/svllm_master_plan.md` — phased roadmap
- `doc/05_design/nvfs/svllm_requirements.md` — filesystem contract svllm asks for

## Build & run

From the main `simple` repo, once this is checked out as a submodule:

```sh
cd examples/svllm
bin/simple run src/bin/svllm.spl
```

## License

MIT — see [LICENSE](LICENSE).
