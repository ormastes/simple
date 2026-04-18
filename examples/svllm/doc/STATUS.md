# svllm — Phase Status

| Phase | Status | Notes |
|---|---|---|
| A1 Model-loader baseline | skeleton only (here) | real work in main simple repo |
| A2 Packer CLI (safetensors → tensor_pack) | pending | will live in main repo as `src/app/svllm_pack/` |
| A3 Streaming loader + pinned DRAM | pending | |
| A4 Paged KV cache + paged attention | pending | |
| A5 Scheduler / worker / executor / engine | pending | |
| A6 HTTP API (OpenAI-compatible) | pending | product binary here (`src/bin/svllm.spl`) |
| A7 Sleep/wake residency | pending | |
| A8 LoRA adapter hot-load | pending | |

Filesystem requirements doc (consumed by the parallel nvfs track) lives at `doc/05_design/nvfs/svllm_requirements.md` in the main simple repo.
