# slang shim tree KV: unified-KV modes 1 and 2 are not byte-identical to no-cache greedy

Date: 2026-11-19. Status: mode 3 exact (default stays snapshot); modes 1/2 kept only as diagnostics.

Measured on Gemma-3-270m (CPU, llama.cpp 99b9548): with one unified multi-sequence
KV (`kv_unified=true`), shared-prefix reuse via `llama_memory_seq_cp` gives output
digests that differ from the no-cache baseline on branching/multiturn, even when
reuse is rounded to whole n_ubatch micro-batches (mode 1) and with a cache that
never inserts (earlier run). Position and seq ids of reused cells are correct (the
mock contract test asserts consecutive positions); the divergence follows the
attention shape (n_kv padded over all sequences). Mode 3 (`kv_unified=false`, one
stream per sequence, whole-sequence `seq_cp` then `seq_rm` tail, because partial
`seq_cp` asserts on non-unified KV) reproduces the no-cache digest in 6/6 cells
(see `test/05_perf/slang_kv_cache/README.md`, logs in `C:/dev/slang-logs/shimtree/`).

Also found: snapshot mode on Gemma-3 (SWA) records `restore_failures` 4-5 per run,
so snapshot yields no reuse there (still correct output). Gaps: single repetition,
no TTFT, no RSS; text only; tree contexts need `n_ctx x 16` cells in mode 3; modes
are exclusive with the physical paged lane. Requests stay serialised per model; a
second concurrent tree request gets SLANG_ERR_BUSY; no new lock (g_state_lock).

## Follow-up (not in this change)
Hybrid policy: use the snapshot on an exact-prefix hit (reuses every token, wins on
Qwen multiturn: 948 prefilled vs 2765) and the mode-3 tree for shared-prefix
branching (snapshot reuses nothing there). Also open: mode 3 copies the whole owner
sequence per hit; a live tree system spec (slang_kv_tree_cache_live_spec) was not
re-created after the worktree loss; max RSS and TTFT unmeasured.
