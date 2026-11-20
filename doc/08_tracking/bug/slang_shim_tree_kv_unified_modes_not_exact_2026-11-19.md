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

## Review fixes (2026-11-20, after-the-fact review of #10396)
- Mode 1/3 reuse is capped by a per-terminal `exact_upto` (prompt length minus the
  last token, rounded down to n_ubatch). Cells an owner produced by generation or a
  partial chunk are never reused by the exact modes. Contract test: 10-token prompt +
  6 generated tokens, follow-up matching all 16 cells reuses 8 (mode 2 reuses 16).
  Live: `slang_kv_tree_cache_live_spec.spl` "boundary" (digest equal to no-cache and
  reuse <= first prompt rounded down to 512).
- The CUDA first-micro-batch workaround now applies to the persistent tree context's
  first decode (throwaway full micro-batch on the request's own empty sequence).
  Contract test: short first prompt, offloaded load, no short first decode. Not run on
  a CUDA host.
- Mode 3 "no KV slot" fails fast (evicting other streams frees nothing); mode 1/2 keep
  evict-and-retry. Pinned owners are never evicted.
- The engine now fails the load when a non-default cache mode is refused; `slang_ggml_free`
  resets the mode; BUSY surfaces as `BackendError.Busy`; an abandoned request (closed
  without finishing) releases the context; `prefix_cache_configure` is refused while a
  tree request is active; statistic getters take `g_state_lock`.
- Documented, not changed: a piece-buffer overflow ends the tree sequence mid-generation
  (its prompt+decoded path is still inserted); media requests return INVALID in tree mode;
  mode 3 ignores the `cells` argument (n_ctx x 16 streams).
- The mock honours `kv_unified` and aborts on a partial `seq_cp` of a non-unified context.
- The contract test is NOT wired into a gate: it needs the pinned clang (about 3 minutes
  on this host) while the push tier targets under 20 s and the required check under a
  minute, and an extended-lane row needs a `must_check_gates.sdn` row plus an exact
  dispatch arm in `check-push-must-pass.shs`. Run it by hand:
  `sh test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs`.
- Correction: PR #10396 claimed the live tree spec passed 2/2, but that spec file was
  not in the merged head; it landed in #10437 with its own run log.
