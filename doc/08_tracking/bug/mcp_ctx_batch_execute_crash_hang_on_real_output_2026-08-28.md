# `simple_ctx_batch_execute` crashes (`StrBytes`) or hangs on real command output

**Date:** 2026-08-28 · **Status:** FIXED (this change) · **Found by:** token A/B lane (`mcp_token_ab_REPORT.md` §2.2/§2.3)

## Symptom

The context-mode mimic completed toy input (`echo ...`) but never a real
workload. `find src -name '*.spl' | xargs wc -l` (884 KB) killed the server:

```
error: semantic: cannot iterate over this type: StrBytes([115, 114, 99, ...])
```

and a 30 KB spec log hung for ~18 minutes at ~17% CPU (killed). The original
plugin completed the identical five-command batch in 16.2 s.

## Root cause (three independent defects, all in `src/app/mcp/main_lazy_ctx_tools.spl`)

1. **Per-character loops over captured output.** `ctx_unescape_cell`,
   `ctx_unescape_json` and `ctx_tokenize` walked text with `for ch in s`.
   Real command output (`git log`, `grep` over a mixed-encoding tree) carries
   bytes that are not valid UTF-8; the runtime represents such text as
   `Value::StrBytes`, and the interpreter's for-in
   (`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs:563`)
   has no arm for it — hence the crash. This module runs interpreted inside
   the server (main.spl's JIT fallback drops the module), so the arm's
   absence is fatal in production even though the same loop works under JIT.
2. **Superlinear store handling.** Every `ctx_index_text` call parsed the
   whole `chunks.sdn` with the generic per-character SDN parser (to find the
   next id) and then re-read and rewrote the whole file; five commands over
   a multi-MB store re-parsed it ten times. Interpreted per-char cost measured
   at ~6.5 us/char: 4 MB per pass ≈ 30 s, times passes ≈ the observed hang.
3. **Search re-tokenized every chunk once per query**, building a full
   term-frequency dict per chunk per query (~3.6 us per token interpreted;
   a 5.6 MB store is ~1M tokens per query).

Memory was bounded only by the resource scope's default 1 MiB cap — a
truncate-first policy stricter than the plugin's 100 KB, silently.

## Fix

- Unescape via native `split("\\")` + segment walk; tokenizer via native
  `lower()` + one `replace` pass per separator (every separator becomes two
  spaces, so ` term ` occurrence counts via `split` are exact). No per-char
  loop remains on any data path; nothing iterates a `StrBytes`.
- Linear row reader (`split("\n")` + `index_of`) replaces the SDN parser;
  torn trailing rows and quoted cells handled. Store is append-only
  (`file_append_text`); the next id is a high-water mark in `stats.sdn`.
- BM25 over a prepared index: one store load + one normalization pass per
  handler call shared by all queries; tf = native whole-word count, dl = bytes.
- Explicit per-command capture cap enforced at the reader: default 8 MiB,
  `SIMPLE_CTX_CAPTURE_MAX_BYTES` env or `capture_bytes` param, hard max
  64 MiB; truncation marked inline and counted (`capture_truncations` in
  `simple_ctx_stats`).

Reproduce spec: `test/01_unit/app/mcp/ctx_batch_scale_spec.spl`.

## Still open (seed defect, not this change)

The interpreter for-in should accept `Value::StrBytes` (lossy, like every
other string method does in `interpreter_method/mod.rs:958`). Any other
per-char loop over process output in the tree will hit the same crash.

## Residual (separate, pre-existing runtime defect, intermittent)

During the post-fix A/B reruns, 2 of ~14 `simple_ctx_batch_execute` calls
stalled indefinitely in the SERVER process with the spawned `/bin/sh` child
already a ZOMBIE (`[simple-main] <defunct>`) — i.e. the runtime's bounded
process-wait (`finish_child_output_bounded`,
`src/compiler_rust/compiler/src/interpreter_extern/system.rs`) never returned
even though the child had exited, and the request's own 120 s wall budget
never fired. Both stalls hit a `grep|head` pipeline (w3); the identical call
completed in 0.4-2.7 s on every retry and in every standalone reproduction,
including against the same 9,729-chunk store. This is NOT the fixed defect
(no crash, no CPU burn, child exited): it looks like a child-reaping /
readers-finished race in the runtime wait loop under a loaded box. Filed here
as residual; needs its own reproduce effort at the seed level.
