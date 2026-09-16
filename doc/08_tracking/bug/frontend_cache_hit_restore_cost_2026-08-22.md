# Front-end cache HIT restores cost most of a parse (interpreted per-line decode)

- **Date:** 2026-08-22  **Status:** FIXED (decoder inlining); native bulk decode still open
- **Area:** `src/compiler/10.frontend/core/flat_pool_codec.spl` (`flat_pool_dec_*`)
- **Follows:** `frontend_shard_and_cache_hit_cost_2026-08-21.md` ("decode is still 69% of a hit")

## Symptom (run11b, 8 `--hir-shard` children, cache all hits)

Children advanced through `parse N/687` at 1.4-2.4 s/module mean (log `dt=`),
with `zca_rows.spl` 25-35 s and `hir_codec.spl` (1.79 MB entry, 573k lines)
598 s in one child. A parse of the same files costs 22-31 s, so a HIT saved
little, and every one of 8 children pays all 687 restores.

## Profile (standalone hit, `SIMPLE_PARSE_PHASE_PROFILE=1`, seed `e5f12c93`)

`hir_codec.spl`: init 0.5 s, **restore 30.9 s**, bridge 7.5 s. Restore by
stage: decl 0.9 s, **expr 17.5 s (383k lines)**, stmt 2.2 s, type 3.6 s. Cost
is linear (~45 us/line): each element went through `next()` -> `next_i64()`
-> `flat_pool_parse_i64()` (three interpreted method calls plus the `ok`
checks), and each AST node's list pool (`expr_args`, `expr_stmts`, ...) paid a
fresh inner decode call and `next_len()` per node. Not lock contention (no
locks on the read path), not `.fpc` I/O (load 18 ms), not quadratic push
(measured linear). The in-child 598 s outlier vs 31-39 s standalone for the
same entry is load (8 children x 2.8 GB RSS on a 125 GB box at load 30+), not
a different mechanism; `zca_rows.spl` in-child (25-35 s) matched standalone
(23.7 s).

## Fix

`flat_pool_dec_i64/bool/text` and `flat_pool_dec_i64_list/text_list` read
`r.lines` directly with a local cursor, bounds-checked exactly as
`next_len()`; `r.pos` / `r.ok` are updated once per pool. Same bytes, same
values (roundtrip spec 17/17, `check-hir-codec-roundtrip.shs` binary
identical, sharding spec byte-identical). Microbench 300k i64: 11.4 s -> 2.6 s.
Real entries (restore phase): `hir_codec.spl` 24.2-30.9 s -> **5.7 s**;
`zca_rows.spl` 16.6 s -> 8.2 s; `llvm_backend.spl` 2.0 s -> 0.7 s.

Pinned by `flat_pool_codec_decode_cost_spec` ("decodes i64 and nested list
pools without a per-element reader call", 300k + 60k lists < 6 s; pre-fix
measured 11.4 s for the i64 half alone) plus a truncated-inner-list case.

## Still open

- The bridge (`flat_ast_to_module`, 7-11 s on hir_codec) and `blob.split`
  are now the next cost; a runtime-level bulk decoder would remove the
  remaining interpreted per-line cost entirely (needs a seed change).
- Each HIR child restores ALL 687 modules although it lowers ~1/8 of them;
  frozen surfaces are not persisted (see `hir_shard_children_reparse_closure_2026-08-22.md`).
- run11 parse shard 6/8 died silently; its claimed modules were orphaned and
  every HIR child re-parsed them (claims should be reclaimable).
