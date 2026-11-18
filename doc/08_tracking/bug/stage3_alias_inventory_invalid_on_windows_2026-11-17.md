# Stage 3 compiler on Windows: every native-build fails admission with `directory-alias-inventory-invalid`

Status: OPEN, cause identified in `phase2_var_reassign_runtime_text_branch_lost_2026-11-17.md` (source workaround landed; confirmation by a rebuilt Stage 3 pending). Blocks Stage 3
self-compilation on Windows.

## Symptom
A Stage 3 compiler built by Phase 2 from commit c71fd7c6a75 (both LLVM and Cranelift
builds) rejects every `native-build` at admission with

    SCV-E-ADMISSION: directory-alias-inventory-invalid

including a hello world in a pristine worktree with no junctions. Phase 2 passes the
identical command in the same tree.

## Source location
Raised at `src/app/compiler_entrypoint/inventory_events.spl:858` on origin/release/1.0.0
(`aliases == nil` after `compiler_inventory_aliases_v1(root, source_roots)`; at the Phase 2
pin the same check is at `:758-760`). The function is
`src/app/compiler_entrypoint/inventory_aliases.spl:65` and has 26 `return nil` exits.

## Known facts
- `git ls-files --stage --cached --others --exclude-standard` listing: 103,000 lines /
  11.2 MB (under the 16 MiB cap); modes only 100644/100755/120000; no CR.
- It contains non-ASCII and quote/space paths, e.g.
  `test/fixtures/compiled_tool_protocol/protocol café.spl`,
  `test/fixtures/compiler/data/nogc_open_경로.txt`,
  `test/fixtures/io/phase1_directory_walk/space ' 한/third.txt`.
- All 46,431 per-file events before the alias step succeed.

## Candidate exits (not narrowed)
1. Parsing of the git listing (non-ASCII / quote / space paths, mode 120000 handling).
2. `scv_worktree_path_safe` rejecting non-ASCII paths.
3. Windows path identity calls `path_final_existing` / `path_entry_present`
   (imported at the top of `inventory_aliases.spl`).
4. Bounded process/file helpers (`process_run_bounded`,
   `file_read_regular_no_follow_bounded`) behaving differently in a natively compiled
   binary than in Phase 2.

## Does Phase 2's pin contain this code?
Yes. 18a1f28937c2 (merge of PR #9028, 2026-11-14, an ancestor of origin/release/1.0.0)
contains `src/app/compiler_entrypoint/inventory_aliases.spl` (same header and imports)
and the call at `inventory_events.spl:758`. `git diff 18a1f28937c2 origin/release/1.0.0`
shows `inventory_aliases.spl` unchanged; only `inventory_events.spl` changed (+135/-5).
So "Phase 2 passes" is meaningful: the same alias-inventory logic succeeds in Phase 2 and
fails in the Phase 2-built Stage 3, which points at a difference in how the code runs
(Phase 2 binary vs a natively compiled copy of the same source) rather than at repository
contents. This is a hypothesis; not confirmed.

## Status
Open. Cause: `phase2_var_reassign_runtime_text_branch_lost_2026-11-17.md` (native probe, 2026-11-18). Source workaround merged in 34d422e9a36; close once a Stage 3 rebuilt with it passes admission.
