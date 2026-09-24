# Feature: current-source macOS Apple Silicon Stage4 deploy

## Raw request

`$sp_dev complete macos stage4 deploy remaining.....md complette andpush and update local dploy`

## Acceptance criteria

- AC-1: Build from current source on `aarch64-apple-darwin` with the canonical bootstrap path and `SIMPLE_NO_STUB_FALLBACK=1`.
- AC-2: Resolve every newly exposed build blocker with retained pre-fix evidence and a canonical bug record.
- AC-3: Produce one exact Stage4 full-CLI candidate without failed-file or stub-fallback markers.
- AC-4: The exact candidate passes CLI sanity, source checking, redeploy gate, and essential-tools smoke.
- AC-5: MCP and LSP startup/request smoke checks pass against the accepted candidate.
- AC-6: Deploy atomically to the local Apple Silicon release path while retaining a rollback artifact.
- AC-7: Installed and accepted-candidate hashes match and the installed CLI passes post-deploy sanity.
- AC-8: Update the macOS Stage4 plan and applicable expert/process evidence without overwriting prior history.
- AC-9: Push only this isolated lane through the protected-branch PR workflow and verify the remote result.

## Scope exclusions

No version bump or release tag; no Rust-seed fallback; no unrelated dirty-main
work; no claim that another architecture is deployed.

## Phase

blocked-after-capped-verification

## Evidence log

- Two conflicting orphan builds were stopped; neither produced a candidate.
- Canonical build cycle 1 exposed 23 duplicate `rt_simd_*` link definitions.
- Canonical cycle 2 passed seed/runtime construction, then Stage2 and a direct
  Stage4 attempt exposed the same 374-unit exact-symbol resolution failure.
- Closure-value native/interpreter probe passes with output `15`.
- The exact-symbol focused LLVM regression passes; final Stage4 remains pending.
- Final canonical cycle rebuilt all Rust authority artifacts and reduced the
  Stage2 failure from 374 units to 3 files. Residuals are one unresolved
  `virtual_source_store` call and two genuine `str.split_whitespace` calls.
- The mandatory three-cycle cap stopped further edits. No Stage4 candidate was
  produced, so deployment was correctly left unchanged.
- Continuation 2026-09-08: `split_whitespace` imports cleared both original
  sites; canonical in-place `Array.remove` cleared the newly exposed
  `Array.remove_at` failure. The imported-trait regression test passed (1/1).
- Continuation cycles reduced Stage2 from 3 files to 2 and then 1. A generic
  defining-module facade still lowers `virtual_source_store` as a bare static
  call because per-file native HIR lacks imported/generic constraint trait-slot
  metadata. The third-cycle cap stopped further retries. No candidate exists;
  deployment and essential-tool gates remain pending.
