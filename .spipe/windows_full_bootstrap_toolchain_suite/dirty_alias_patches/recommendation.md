# Dirty alias semantic triage: assigned group

Scope is exactly the four rows in `../dirty_alias_owner_decision.md`: `.codex/commands/sp_dev.md`, `examples/05_stdlib/spipe/.codex/commands/dev.md`, `examples/05_stdlib/spipe/.codex/commands/sp_dev.md`, and `src/app/lint/main.spl`.

## Recommendation

Restore all four Git mode-120000 leaves to their recorded link blobs. Do not merge leaf text into the canonical targets. Each dirty ordinary leaf is a byte-for-byte historical target snapshot whose blob appears in target history; the current target is newer and tracked. No unique leaf-only work was found.

Apply only after owner authorization and a recoverable backup of the four ordinary files. Re-inventory hashes immediately before restoration because this review is read-only and concurrent work may change them.

## Evidence

| leaf | HEAD link text | dirty blob | classification | canonical evidence |
|---|---|---|---|---|
| `.codex/commands/sp_dev.md` | `../skills/sp_dev/SKILL.md` | `d888e1b148e5634cca36f2361a1768ca83ee37fe` | stale and conflicting | Current target adds bug-ownership rules at line 18, protected self-review at line 63, CUDA trust policy at line 371, and multilingual-font policy at line 717. The leaf also retains superseded must-check text and an obsolete completion-recorder sentence. Its blob is present in target history at transition commit `82098baaa450bc7d300a2ad674c6677a9a27b69c`. |
| `examples/05_stdlib/spipe/.codex/commands/dev.md` | `../skills/dev/SKILL.md` | `6109757850e76a0e418d19ac4e39cff2cd49f502` | stale, no unique edit | Current target adds the protected-PR handoff at line 23. Dirty blob is the historical pre-addition target and is identified by target history at `82098baaa450bc7d300a2ad674c6677a9a27b69c`. |
| `examples/05_stdlib/spipe/.codex/commands/sp_dev.md` | `../skills/sp_dev/SKILL.md` | `36d6d5fdf949c264047bd6cb355c85b38d549a7d` | stale, no unique edit | Current target adds the protected-PR section at line 22. Dirty blob is the historical target snapshot identified at the same transition commit. |
| `src/app/lint/main.spl` | `../../compiler/90.tools/lint/main.spl` | `6211849cc02fad67270737844b97c1d00cd461b6` | stale; would hide current public surface | Current target adds `export use compiler.tools.lint._LintMain.legacy_adapter.*` at line 42, committed in `e0fa5ef45e21dbf85ac045f853ba0bcc18fd6f52`. The leaf exactly matches the preceding target blob. |

All four index entries are mode `120000`; the dirty working-tree objects are ordinary files. Current source/test imports use `compiler.tools.lint.main`, making the canonical lint facade—not the stale app-path copy—the active API owner.

## Safety boundary

These proposals intentionally contain no commands that overwrite or delete the leaves. They specify the desired index-compatible end state only. Materialization should run later through the receipt producer after all dirty-alias owner decisions are approved.
