# Modified symlink placeholders block strict Windows bootstrap materialization (2026-10-22)

## Symptom

After resolving the receipt-root policy block, the Windows strict
materializer failed startup with:

```
materialize-symlinks-windows: FAIL (ordinary or tampered placeholder bytes: .claude/commands/arch.md)
VERDICT — ABORTED: stage=starting exit=1
```

## Root cause

37 git-tracked symlinks under `.claude/commands/**`, `.codex/commands/**`,
`bin/mail`, and `examples/05_stdlib/spipe/.codex/commands/**` had their
on-disk placeholder bytes replaced with full file content (each under the
materializer's 4096-byte placeholder size guard, so the size heuristic
classified them as placeholders and the byte comparison against the HEAD blob
failed). On a `core.symlinks=false` checkout a symlink is a regular file
holding the target text; the strict receipt path treats any size-plausible
placeholder whose bytes differ from the HEAD blob as tampered.

For every affected path the replacement content was byte-identical to the
content already present at the symlink's resolved target (e.g.
`.claude/commands/arch.md` content == `.claude/skills/arch.md` content), so
the working-tree state was consistent — only the placeholder carrier bytes
were wrong.

## Fix (no content lost)

Each affected symlink placeholder was restored to its committed target text
(`git show HEAD:<path>`), moving nothing: the modified content remains live
at the resolved targets where the symlinks point. After the restore,
`git status` shows no modified symlinks and the strict materializer passes.

## Prevention

Edit symlinked command files through their resolved targets
(`.claude/skills/**`, `.codex/skills/**`, `tools/mail-cli/bin/mail`), not by
replacing the placeholder file in place — or run on a checkout with
`core.symlinks=true` where the placeholder indirection does not exist.

## Evidence

- Reproduced 2026-10-22 on `release_phase3`; bootstrap proceeded past
  materialization after the restore.
