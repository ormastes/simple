# Bootstrap provenance Git rename scan

Status: claimed; repair pending
Severity: P2 bootstrap performance/robustness
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`

## Symptom

Stage 3 provenance invokes `git diff --binary --full-index HEAD --` with rename
detection enabled. In the isolated dirty worktree Git examined about 1.32
million rename candidates, emitted the rename-limit warning twice, consumed
minutes at one core, and used roughly 1.2 GiB RSS before Stage 4 could start.

## Owner and intended repair

The authority owner is
`scripts/check/lib/bootstrap-stage3/authority.shs`. Provenance needs stable
content bytes for tracked additions/deletions/modifications; it does not need
rename pairing. Add `--no-renames` to the fingerprint diff, retain binary and
full-index output, and cover the command contract plus dirty-content hash
change behavior.
