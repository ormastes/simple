# app Layer Expert

## Role

Maintain process knowledge for the `app` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/app` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/app/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)
- [debug_profile feature wiki](../../feature_expert/debug_profile/skill.md) — `src/app/cli_debug/` evidence bundle writer + reader (`simple debug write` / `inspect`); CLI acceptance is hand-verified only, see `todo_db.sdn` row 0

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Session update 2026-09-06 — the silent-rewind merge class

**A PR built on a stale snapshot can DELETE landed work while merging cleanly.**
This is not a conflict and no tool warns about it: `git merge-tree` reports no
conflict, CI is green, and the diff looks like an addition because the deletions
are in a file the author never opened. It bit four PRs in one day. Under the
parallel-agent load this repo runs, any branch cut more than a few hours ago is
a candidate.

The victims are the *shared append-only meta files* several lanes all touch —
registries, manifests and gate ledgers such as
`doc/00_llm_process/knowledge_registry.sdn`,
`doc/00_llm_process/llm_process_manifest.sdn` and
`config/check/must_check_gates.sdn`. Every lane appends a row; a snapshot taken
before three other lanes appended theirs silently removes all three.

### Detection — run this before every push

```sh
git diff origin/main..HEAD -- <shared meta file> | grep -c '^-[^-]'
```

Must print `0`. `^-[^-]` skips the `---` file header, so the count is real
removed lines. A non-zero count on an append-only file is a rewind: rebase onto
`origin/main` and re-apply your row, never force the snapshot through.

Caveat: this idiom is only valid for files that are genuinely append-only.
On a file where lines legitimately change, a removed line is normal and you must
read the diff instead of counting it.

Same family, already recorded:
[aspect_dynload_facet_implementation_deleted_by_merge_restore_2026-09-05.md](../../../08_tracking/bug/aspect_dynload_facet_implementation_deleted_by_merge_restore_2026-09-05.md),
[sffi_authority_group2_stale_snapshot_clobber_2026-09-02.md](../../../08_tracking/bug/sffi_authority_group2_stale_snapshot_clobber_2026-09-02.md),
[share_history_merge_landed_consumers_without_their_api_2026-09-01.md](../../../08_tracking/bug/share_history_merge_landed_consumers_without_their_api_2026-09-01.md).
The push-side protocol this implements is `.claude/rules/vcs.md` § "Sync must
never clobber (anti-revert protocol)"; the PR-landing mechanics are in
`.claude/skills/spipe.md` § "Landing a PR here".
