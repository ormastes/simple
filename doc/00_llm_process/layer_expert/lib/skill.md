# lib Layer Expert

## Role

Maintain process knowledge for the `lib` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/lib` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/lib/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Session update 2026-09-06 — silent-rewind merges

`src/lib` shares append-only registry/manifest files with several parallel
lanes, so it is exposed to the stale-snapshot merge class that deleted landed
work in four PRs on 2026-09-06 without producing a single conflict. The
detection recipe (`git diff origin/main..HEAD -- <shared meta file> |
grep -c '^-[^-]'` must be `0`) and the caveats are on the
[app layer expert](../app/skill.md) § Session update 2026-09-06.
