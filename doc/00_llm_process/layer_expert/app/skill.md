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
