# os Layer Expert

## Role

Maintain process knowledge for the `os` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/os` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/os/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)

## Boundary Rules

- Pure Simple first: never a C implementation where pure Simple can do it; the C runtime is a boundary, not a place for logic. Bootstrap-required C keeps a pure-Simple twin (`scripts/check/check-dual-run-shadow.shs`). HAL code minimizes inline asm (typed register views > optimization-restraining tags > intrinsics > asm for irreplaceable ops only). Full policy: [pure_simple_hal.md](../../../07_guide/os/hal/pure_simple_hal.md).

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)
