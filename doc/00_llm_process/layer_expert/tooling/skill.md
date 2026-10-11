# tooling Layer Expert

## Role

Maintain process knowledge for the `tooling` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/tooling` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/tooling/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Host config (2026-10-09)

Host facts (job ceiling, worker memory, cpu family/features, os, LLVM
root/version, gpu) come from the layered host config, not hardcoded script
values: env `SIMPLE_HOST_<KEY>` > `~/.config/simple/host.sdn` (setup-generated,
untracked) > `config/host/<hostname>.sdn` > `config/host/host_config.sdn`
(tracked, values commented). Reader: `scripts/setup/host-env.shs`
(`--get/--print/--init/--selftest`) and `std.common.config_core.host_config`.
Guide: `doc/07_guide/infra/toolchain/host_config.md`; feature expert:
`doc/00_llm_process/feature_expert/host_config/skill.md`.
