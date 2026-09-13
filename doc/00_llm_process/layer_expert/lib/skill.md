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

## SciLib Handoff

SciLib's public typed-array and linear-algebra contract is documented in
`doc/07_guide/lib/scilib/scilib_ndarray_linalg_guide.md`; its active port
handoff is `doc/03_plan/lib/scilib/ports/scilib_port_remaining_agents.md`.
Use the feature expert at `doc/00_llm_process/feature_expert/scilib_port/skill.md`
for layer ownership, wrapper-boundary rules, and scenario evidence.

Template: [layer_skill.md](../../template/layer_skill.md)

## Session update 2026-09-11 — one-liners

- CPU<->GPU boundary fix campaign (Engine2D Vulkan rect batching, route-key
  re-arm, mid-frame fences): `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`
  § "2026-09-11 — CPU<->GPU boundary fix campaign (rect batch, F1/F2)".
- CEF-backed Chrome dynlib render module (Vulkan-composited offscreen
  Chromium): `doc/00_llm_process/feature_expert/chrome_dynlib/skill.md`.
- R1 root cause + typed-upload opt-in (Vulkan bind-after-readback):
  `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md` § "R1 round 2".
- Interpreter `&mut` extern out-slot writeback fix: no interpreter layer_expert
  page exists yet — see `doc/08_tracking/bug/interpreter_refmut_extern_out_slots_never_written_back_2026-09-11.md`
  directly.

## Session update 2026-09-06 — silent-rewind merges

`src/lib` shares append-only registry/manifest files with several parallel
lanes, so it is exposed to the stale-snapshot merge class that deleted landed
work in four PRs on 2026-09-06 without producing a single conflict. The
detection recipe (`git diff origin/main..HEAD -- <shared meta file> |
grep -c '^-[^-]'` must be `0`) and the caveats are on the
[app layer expert](../app/skill.md) § Session update 2026-09-06.
