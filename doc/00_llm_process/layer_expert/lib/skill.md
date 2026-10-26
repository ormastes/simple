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

## Session update 2026-09-19 — one-liners

- Host file mapping moved under SOSIX as two ops (`sosix_file_map` ACTUAL
  access, `sosix_file_map_prefetch` CACHING; Windows prefetch is a no-op):
  `doc/00_llm_process/feature_expert/sosix_runtime_unification/skill.md`
  § "Ownership and paths" (File mapping row). `std.io.file_ops.file_mmap` is
  gone; the core-C lane now defines `rt_mmap` statically.

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

## Memo/cache keys must name every input (2026-09-14)

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
carries a style-cascade memo whose comment asserts the computed style is "a
deterministic function of (parent inherited identity, tag, presentational
decls)" plus em_base, writing mode and the accumulated author declarations —
"so those six inputs are the whole key". That claim is a maintenance contract,
not a description: the moment a new UA rule read the ANCESTOR chain, the
invariant broke and the cache served a stale style to the second node with the
same tag. The failure was silent and partial — `ol`-in-`ul` worked, `ul`-in-`ul`
did not — which is the worst shape to debug, because the fix looks half-applied
rather than mis-cached.

Rule for this layer: when adding an input to a memoised computation, add it to
the key in the same edit, and pin it with a spec whose fixture actually
activates the cache (here the memo only runs when some author rule matches, so
a bare-UA fixture would have passed without the key change and guarded
nothing). Sabotage the key term on its own and confirm the spec reds — a
"simplification" of a cache key otherwise reads as a free cleanup.

See `doc/08_tracking/bug/web_layout_vertical_drift_accumulates_16px_per_construct_2026-09-14.md`.
