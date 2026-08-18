# Debug + Profile Capability Feature Expert

## Role

Own process knowledge for the **unified debug/profile capability**: one pair of
traits (`DebugTarget`, `ProfileTarget`) plus their group (`DebugProfiler`),
implemented by the host, the reference VM, and the CUDA/Vulkan/Metal GPU lanes,
and surfaced through DAP, the Lab HTTP API, and `debug-doctor`.

**The single most important thing to know before touching this area:** classes
are value types, and every mis-shaped handle in this feature fails *silently*.
There is no diagnostic. See "The one hazard" below.

## Pipeline Links

(The template's `skill_command/skills/pipe/...` paths do not exist in this repo;
these point at the real skills.)

- research: `.claude/skills/research.md`
- design: `.claude/skills/design.md`
- impl: `.claude/skills/impl.md`
- verify: `.claude/skills/verify.md`
- release: `.claude/skills/release.md`
- **capability authoring: `.claude/skills/capability_interfaces.md`**

## Feature Links

- Design (authoritative; its §3 **CORRECTION** block overrides the prose beneath it):
  [doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md](../../../05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md)
- Plan: [doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md](../../../03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md)
- Authoring guide (start here to write a backend):
  [doc/07_guide/language/capability_library_authoring.md](../../../07_guide/language/capability_library_authoring.md)
- DAP guide: [doc/07_guide/app/lsp_dap/debug_profile_dap.md](../../../07_guide/app/lsp_dap/debug_profile_dap.md)
- Grammar requirement (inert): [doc/02_requirements/language/grammar/trait_with_capability_groups.md](../../../02_requirements/language/grammar/trait_with_capability_groups.md)
- Lane notes: [doc/08_tracking/lane_matrix.md](../../../08_tracking/lane_matrix.md) § Debug / profile capability per lane

## Code map

| Area | Path |
|---|---|
| Traits + reference impls | `src/lib/common/debug/` |
| GPU wrappers | `src/lib/gc_async_mut/gpu_lane/{cuda,vulkan,metal}_debug_session.spl` |
| DAP session | `src/app/dap/target_session.spl` |
| Lab endpoints + `%profile` | `src/app/simple_lab/lab_debug.spl`, `lab_server.spl` |
| Resolver + doctor | `src/app/debug_doctor/main.spl`, `src/lib/nogc_sync_mut/debug_doctor/matrix.spl` |
| Critical-mode lint | `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl` |

## The one hazard (assume every handle is a copy)

Three symptoms, one cause — classes are value types and nothing warns:

1. **Pairing diverges copies.** A group built from `session.debug()` +
   `session.profile()` holds two diverging copies (P2: 8/70 RED,
   `expected 6, got 0`).
2. **`fn` discards mutation.** A `fn` trait method gets a copy. Every mutating
   method must be `me`. (Does not bite for class-typed fields — P3/P4/P9 — but
   `me` stays the default.)
3. **Acquisition position decides aliasing.** A handle stops aliasing unless
   acquired as a function's **tail** expression; `set_breakpoint`/
   `profile_begin` are then silently discarded while `step`/`resume` keep
   working, reading as "this backend can't profile" (P10, 12-shape matrix).

Safe shapes: hold a class-typed session field directly (P3/P9/P8), or drive
`launch()` without binding a handle (P6/N3), or return the acquisition as a
tail expression.

Bugs: `capability_group_from_unsound_under_value_semantics_2026-08-09.md`,
`ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09.md`.

## Contract details that specs assert

- `set_breakpoint` returns **false** if already present (not idempotent-true).
- `breakpoints()` is **ascending**.
- `read_mem` returns **empty** on overrun, not a short buffer.
- `cap_level_name` is **lowercase**.
- `PROFILE_ABSENT = -1` is the only honest "not measured". Reporting `0` is a
  contract violation (P7 fixed exactly that).
- Profiling is **armed at attach** (`AttachOpts.profile`) — GPU PROF-1 cannot
  be enabled after upload.

## What is real, and what is not

- **All evidence is from the Rust seed.** Nothing here is self-hosted evidence.
- **CUDA and Vulkan genuinely run on device** — 20 launches each, field diffs
  clean.
- **Metal's entire device path is unverified.** `svmg_metal_kernel.metal` has
  never been compiled by any Metal compiler (no `xcrun`/`metal` on this Linux
  host). This is the feature's highest-risk unknown. Never state or imply that
  Metal works.
- **DAP GPU attach is ROUTING-ONLY.** No `.spl` → SVM-G path exists;
  `lower_svmg_program` is scoped to HIR test bodies with no caller outside
  `70.backend`. Filed:
  `no_general_spl_to_svmg_path_blocks_dap_gpu_attach_2026-08-09.md`.
- **The trait `with` sugar is INERT** — `desugar_traits` has no compile-path
  caller and the deployed seed predates the parser change.
- **`if val` is AOT-broken** (real `nil` → `SOME` under `native-build`), so a
  generated capability check would fail **OPEN** natively once wired.

## Testing practice this feature established

- **Assert on execution, not text or structure.** P0's generator passed 21/21
  while emitting code that could not compile.
- **A disjunctive spec is unfalsifiable.** "skip cleanly OR match ref_vm"
  proves nothing. Emit the branch (`DEVICE-RAN:` /
  `SKIPPED: … the DEVICE-RAN branch did NOT run`) and support
  `SIMPLE_REQUIRE_GPU=1`. Note `step()` text is **swallowed** on passing runs —
  use `print` or assert messages (found independently by N3 and P13).
- **Prove oracles by sabotage.** P6b's launch-count floor sabotaged to
  `expected 20 to be greater than 100000`; P4 caught its own zero-overhead
  oracle passing with guards removed.
- **Gate tautologies (P15).** 12 specs asserted only
  `test_env_require(...) == "blocked:..."` — green *because* the gate was shut,
  with false `@cover` claims. **The fix is NOT flipping the expected value to
  `ready`** — that trades one vacuous spec for another. Assert on behaviour
  behind the gate.
- **A green spec says nothing about reachability.** Three landed mechanisms
  have no caller: `desugar_traits`, `svmg_lowering`, `action_key`/
  `interface_digest`. Grep for callers before claiming end-to-end.

## Landed streams

P0 `50f06dcdd56` · P0b `8477ff5bdd0` · P1 `5ad3f64f928` · P2 `0b8ec4395b2` ·
P3 `79f3b662376` · P4 `a800bb04066` · P5 `abacef5d7f4` · P6 `7d53bf0a83b` ·
P6b `7f4004e1ff1` · P7 `40f72d2ceb1` · P8 `f94d2c2b02a` · P9 `6e108de66b2` ·
P10 `a4156a456d2` · P11 `2562958c4b0` · P13 `5fb82db579b` · P14 `c3307d1404d` ·
P15 `1bc53420716` · N3 `c2fc4ebaef5`

## Fix-verification contract (2026-08-18)

Every bug fix lands with: (1) a **reproduction spec run red-first** (observe
the reported symptom fail before the fix, report red→green with values);
(2) **similar-case specs** covering the sibling code paths that share the
defect's shape (other match arms, API-family twins, neighboring config axes,
boundary values — grep for the wrong pattern and cover each repeat);
(3) a **sabotage probe** (re-break → red → restore → green, all three
observed). Canonical wording: `.claude/agents/test.md` § "Every fix ships a
reproduction spec AND similar-case specs"; SPipe process hook:
`.claude/skills/spipe.md` § "Reproduce-first for bug-fix specs".
