# Unified Debug + Profile Capability — Detailed Parallel Plan

**Design:** `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md`
(read FULLY first; §refs below point there). Supersedes the GPU-only plan
(`gpu_debugger_common_interface_parallel_plan_2026-08-09.md` — its D1/D3
protocol content is inherited by P5/P6 here; do not execute that plan
separately).
**Status:** PLAN ONLY — agents not yet launched.

**Ground rules (every agent, verbatim from prior plans — they work):**
- Never work in the shared `/home/ormastes/dev/pub/simple` checkout.
  `git fetch origin main` → `git worktree add /home/ormastes/dev/pub/simple-<stream>-wt origin/main --detach`
  → work there → remove when done.
- Push per-stream, immediately after verification:
  `timeout 90 env GIT_SSH_COMMAND="ssh -o BatchMode=yes -o ConnectTimeout=10 -i ~/.ssh/id_ed25519_this_mac" git push git@github.com:ormastes/simple.git HEAD:refs/heads/main`;
  non-fast-forward → fetch, `git diff --quiet old new -- <your files>` must
  be silent, rebase, retry; real overlap → STOP and report.
- `SIMPLE_MODULE_LIMIT=4000` on every test run. Never weaken assertions.
  Metal device paths skip on Linux by design — assert the skip is clean.
- Each stream's report must include: files, fresh `Results:` lines, push
  SHA verified via `ls-remote`, and any interface drift from the design doc
  (report it, don't silently diverge).

## Dependency graph

```
P0 lang: trait-with groups + .from() sugar (parser+desugar)   ── independent
P1 critical-mode lint (warn→error flag) + manifest pin        ── needs P0 (lints .from())
P2 shared traits lib (capability/debug_target/profile_target/core)  ── independent of P0!
 ├─ P3 host DebugTarget adapter over existing DAP session          needs P2
 ├─ P4 host ProfileTarget (interpreter counter discovery + wall)   needs P2
 ├─ P5 DBG-1 + ref_vm + debug vectors (= old D1)                   needs P2 only for types
 │   └─ P6 cuda+vulkan debug wrappers + kernels + env specs (= old D3)  needs P5
 │        └─ P7 PROF-1 + native timing (cuEvent/vkQuery/MTL) + vectors  needs P5,P6
 │             └─ P8 metal debug+profile wrapper (unit Linux, env skip) needs P6,P7 pattern + Metal-lane N2/N3
 ├─ P9 DAP target-neutral session + profile custom requests        needs P2,P3 (ref/host first)
 ├─ P10 Lab/notebook endpoints + %profile magic                    needs P2 (ref-backed)
 └─ P11 config resolver (bare gpu tag) + debug-doctor              needs P2 (doctor drives accessors)
P12 docs/guide/grammar/skills/wiki                                 with each stream + final sweep
```

Note P2 does NOT wait for P0: groups/`from()` are sugar ATOP plain traits +
Option accessors, which are today-valid Simple. P0 lands the sugar; P2's
library converts its hand-written group struct to the sugared form in a
small follow-up commit (explicitly listed in P0's tasks).

## Wave 1 (launch together): P0, P2, P5, P11
## Wave 2: P1, P3, P4, P6, P10
## Wave 3: P7, P9
## Wave 4: P8, P12 final sweep

---

### P0 — Language: trait `with` groups + generated `.from()` (design §3)

Files: parser (trait-header production — find where `struct X with M:` is
parsed and extend the trait header to accept the same clause; zero new
tokens), `src/app/desugar/trait_scanner.spl` + `forwarding.spl` (group =
concat member fn-fields; blanket satisfaction; generate `Group.from(expr)`
per the accessor-matching rule in design §3 — missing accessor = compile
error naming it).
Also: file the feature-request doc under `doc/02_requirements/language/`
FIRST (small, states grammar delta + desugar semantics), then implement
against it.
Tests: `test/01_unit/compiler/desugar/trait_group_spec.spl` — group parses;
blanket satisfaction (type implementing members passes where group is
expected); `.from()` returns Some/None correctly; missing-accessor compile
error (negative fixture); NO new tokens (assert existing grammar corpus
unchanged — run the parser suite).
Regression: full desugar/parser suites + `bin/simple lint` self-run.
Follow-up task in-stream: convert P2's hand-written group to sugar once
green.

### P1 — Critical-mode lint + manifest pin (design §4)

Files: new lint `dynamic_capability_acquire` in the existing lint framework
(`src/compiler/35.semantics/lint/`); `@init_phase` attribute recognition;
config keys `critical.dynamic_acquire: allow|warn|error` (SDN); manifest
pin validation for `gpu.backend` under critical mode + boot-time
probe-vs-manifest refusal helper.
Tests: fixture with `.from()` outside `@init_phase` → warn under `warn`,
error under `error`, silent under `allow`; manifest mismatch with fake
probe → refusal with report; inside-`@init_phase` → clean.
Docs (in-stream): lint reference entry + critical-mode section of the
library-authoring guide (§10.2 skeleton ok; P12 polishes).

### P2 — Shared traits library (design §2)

Files: `src/lib/common/debug/{capability,debug_target,profile_target,session_core}.spl`
+ hand-written `DebugProfiler` group struct + `debug_profiler_from(s)`
helper (to be replaced by P0 sugar) + `ref_debug_session.spl` implementing
ALL of it over `ref_vm.spl`'s `SvmgVm` (including Emulated profile via a
host-side step counter — ref needs no DBG-1 to count steps).
Tests: `test/01_unit/lib/debug/debug_target_ref_spec.spl` — the FULL
contract against ref: breakpoints, step, resume, state decode, read_mem,
profile begin/end steps exactness, accessor Some/None, group acquisition.
This spec is the feature's behavioral anchor — be exhaustive; every later
backend spec diffs against ref through the same vector tables.

### P3 — Host DebugTarget over the existing DAP session (design §5)

Files: `src/app/dap/host_debug_target.spl` (adapter over
`SimpleDapSession`'s existing breakpoint/step/stack machinery; `pc_kind =
"line"`); NO restructuring of existing dap files.
Tests: adapter unit spec driving the trait against a fixture `.spl`
program (breakpoint on line N hits; step advances; stack sane; read_mem
maps the variable slab per whatever `SimpleDapSession` exposes — if
variable slab access needs a small hook in existing code, keep the diff
minimal and prove existing DAP specs still green).
Regression gate: ALL existing `src/app/dap` specs unchanged and green
(enumerate them in your report).

### P4 — Host ProfileTarget (design §5)

Opening task: DISCOVER whether the interpreter already maintains an
instruction/node counter (grep coverage + step-budget machinery in the
interpreter first; report what exists). Expose if present; else add a
cheap counter gated on profiling-enabled (measure the overhead OFF —
must be zero when disabled; state the measured cost when ON).
Files: `src/app/dap/host_profile_target.spl` (+ minimal interpreter hook
if needed — if that hook is Rust, it's a narrow documented exception;
report it explicitly).
Tests: wall_ns > 0 always; steps exact on a fixed-instruction fixture (or
honestly `-1` + `detail` note if only wall is achievable — do not fake).

### P5 — DBG-1 + ref_vm + debug conformance vectors (design §6; = old plan D1)

Exactly the superseded plan's D1 content: DBG-1 offsets/flags/sentinel in
`mailbox_const.spl` (assert non-overlap with REG/LOG/RECORD in a unit
spec); save/restore/breakpoint-check in `ref_vm.spl` gated on
`DBG_FLAGS != 0`; `test/fixtures/svmg/debug_conformance_vectors.spl`
(break-at-pc, step-N, resume-to-completion, break-in-loop,
resume-with-persisted-arena, budget-expiry-during-debug, table-full).
PLUS (pulled forward from P7 so kernels change once): the PROF-1
`DBG_STEP_COUNT` field and its ref_vm increment, vector-verified.
Regression gate: existing svmg conformance suite byte-identical green.

### P6 — CUDA + Vulkan debug wrappers, kernels, env specs (design §6; = old D3)

DBG-1+PROF-1 in `svmg_cuda_kernel.ptx` and `svmg_vulkan_kernel.spv`
(rebuild .spv from .spvasm per the existing checked-in convention +
.sha256); `cuda_debug_session.spl`/`vulkan_debug_session.spl` implementing
`DebugSessionCore`+`DebugTarget` (+ Emulated `ProfileTarget` via
DBG_STEP_COUNT readback); persisted-arena continuity (absolute-offset —
see the 2026-08-08 bug docs; the relative-offset bug is a known trap).
Env specs run the debug vector table on live devices (both present on this
host), diff field-for-field vs ref.
Regression gates (run fresh, all four): cuda_vm conformance 2/2, vulkan_vm
conformance 2/2, cuda_exec 4/4, vulkan_exec 3/3 — DBG_FLAGS==0 inertness.

### P7 — Native profile timing (design §7)

Per backend, in order of certainty: Vulkan timestamp query pool; CUDA
cuEvent pair; (Metal timing goes with P8). First task per backend: check
the existing extern surface (62 rt_vulkan_*, 33 rt_cuda_*) for
event/query support; a missing extern is a NARROW Rust addition following
the sibling dlopen-table pattern — report each one added.
Profile conformance vectors: fixed-instruction fixtures — `steps` exact vs
ref on both backends; `device_ns > 0` and wall/device sanity on live
hardware; `ProfileReport.level` correctly `Native` vs `Emulated` per path.
Doctor row data now real for cuda/vulkan.

### P8 — Metal: debug + profile wrapper (design §6/§7; needs Metal-lane N2/N3)

Gate-check first: Metal lane plan's N2 (landed: metal_lane_session) and N3
(kernel — check origin/main). If N3 absent, implement wrapper + unit tests
against the documented kernel contract and say so.
`metal_debug_session.spl` (+ MTL GPUStartTime/GPUEndTime Native timing;
MTLCounterSampleBuffer explicitly P3-absent in `detail`).
Unit specs run ON LINUX (routing, probe-skip propagation, DBG/PROF block
construction, synthetic readback decode, ProfileReport assembly). Env spec
asserts the clean skip. Extend the Metal-pending tracking doc.

### P9 — DAP target-neutral session + profile requests (design §8)

`src/app/dap/target_session.spl` + launch-config routing (`gpu:true` via
the resolver, `gpuModeSpec` explicit, default host) + custom requests
`simple/profileBegin|End`.
Unit: full DAP JSON round-trips against ref target AND host target
(extend the existing DAP spec pattern — protocol in, assert responses).
Env: one live-CUDA DAP round trip (host-aware skip).
Regression: every existing DAP spec unchanged green.

### P10 — Lab endpoints + %profile magic (design §9)

Endpoints on `lab_server.spl` (debug: start/step/resume/break/state;
profile: begin/end) + `%profile` in the magics dispatcher. Ref-backed
default; live-CUDA case where hardware present.
Reuse `lab_http_api_spec.spl`'s real-subprocess driver pattern — note its
documented traps (portfile poll constants, daemon timeout). `lab_server.spl`
is hot — tight diff, push fast.

### P11 — Config resolver + debug-doctor (design §5/§8; resolver = old D7)

`resolve_gpu_mode_spec(tag, config)` + `[gpu]` SDN section in the EXISTING
project config (find it; don't invent a file) + `debug-doctor` (subcommand
or run-script — implementer picks lighter; prints the §5 matrix by REALLY
constructing sessions and calling accessors).
Unit: resolver matrix with fake probes (explicit passthrough / configured /
auto-probe order cuda→vulkan→metal / no-tag=host / none-available error
listing per-backend reasons). Doctor spec: host row asserts Native entries;
gpu rows host-aware.

### P12 — Docs, grammar reference, lib guide, skills, wiki (design §10)

Runs twice: (a) each stream lands its own doc slice with its code (listed
per stream above); (b) final sweep agent verifies all six §10 deliverables
exist, are accurate against the AS-BUILT code (not the design's
aspirations), cross-link correctly, and the LLM wiki hub
(`feature_expert/debug_profile/skill.md`) reflects reality. Also: lane_matrix
debug/profile notes; supersession notes added to the two older design docs'
Status lines; link-check every touched doc (the notebook-lanes D1 pattern —
paths/symbols must exist).

## Definition of done

Design doc §11 verbatim; every stream's verification actually run and
reported. The four cross-cutting regression gates (existing DAP specs, four
GPU suites, svmg conformance, parser/desugar suites) each appear in at
least one stream's fresh-run report.
