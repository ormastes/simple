# Metal GPU Lane + Vulkan JIT Notebook — Parallel Implementation Plan

**Design:** `doc/05_design/app/tools/metal_gpu_lane_and_vulkan_jit_notebook_architecture_2026-08-09.md` (read in full before starting any stream)
**Related in-flight work (check status before starting N4/N6):**
`doc/08_tracking/bug/notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`

**Ground rules for every agent:**
- Do NOT work directly in `/home/ormastes/dev/pub/simple` (shared, contested by
  many concurrent sessions — origin/main moves multiple commits per minute).
  `cd /home/ormastes/dev/pub/simple && git fetch origin main`, then
  `git worktree add /home/ormastes/dev/pub/simple-<stream>-wt origin/main --detach`.
  Do all work in your own worktree. Remove it when done
  (`git worktree remove /home/ormastes/dev/pub/simple-<stream>-wt --force`).
- Push directly, don't wait to be asked: commit inside your worktree, then
  `timeout 90 env GIT_SSH_COMMAND="ssh -o BatchMode=yes -o ConnectTimeout=10 -i ~/.ssh/id_ed25519_this_mac" git push git@github.com:ormastes/simple.git HEAD:refs/heads/main`.
  If rejected non-fast-forward: `git fetch origin main`, confirm
  `git diff --quiet <old-tip> <new-tip> -- <your changed files>` shows NO
  output (proves no real overlap with what landed while you worked), then
  `git rebase origin/main` and retry. If genuine overlap appears, STOP and
  report — do not force.
- `SIMPLE_MODULE_LIMIT=4000` for any `bin/simple test` invocation.
- Never weaken a failing assertion. A correctly-failing/correctly-skipping
  spec is a legitimate artifact; file or update a bug doc instead of forcing
  green.
- Metal specs WILL skip on this Linux host — that's correct, expected,
  described in the design doc §9. Do not treat a `skip:` result as a problem
  to solve; verify it's the RIGHT skip reason (macOS/Metal absent), not a
  wrong-path bug masquerading as a skip.
- This repo strongly prefers `.spl` over Rust. Only touch
  `src/compiler_rust/` if the design doc explicitly calls for it (it
  shouldn't, for Metal — the FFI surface already exists per design §3) or you
  hit a genuine, narrow, well-understood gap. If a Rust change looks broad or
  risky, stop and report rather than force it (same standard applied to
  today's Vulkan-fence-timeout and interpreter-writeback investigations).

## Stream N1 — Grammar extension for `remote(metal(...))`

Design §8. Add `metal` as a valid backend token in the composite mode-spec
grammar/extractor. Reject `metal(...(resident))` mirroring Vulkan's existing
resident-rejection (find and mirror that exact test/validation). Small,
independent, no dependencies — good first stream.

**Verify:** existing grammar/extractor spec suite still green; a new
positive test for `interpreter(remote(metal(...)))`/`jit(remote(metal(...)))`
parsing accepted, and a negative test for the resident-suffix rejection.

## Stream N2 — `metal_lane_session.spl`

Design §4. New file, `src/lib/gc_async_mut/gpu_lane/metal_lane_session.spl`,
mirroring `vulkan_lane_session.spl`'s shape. Read
`src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl` for the FFI call
sequence but do not import/extend it — clean-room lane session. Add
`probe_gpu_driver_present("metal")`/`probe_gpu_symbols("metal")` to
`src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl`.

**Verify:** a minimal probe-only spec runs and SKIPs cleanly on this host
(confirms the probe path itself works, not just "doesn't crash").
Depends on: N1 (grammar) only loosely — can proceed in parallel, integrate
mode_spec parsing at the end.

## Stream N3 — `metal_vm_executor.spl` + `svmg_metal_kernel.metal`

Design §5. New file, `src/lib/gc_async_mut/gpu_lane/metal_vm_executor.spl`.
Port the SVM-G interpreter to MSL (checked-in kernel + `.sha256`, matching the
`svmg_cuda_kernel.ptx`/`svmg_vulkan_kernel.spv` convention). Depends on N2
(needs `MetalLaneSession` to dispatch against).

**Verify:** `test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl`
(new — see N8) SKIPs cleanly on this host with the correct reason. Do NOT
claim "conformance verified" — it cannot be, on this host. Claim "host-aware
skip-clean and structurally complete, unverified on real hardware," and file
the tracking bug per design §9/§11.

## Stream N4 — `metal_jit_lane_executor.spl` + MSL builder

Design §6, §3 (MSL builder). New files:
`src/compiler/70.backend/backend/metal/msl_builder.spl`,
`src/lib/gc_async_mut/gpu_lane/metal_jit_lane_executor.spl`.

**Before starting**, check
`doc/08_tracking/bug/notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`'s
current status (`git show origin/main:<path>`). If it's RESOLVED, mirror its
"arbitrary cell source → backend codegen → device artifact → run_program"
pattern exactly, targeting MSL instead of PTX. If it's still OPEN, build the
FFI/session/dispatch plumbing only and leave `run_program` as an honest
`Blocked` diagnostic citing this design doc — do not invent a fixed-demo-
kernel shortcut (that's the exact anti-pattern this whole plan exists to
avoid repeating for a third backend).

## Stream N5 — `metal_exec.spl` (notebook layer)

Design §6. New file, `src/lib/nogc_sync_mut/notebook/metal_exec.spl`
(`MetalExec`/`MetalExecFactory` implementing `NotebookExecutor`). Wire into
`src/lib/nogc_sync_mut/notebook/executor.spl`'s factory dispatch. Depends on
N2 (session) and N3 (VM executor) at minimum; N4 (JIT executor) for the jit
submode specifically — can stub the jit branch as `Blocked` if N4 hasn't
landed yet, same honesty standard as N4 itself.

**Verify:** `test/02_integration/app/tools/notebook/metal_exec_spec.spl`
(new — see N8) SKIPs cleanly.

## Stream N6 — Vulkan JIT notebook gap closure

Design §7. Independent of all Metal streams (N1-N5) — can run fully in
parallel with them.

**Before starting**, same check as N4: is CUDA's arbitrary-source-compile
gap resolved yet? If yes, mirror the pattern into
`vulkan_jit_lane_executor.run_program` (targeting
`src/compiler/70.backend/backend/vulkan/spirv_builder.spl`). Either way, add
the missing `jit` routing branch to `vulkan_exec.spl` (today it has ZERO
`jit`/`remote(vulkan` handling — confirmed via grep, this is not even a
stub) — at minimum an honest `Blocked` diagnostic mirroring CUDA's exact
message pattern, citing `notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`
and this design doc.

**Verify:** `test/02_integration/app/tools/notebook/vulkan_exec_spec.spl`
stays green (3/3, no regression); a new case or spec confirms
`jit(remote(vulkan(...)))` mode_spec routes to SOME defined behavior (either
real execution or an honest Blocked) rather than an unhandled/crashing path.

## Stream N7 — (reserved / do not use)

Intentionally not assigned — avoids a stream number collision with the
already-in-flight CUDA JIT-lane work (tracked separately, not part of this
plan). Do not start independent CUDA-lane work under this plan; that work is
owned elsewhere.

## Stream N8 — Test/spec authoring

Design §9. Can start in parallel with N1-N6 for the SHAPE of each spec
(structure, describe/it blocks, host-aware skip scaffolding via
`gpu_lane_common.spl`'s existing helpers) even before the executors they'll
call exist — write against the design doc's documented function signatures,
then do a final pass once N2-N6 land to confirm imports/calls match reality.

Required specs (mirror the exact CUDA/Vulkan file naming convention):
- `test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl`
- `test/03_system/gpu_lane/metal_jit_hello_spec.spl`
- `test/02_integration/app/tools/notebook/metal_exec_spec.spl`
- A grammar-level rejection test for `metal(...(resident))` (N1 may write
  this directly instead, avoid duplicating — coordinate via bug/todo doc if
  both streams are active simultaneously).

**Verify:** every new spec runs (not just "compiles") and produces a clean
`skip:` result with the CORRECT stated reason on this host. A spec that
crashes, hangs, or silently passes with no real assertion is not acceptable
even in the "will only run for real on Mac" case — the skip PATH itself must
be exercised and correct today.

## Stream N9 — Docs: `lane_matrix.md` + tracking bug

Design §10, §9 (tracking bug). Do LAST, after N1-N6/N8 land (or at minimum
after enough of them land to write an accurate status). Add `metal_jit`/
`metal_vm` rows to `doc/08_tracking/lane_matrix.md`. File
`doc/08_tracking/bug/metal_gpu_lane_never_verified_on_real_mac_hardware_2026-08-09.md`
per design §9/§11 — explicit disclosure, not silent omission, that only the
skip-path has been exercised.

## Suggested launch order

Given dependencies: N1, N2, N6, N8(shape-only) can start immediately in
parallel. N3 depends on N2. N4/N5 depend on N2+N3 (and N4 additionally on the
CUDA JIT-lane gap's status). N9 goes last. A reasonable first wave is
N1 + N2 + N6 + N8(scaffolding), then N3, then N4/N5, then N9 — but a single
agent per stream working somewhat out of order (e.g. N3's agent writing
against N2's documented-but-not-yet-landed interface, then rebasing) is fine
given each stream's design-doc signatures are already fully specified; true
hard sequencing is not required, just be honest in your report if you had to
build against an interface that later changed.

## Definition of done

Matches design doc §11 exactly. Do not mark this plan complete until every
stream's own "Verify" step has been run for real and reported, not assumed.
