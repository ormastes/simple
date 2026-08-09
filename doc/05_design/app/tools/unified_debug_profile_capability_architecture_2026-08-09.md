# Unified Debug + Profile Capability Architecture (host + GPU, shared interfaces)

**Status:** Design v2, not yet implemented (plan:
`doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md`)
**Supersedes/extends:** `gpu_debugger_common_interface_architecture_2026-08-09.md`
(its DBG-1 protocol, debug conformance vectors, and lane-session delegation
carry over UNCHANGED — §5 there; this doc widens the interface layer so host
(CPU) and GPU share ONE debug interface and ONE profile interface, adds
profiling implementations per backend, the capability/trait-group language
mechanism, and critical-mode enforcement.)

## 1. Goals

1. **One `DebugTarget` and one `ProfileTarget` interface shared by host and
   GPU.** The existing host DAP session (`src/app/dap/`) and every GPU lane
   implement the same traits; the DAP server, Lab endpoints, and any tool
   drive a target without knowing whether it is CPU or GPU.
2. **Profiling implemented for real** on host + CUDA + Vulkan + Metal, with
   tiered honesty: `Native | Emulated | Unavailable`.
3. **Trait groups with zero new grammar tokens** (§3): reuse the existing
   `with` clause; group acquisition sugar is a *generated static* `.from()`,
   pure desugar.
4. **Critical mode**: dynamic capability acquisition after initialization is
   a lint **warning now, error later** (phased flag), with the backend
   manifest-pinned at build.
5. **Capability doctor**: a runnable check reporting exactly which
   debug/profile capabilities THIS host supports per target (host, cuda,
   vulkan, metal), at which tier — so "does the host properly support DAP
   and profile" is a command, not a guess.
6. Docs land with the code: grammar reference, library-authoring guide,
   skills, LLM wiki (§10).

## 2. Interface layer (the shared core)

New tier-neutral module `src/lib/common/debug/` (pure logic, importable from
every family per the existing tier rules):

```simple
# capability.spl
enum CapLevel:
    Native        # real backend mechanism (cuEvent, VkQuery, MTL timestamps, host clock)
    Emulated      # correct but synthesized (SVM-G step counts, interpreter counters)
    Unavailable

struct DebugState:
    pc: i64                # host: line; GPU: bytecode pc  (unit named in `pc_kind`)
    pc_kind: text          # "line" | "svmg_pc"
    sp: i64
    stack: [i64]
    call_stack: [i64]
    stop_reason: text      # "breakpoint" | "step" | "halt" | "trap" | "timeout" | "running"

# debug_target.spl
trait DebugTarget:
    fn kind() -> text                    # "host" | "cuda" | "vulkan" | "metal" | "ref"
    fn debug_level() -> CapLevel
    me set_breakpoint(loc: i64) -> bool  # loc in pc_kind units
    me clear_breakpoint(loc: i64) -> bool
    me breakpoints() -> [i64]
    me step() -> DebugState
    me resume() -> DebugState
    me state() -> DebugState
    me read_mem(offset: i64, len: i64) -> [u8]    # host: variable slab; GPU: DATA region
    me detach() -> text

# profile_target.spl
struct ProfileReport:
    level: CapLevel
    wall_ns: i64           # always present (host clock around the run)
    device_ns: i64         # Native only: cuEvent / VkQuery / MTL GPU time; else -1
    steps: i64             # Emulated/VM: instruction count; host: interpreter step count; else -1
    detail: text           # backend-specific extras, SDN-encoded ("" when none)

trait ProfileTarget:
    fn profile_level() -> CapLevel
    me profile_begin()
    me profile_end() -> ProfileReport

# session core trait — the ONLY runtime capability edge (design rationale:
# see the superseded doc's §4 discussion + the mode-stratification analysis)
trait DebugSessionCore:
    fn kind() -> text
    me attach(source: text, opts: AttachOpts) -> text    # "" | "skip:..." | error
    me debug() -> Option<DebugTarget>
    me profile() -> Option<ProfileTarget>
    me shutdown() -> text
```

**Rule: accessors are part of the core trait** — every implementation MUST
answer `debug()`/`profile()`; forgetting one is a compile error. A `None` is
a truthful runtime absence, never an unimplemented hole.

## 3. Trait groups + sugar — zero new grammar tokens

> **CORRECTION 2026-08-09 — read before implementing against this section.**
> The `.from()` acquisition shape originally specified below is **UNSOUND** and
> was measured RED by P2 (8/70 failing, `expected 6, got 0`) before being
> corrected on main.
>
> Cause: classes in this language are **value types** — `val b = a` copies. A
> group built by PAIRING two accessors (`session.debug()` + `session.profile()`)
> therefore holds two *diverging copies* of the session. Stepping through the
> debug half leaves the profile half reading 0 steps. Nothing in the type system
> catches this.
>
> **Corrected shape (what is on main):** a group is **one trait over one value**
> — the literal union of its members' methods, which is exactly what the `with`
> sugar already desugars to — acquired through a **single** accessor, never by
> pairing. Until P0's generator is updated, each backend supplies
> `<backend>_debug_profiler(session)`.
>
> A second value-semantics trap in the same family: **`me` vs `fn` on trait
> methods is load-bearing.** A `fn` method receives a COPY of the receiver and
> silently discards mutation, with no compiler complaint. Every mutating method
> (`step`, `resume`, `set_breakpoint`, `clear_breakpoint`, `detach`,
> `profile_begin`, `profile_end`) MUST be declared `me`. The `me` markers in
> this document are normative, not stylistic.
>
> Authoritative writeup:
> `doc/08_tracking/bug/capability_group_from_unsound_under_value_semantics_2026-08-09.md`.
> Landed interfaces to code against: `src/lib/common/debug/`.
> Also note `AttachOpts` (referenced but never defined here) is now real in
> `session_core.spl`: `step_budget`, `entry_pc`, `log_cap`, `profile: bool` —
> and profiling must be **armed at attach**, since GPU PROF-1 cannot be enabled
> after upload.

**Group definition** reuses the existing `with` clause (already parsed on
`struct X with Mixin:`; the trait-header production is extended to accept
the same clause — no new keyword, no new token, no `+`):

```simple
trait DebugProfiler with DebugTarget, ProfileTarget:
    pass_dn                                  # pure group: zero new methods
```

**Desugar** (in `trait_scanner.spl`/`forwarding.spl`, where traits already
flatten to struct-of-fn-fields): a group trait desugars to the concatenation
of its members' fn-fields, plus TWO generated artifacts:

1. **Blanket rule**: any type implementing all members automatically
   satisfies the group (checked at compile time — the group adds no
   obligations, so this is sound by construction).
2. **Acquisition sugar** — a generated static on every group:

```simple
val dp = DebugProfiler.from(session)     # Option<DebugProfiler>
# desugars to: match on session.debug(), session.profile(); Some(group struct
# bundling both) only if ALL members acquire; None otherwise.
```

`.from()` generation rule: for each group member trait `M`, the source
expression must expose an accessor returning `Option<M>` (matched by return
type against the core trait's accessors). If no accessor exists for some
member, `.from()` is not generated and using it is a compile error naming
the missing accessor — mistakes surface at build, not run.

Static use needs no acquisition at all — a fn taking the group directly is
statically checked:

```simple
fn trace_run(dp: DebugProfiler) -> ProfileReport:
    dp.profile_begin()
    dp.resume()
    dp.profile_end()
```

## 4. Critical mode: warn now, error later

Lint `dynamic_capability_acquire` (new, in the existing lint framework):
flags any `<Group>.from(...)` call or `Option<Trait>`-returning accessor
call that is NOT inside an `init`/boot-marked function (attribute
`@init_phase` on the composition root; the lint ships with the exact
marking rules documented).

Phase-in, controlled by project config (SDN):

```
critical:
  dynamic_acquire: warn      # today's default in critical mode
  # -> "error" in a later release; non-critical profiles: "allow"
```

- `allow` (default outside critical mode): no diagnostics.
- `warn` (critical mode initial): builds succeed, diagnostic names the call
  site + the manifest alternative.
- `error` (critical mode target state): build fails. Additionally in
  critical mode the GPU backend must be **manifest-pinned**
  (`gpu: backend = cuda(sm80)` — no `auto`); `probe()` at boot must match
  the manifest or the process refuses to start with a manifest-mismatch
  report (promoted fault path, not a fallback).

## 5. Host (CPU) implementations — and the "does host properly support it" check

**Host debug — exists, needs adapting, not building:** `src/app/dap/`'s
`SimpleDapSession` already does breakpoints/step/stack/evaluate against a
launched `.spl` source session. Work: implement `DebugTarget` over it
(thin adapter `host_debug_target.spl`; `pc_kind = "line"`), so the SAME
trait drives host and GPU. Existing DAP protocol handling is untouched;
`dap_handlers` gains a target-neutral path (§8).

**Host profile — partial, needs real implementation:** wall-clock exists
trivially; `steps` requires an interpreter counter. Check first (stream
P4's opening task) whether the interpreter already maintains an instruction/
node counter (coverage and step-budget machinery suggest yes somewhere);
expose it if so, add a cheap one gated behind profiling-enabled if not.
Host `profile_level()` = `Native` for wall_ns, reported honestly in
`detail` which pieces are measured vs absent.

**Capability doctor (§1.5):** `bin/simple debug-doctor` (new small
subcommand or `run` script per repo conventions — implementer picks the
lighter path) prints the matrix:

```
target   attach   debug            profile
host     ok       Native (line)    Native (wall) + steps
cuda     ok       Native (svmg_pc) Native (cuEvent) / Emulated (steps)
vulkan   ok       Native (svmg_pc) Native (vkQuery) / Emulated (steps)
metal    skip:... -                -
```

Each row produced by actually constructing the session and calling the
accessors — the doctor IS the acceptance test for "host properly supports
DAP and profile interfaces", runnable anywhere, and its output is the
skip-clean story on hosts missing hardware.

## 6. GPU debug — unchanged from the superseded design

DBG-1 arena block, kernel save/restore/breakpoint-check, debug conformance
vectors, ref/cuda/vulkan/metal wrappers — all as specified there (§3-§4).
Only naming shifts: wrappers implement the SHARED `DebugTarget` (this doc
§2) instead of a GPU-only trait; `GpuDebugState` folds into `DebugState`
with `pc_kind = "svmg_pc"`.

## 7. GPU profile — PROF-1 (new)

**Emulated tier (all backends, lands first):** SVM-G already meters
execution via step budget. PROF-1 adds a `DBG_STEP_COUNT u64` (or u32 pair)
field to the DBG-1 block: the kernel increments per instruction when
`DBG_FLAGS.profile` bit set; readback gives exact instruction counts. Works
identically on cuda/vulkan/metal/ref — this alone satisfies `Emulated` on
every backend and is the only tier testable end-to-end on the host `ref` VM.

**Native tier (per backend, real device timing):**
- CUDA: `cuEvent` pair around the launch → `device_ns`
  (`cuEventRecord`/`cuEventElapsedTime`; check the existing 33 rt_cuda_*
  externs for event support; if absent, this is a narrow, pattern-following
  Rust extern addition — same dlopen table as the siblings).
- Vulkan: `VK_QUERY_TYPE_TIMESTAMP` query pool (2 timestamps around the
  dispatch) → `device_ns`. Same extern-gap check against the 62 rt_vulkan_*
  symbols.
- Metal: `MTLCommandBuffer` `GPUStartTime`/`GPUEndTime` (simplest of the
  three — already-completing command buffers carry the timestamps; check
  rt_metal_* surface). `MTLCounterSampleBuffer` hardware counters are
  explicitly **P3, out of scope** — `detail` notes their absence.
- Every backend also fills `wall_ns` (host clock around dispatch) so even
  `Native` reports are cross-checkable, and a Native-vs-wall gross
  divergence is flagged in `detail` (cheap sanity oracle).

**Profile conformance vectors:** small table (fixed-instruction-count
programs) asserting `steps` exactness on every backend vs `ref_vm`, and
`device_ns > 0`, `wall_ns >= device_ns`-ish sanity for Native tiers on live
devices. Same host-aware skip contract as everything else.

## 8. DAP integration — one adapter, any target

`src/app/dap/` gains a target-neutral session (`target_session.spl`):
launch config selects the target —

```
{"type":"simple", "program":"cell.spl"}                          -> host (today's behavior, unchanged)
{"type":"simple", "program":"cell.spl", "gpu": true}             -> config-resolved GPU target
{"type":"simple", "program":"...", "gpuModeSpec":"interpreter(remote(cuda(sm80)))"}  -> explicit
```

- Breakpoints/step/stack/variables map through `DebugTarget` uniformly
  (host `pc_kind=line` maps directly; GPU maps through the debug map —
  superseded doc §6, unchanged).
- **Profiling over DAP**: custom requests `simple/profileBegin`,
  `simple/profileEnd` → `ProfileReport` as the response body (DAP permits
  custom requests; document them in the DAP guide). IDEs without custom-
  request UI still get profiles via the Lab endpoints or `debug-doctor`.
- Existing local-session code paths untouched; the neutral session wraps
  `host_debug_target` for the host case. Existing DAP specs must stay green
  as-is (regression gate).

Bare-`gpu`/config resolution is the previously-designed resolver
(superseded doc §7b) — unchanged, now also consulted by the DAP launch
config and the doctor.

## 9. Notebook/Lab

As the superseded doc §7, plus profile endpoints:
`POST .../debug/profile/begin`, `POST .../debug/profile/end` →
`ProfileReport` JSON. `%profile` cell magic = begin/execute/end around one
cell, report appended to the cell's outputs.

## 10. Documentation deliverables (land WITH the code, not after)

1. **Grammar reference** (`doc/07_guide/quick_reference/syntax_quick_reference.md`):
   trait `with` groups, generated `.from()`, `@init_phase`.
2. **Library-authoring guide** (new
   `doc/07_guide/language/capability_library_authoring.md`): when to define
   a core trait vs enhanced trait vs group; accessor rule ("accessors live
   on the core trait"); CapLevel honesty rules; critical-mode implications;
   worked example = this very feature.
3. **Skills**: update `.claude/skills/` (and `.codex`/`.gemini` mirrors per
   repo convention) — a `capability_interfaces` skill (how to write/extend
   capability libs) and updates to the gpu/notebook skill entries for
   debug/profile.
4. **LLM wiki**: `doc/00_llm_process/feature_expert/debug_profile/skill.md`
   (new hub) + layer_expert updates where the DAP/interpreter layers are
   touched — per the repo's "wiki ships with the commit" rule.
5. **DAP guide**: custom profile requests + target selection documented in
   the existing mcp/dap guide location.
6. Grammar/feature request doc for the trait-`with` extension filed under
   `doc/02_requirements/language/` per the repo's feature-request flow
   (the parser/desugar stream implements against it).

## 11. Definition of done

- Trait groups parse (`with` clause), desugar, blanket-satisfy, and
  `.from()` generates — unit-tested in the desugar/parser suites; zero new
  tokens confirmed by the grammar diff.
- `DebugSessionCore`/`DebugTarget`/`ProfileTarget` + ref/host/cuda/vulkan/
  metal implementations, lint clean.
- Debug conformance vectors: ref + live cuda + live vulkan green; metal
  skip-path asserted (device pass pending first Mac run — tracking doc).
- Profile conformance vectors: `steps` exact on ref + live cuda + live
  vulkan; Native `device_ns` sane on both; metal unit tests green on Linux.
- `debug-doctor` prints the true matrix on this host (host+cuda+vulkan
  rows real, metal skip row) — its spec asserts the host row's Native
  entries.
- DAP: existing local specs unchanged green; target-neutral session
  unit-tested vs ref; one live-CUDA DAP round trip; profile custom
  requests round-trip.
- Critical-mode lint: fires as `warn` on a fixture using `.from()` outside
  `@init_phase`; promotes to error under `dynamic_acquire: error`; manifest
  pin + boot mismatch refusal tested with a fake probe.
- All §10 docs/skills/wiki landed in the same commits as their code.
- No regression across: existing DAP specs, all 4 GPU lane/notebook suites,
  desugar/parser suites.
