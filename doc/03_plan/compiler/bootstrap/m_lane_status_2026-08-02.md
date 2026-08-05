# M-lane status reconstruction (M2, M4-M8) — 2026-08-02

Research/reporting pass. **No lane was implemented by this pass; nothing was
changed outside this file.** No bootstrap was run (explicitly out of scope).

## 0. Where the M-lane plan actually lives

The M lanes are **not** in
`doc/03_plan/compiler/bootstrap/stage4_memory_parallel_agent_plan_2026-07-29.md`
(that one defines L1-L7 only). They are in its **successor plan**:

> **`doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`**
> — defines M1-M8 plus two cross-cutting requirements (allocator-model
> coverage across all four models; zero-overhead-when-off HARD RULE).

Found via the M3 clue exactly as expected: M3 produced
`src/lib/common/mem_infra/config.spl`, whose header and specs cite that plan.

Supporting docs:

| Doc | Path |
|---|---|
| Plan (M1-M8) | `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md` |
| Lane state (agent) | `.spipe/stage4_memory_harden/state.md` § "M-plan status" |
| Pure-Simple parity audit | `doc/03_plan/runtime/memory_analysis/pure_simple_parity_worklist_2026-07-29.md` |
| M2 design | `doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md` |
| M4 design | `doc/05_design/compiler/backend/m4_llvm_mem_infra_design.md` |
| M5 design | `doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md` |
| M7 design (GC+GPU) | `doc/05_design/runtime/memory_analysis/gc_gpu_instrumentation_design.md` |
| M8 design | `doc/05_design/app/mem_cli/m8_simple_mem_cli_design.md` |
| M8 requirement | `doc/02_requirements/runtime/memory_analysis/feature_simple_mem_cli.md` |

**`.spipe/stage4_memory_harden/state.md` is STALE.** It is dated 2026-07-29 and
is superseded by at least four later commits (`0917eee9b93`, `a9e61476da9`,
`988ba740cce`, `8480180d37a`, `ef00d5e2094`). Several of its "not implemented"
lines are wrong today (e.g. it says `SIMPLE_AST_GEN_HARDEN` is unimplemented; it
is implemented). Do not read it as current.

### What M3 actually produced (the clue that located the plan)

M3 is genuinely landed, and is the strongest artifact of the campaign:

- `src/lib/common/mem_infra/config.spl` (160 lines) — the capability matrix
  (7 rows × 3 backends: attr, guard, harden, genarena, strict, asan, memprof),
  `resolve_mem_infra()` with graceful degradation + `--mem-infra-strict`, and
  `mem_infra_env_assignments()` mapping rows to the pre-existing env gates
  (`SIMPLE_MEM_ATTR=1`, `SIMPLE_MEM_HARDEN=1`, `SIMPLE_MEM_GUARD_RATE=64`,
  `SIMPLE_AST_GEN_CHECK=1` + `SIMPLE_GEN_ARENA_CHECK=1`, `SIMPLE_STRICT_MEM=1`,
  and `BUILD:asan` / `BUILD:memprof` markers).
- CLI wiring: `src/app/cli/_CliMain/args_and_os_commands.spl` (parse),
  `src/app/cli/_CliMain/main_and_help.spl:86-100` (`apply_mem_infra_flags`),
  `src/app/cli/cli_helpers.spl:151` (help text).
- Specs: `test/01_unit/lib/mem_infra/config_spec.spl`,
  `test/03_system/check/mem_infra_flag_spec.spl`.

**Caveat on M3's "completed" status** — two real holes, both documented below in
§1 (guard row is a false capability claim) and §7 (the flag is unreachable from
the deployed binary).

---

## Cross-cutting finding: the whole M3/M8 user surface is unreachable today

`--mem-infra=` and `simple mem` exist **only in the pure-Simple CLI**
(`src/app/cli/`, `src/app/mem/`). The deployed `bin/simple` is the **Rust seed**
(probe: `strings bin/simple | grep -c "enum construction: unregistered enum"`
→ **0** = Rust driver), and the seed does not carry that CLI.

Measured live, 2026-08-02, against deployed `bin/simple` (**SEED evidence**):

```
$ bin/simple --mem-infra=guard,strict run test/fixture/mem_infra/attr_enabled_probe.spl
error: file not found: --mem-infra=guard,strict

$ bin/simple mem help
error: file not found: mem

$ bin/simple --help | grep -ci "mem-infra"
0
```

So: the M3 flag and the M8 `mem` subcommand are **implemented but not
deliverable** until a self-hosted redeploy. This is the one place where the
M-lane campaign genuinely is blocked on the bootstrap — for *reachability*, not
for *implementation*. Every lane's underlying mechanism can still be written and
unit-tested without a bootstrap.

## Evidence basis — what was actually run

All spec runs below went through the deployed `bin/simple`, i.e. the **Rust
seed**. Label them seed evidence; they are not self-hosted evidence. Verdicts
taken from the authoritative `Results:` line, not from a checkbox.

| Spec | Result | Exit |
|---|---|---|
| `test/01_unit/lib/mem_infra/config_spec.spl` | 12/12 PASS | 0 |
| `test/01_unit/lib/mem/gen_arena_spec.spl` | 5/5 PASS | 0 |
| `test/01_unit/lib/mem/gen_arena_report_spec.spl` | 4/4 PASS | 0 |
| `test/01_unit/compiler/interp/mem_guard_rate_spec.spl` | 3/3 PASS | 0 |
| `test/01_unit/compiler/interp/mem_harden_spec.spl` | 3/3 PASS | 0 |
| `test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl` | 4 examples / 9 PASS | 0 |
| `test/01_unit/lib/gpu/mem_profile_device_counters_spec.spl` | 3 examples / 9 PASS | 0 |
| `test/03_system/app/mem_cli_spec.spl` | 7/7 PASS | 0 |
| `test/03_system/check/mem_infra_flag_spec.spl` | 3/3 PASS | 0 (needs `--timeout 600`; at the default it exits 255 with no verdict) |

**NOT run by this pass:** the Rust-side `cargo test` suites for
`interpreter_extern/{mem_guard,memory,gpu}.rs` and `runtime/src/value/heap.rs`;
any C-runtime harden test; any overhead re-measurement; any bootstrap stage.
Claims about those below come from **reading source**, and are labelled so.

---

## M2 — sampled guard pages + hardened debug allocator

**Spec:** yes — plan §M2, plus design
`doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md` (177 lines).

**Code that exists:**

| Path | What it does |
|---|---|
| `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs` (249 lines) | Real GWP-ASan-style sampled guard allocator: `mmap` slot with `mprotect(PROT_NONE)` leading + trailing guard pages, right-aligned user pointer, `guard_free_sampled` `PROT_NONE`s the whole mapping (UAF traps), owner tag carried, `SIMPLE_MEM_GUARD_RATE=N` cached in a `OnceLock` (0/unset = off). Has in-file `#[cfg(test)]` tests. |
| `src/compiler_rust/compiler/src/interpreter_extern/memory.rs` (991 lines) | Hosted quarantine ring + poison-on-free (`SIMPLE_MEM_HARDEN=1`), `rt_mem_harden_check` / `rt_mem_guard_stats` externs. |
| `src/runtime/runtime_memory.c:170-290` | **C-side harden mirror** — `SIMPLE_MEM_HARDEN=1` cached via one `getenv`, 8-byte size header, `0xDE` poison on free, fixed-size FIFO quarantine ring, tamper scan for post-free writes, double-free of a quarantined block refused. |
| `src/compiler/10.frontend/core/_Ast/module_state.spl:51,91,98` | `SIMPLE_AST_GEN_HARDEN=1` arena-generation harden gate (the L6 extension). **Landed since `.spipe` state said "not implemented".** |

**Genuinely done vs claimed done:**

- Done, verified by running: interpreter-side guard sampling and harden gates —
  `mem_guard_rate_spec` 3/3 and `mem_harden_spec` 3/3 PASS on the seed.
- Done, verified by **reading only** (not run): the C `rt_alloc`/`rt_free`
  harden path, and the `SIMPLE_AST_GEN_HARDEN` arena gate. Both are real code
  with real logic, not stubs. I did not execute either.
- **NOT done — and the matrix lies about it.** The guard-page allocator exists
  **only in the Rust interpreter extern**. Measured: `grep -c MEM_GUARD
  src/runtime/runtime_memory.c` → **0**. But `config.spl:34` declares
  `MemInfraRow(name: "guard", interpreter: true, cranelift: true, llvm: true)`.
  So `--mem-infra=guard` on a native build exports `SIMPLE_MEM_GUARD_RATE=64`
  that **nothing reads** — a silent no-op presented as a safety capability.
  Filed: `doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md`
  (status OPEN).
- **NOT done — exit criteria unmet.** Plan §M2 exit is "seeded UAF fixtures
  (malloc AND stale-slot AND after-sweep) each trapped with attribution." Only
  the malloc class has fixtures (`test/fixture/mem_infra/{guard_rate_workload,
  harden_poison_workload}.spl`). No stale-slot UAF fixture, no after-sweep
  fixture, and no fixture asserts that the trap carries the owner attribution.
- **NOT done — cross-cutting req 2 unmet at the campaign level.** The plan's own
  §"Overhead measurements" records M1's ON-path at **+50.5% pooled** against a
  **<15% target**, and concludes a structurally different approach (batched or
  per-thread-accumulate attribution) is needed. Since guard/harden reporting
  rides on M1's attribution, that open number sits under M2 too.

**Remains, concretely:**
1. Port the guard-page allocator into `src/runtime/runtime_memory.c` (mirror of
   `mem_guard.rs`) so `guard` is true on cranelift/llvm — **or** flip
   `config.spl:34` to `cranelift: false, llvm: false` and close the bug. Do one
   of the two; shipping the current matrix is a false safety claim.
2. Add the stale-slot and after-sweep UAF fixtures; assert owner attribution in
   all three trap paths.
3. Seed-interpreter extern parity for `rt_mem_guard_stats`/`rt_mem_harden_check`
   (per the parity worklist).

**Blocked on bootstrap?** **No.** All of the above is C, Rust-seed, and
pure-Simple work testable without a self-hosted binary. Only exposing it via
`--mem-infra=guard` needs the redeploy.

---

## M4 — LLVM lane (asan + memprof)

**Spec:** yes — plan §M4, plus design
`doc/05_design/compiler/backend/m4_llvm_mem_infra_design.md` (137 lines).
(Note: `.spipe` state says "No design doc yet" — stale; the doc exists.)

**Code that exists:**

- `src/lib/common/mem_infra/config.spl:38-39` — `asan` and `memprof` matrix rows
  (llvm-only, correctly `false` on interpreter/cranelift), degradation fallback
  to `harden`/`attr` at `config.spl:69-72`, and `BUILD:asan` / `BUILD:memprof`
  markers at `config.spl:156-159`.
- `src/app/cli/_CliMain/main_and_help.spl:87` — the markers **print a notice and
  do nothing else**, self-documented in the source: *"`BUILD:*` markers
  (asan/memprof) have no runtime env knob yet, so they only print a notice."*

**Pre-existing, NOT part of M4** (do not count these as lane progress):
`src/compiler/90.tools/leak_check/` (external `asan`/`valgrind` leak-check
driver) and `src/app/compile/native.spl:359,435`
(`-fsanitize=address,leak -fno-omit-frame-pointer -g` behind an existing
`sanitize` flag). These predate the lane and are not wired to `--mem-infra`.

**Genuinely done vs claimed done:** the *interface* is done (matrix rows +
degradation + notice). The *lane* is not started: measured
`grep -rn "fmemory-profile" src/` → **zero hits anywhere**. There is no memprof
emission, no profile artifact, and no `--mem-infra=asan` build path.

**On the "blocked" claim:** `doc/08_tracking/bug/m4_llvm_feature_link_failure_2026-07-30.md`
is resolved as **not reproducible** — the seed's `cargo build --release -p
simple-driver --features llvm` succeeds, and the earlier "62 undefined symbols"
framing was a conflation with a *different* problem (the pure-Simple compiler's
**stage-2 LLVM link**, tracked in
`seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`). So M4 is not blocked
where it was believed to be blocked.

**Remains, concretely:**
1. Wire `BUILD:asan` to an actual native test-build path (the `sanitize` flag in
   `src/app/compile/native.spl` is the obvious hook) and prove it catches the M2
   malloc fixture.
2. Emit `-fmemory-profile` on the LLVM path and store the raw profile for a
   later PGHO feed; produce one for a stage-2 compile of a small corpus.

**Blocked on bootstrap?** **Partly.** Item 1 (asan on native test builds through
the existing clang invocation) is independently workable. Item 2's plan-stated
exit — "memprof profile produced for a **stage-2** compile" — needs a working
stage-2 LLVM link, which is a separate open bootstrap defect. Cranelift remains
the working stage-2/3 backend.

---

## M5 — strict interpreter mode (Miri-lite)

**Spec:** yes — plan §M5, plus design
`doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md`
(160 lines). (`.spipe` state says "no code landed" — **stale**, code has landed.)

**Code that exists:**

| Path | What it does |
|---|---|
| `src/compiler_rust/compiler/src/value.rs:271-291,325` | `SIMPLE_STRICT_MEM=1` gate, `strict_mem_enabled()` (`OnceLock<bool>`, cached — satisfies the hard rule), `strict_mem_enable()`. |
| `src/compiler_rust/compiler/src/interpreter/node_exec.rs:220-225` | Under strict mode, an initializer-less `let` leaves the name **uninit** (no overlay entry) so a later read traps. |
| `src/compiler_rust/compiler/src/hir/lower/lowerer.rs:252` | `with_strict_memory_mode()`. |
| `src/compiler/70.backend/backend/env.spl:48-95` | **Pure-Simple parity**: `EvalContext.strict_mem` cached once, `mark_uninit`/`is_uninit`/`clear_uninit`, all skipped when the flag is off. |
| `src/compiler/70.backend/backend/interpreter.spl:25-33,138-139,330-332` | `interp_strict_mem_enabled()` read once in `process_module()`, uninit-read trap at the deref site. |

**Genuinely done vs claimed done:** **one of four defect classes.** Verified by
running: `interpreter_strict_mem_spec.spl` 4 examples / 9 assertions PASS (seed).
Verified by reading: the implementation covers **uninitialized-read traps** only.
The plan's other three classes have **no implementation found**:

- poison-on-free — no strict-mode poisoning path;
- arena provenance + generation enforcement **on every index deref** (the plan
  is explicit: "not just tag reads") — the existing `SIMPLE_AST_GEN_CHECK` /
  `SIMPLE_GEN_ARENA_CHECK` are the L6/M6 tag-read checks, not deref-site
  enforcement;
- GC-tier dangling-survivor checks — none.

Plan exit ("each defect class has a fixture that passes normally and traps under
strict") is met for 1 of 4.

**Remains, concretely:** implement the three missing classes with a
passes-normally/traps-under-strict fixture each, in both the Rust seed and the
pure-Simple interpreter (parity is already the established pattern here). Note
the design doc's GC row may be trivially satisfiable — the M7 design's own
verdict is that the GC is vestigial with no tracing collector over program
values; if so, say so explicitly rather than leaving the row silently unmet.

**Blocked on bootstrap?** **No.** This is pure-Simple `src/compiler/70.backend/`
work plus its Rust-seed mirror, and its spec already runs green on the seed.

---

## M6 — stdlib generational slotmap (`std.mem.gen_arena`)

**Spec:** yes — plan §M6.

**Code that exists:** `src/lib/nogc_sync_mut/mem/gen_arena.spl` (151 lines) —
`GenArena<T>` with Vale-style generational handles and a
`SIMPLE_GEN_ARENA_CHECK=1` diagnostic gate. Specs
`test/01_unit/lib/mem/gen_arena_spec.spl` and `gen_arena_report_spec.spl`.

**Genuinely done vs claimed done:** the library itself is real and green —
5/5 and 4/4 PASS on the seed (run). But `.spipe` state marks M6 **"DONE"** and
that is **overstated on two of the plan's own criteria**:

- **"Migrate one ECS store as proof" — NOT done.** Measured:
  `grep -rln "GenArena\|gen_arena" src/ --include=*.spl` returns **exactly one
  file — `gen_arena.spl` itself.** The library has **zero consumers** in the
  tree. The "proof" half of the lane was never executed.
- **"checks default-on in debug tier, compiled out in release / zero-cost
  release" — unproven.** The gate is an env read (`SIMPLE_GEN_ARENA_CHECK`),
  which is a runtime branch, not a compile-out. No release-tier zero-cost
  measurement is on record. I did not measure it.

**Remains, concretely:** (1) migrate one real ECS store onto `GenArena` and keep
a stale-handle fixture that traps in debug; (2) either demonstrate the checks
actually compile out in the release tier, or amend the plan to say they are
runtime-gated.

**Blocked on bootstrap?** **No.** Pure stdlib + one consumer.

---

## M7 — GPU lane (CUDA/HIP)

**Spec:** yes — plan §M7, plus design
`doc/05_design/runtime/memory_analysis/gc_gpu_instrumentation_design.md`
(188 lines, covers both the GC row and the GPU row).

**Code that exists:**

| Path | What it does |
|---|---|
| `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:34-74,1200,1210` | Device-alloc choke point: `note_device_alloc`/`note_device_free` over a `Mutex<HashMap<u64,u64>>`, exposed as `rt_gpu_mem_live_bytes()` / `rt_gpu_mem_peak_bytes()`, wired into the two real device-alloc sites. Underflow-safe on an untracked free. Has `#[cfg(test)]` tests needing no GPU. |
| `src/lib/nogc_sync_mut/gpu_profile/mem_profile.spl` (243 lines) | `run_under_compute_sanitizer(tool, cmd)` — subprocess wrapper, returns `("", "compute-sanitizer not found", 127)` when absent rather than failing hard; `device_trace_to_memory_viz` serializer. |

**Genuinely done vs claimed done:** the counters are real (spec
`mem_profile_device_counters_spec.spl` 3 examples / 9 PASS on the seed — but note
those tests exercise the counter arithmetic and need no GPU, so they say nothing
about device behaviour). The rest of the lane is **honestly self-declared
incomplete in its own source header**, and I confirm by reading:

- `mem_profile.spl:13-17` — the trace emits **our own** `"simple-gpu-trace v1"`
  schema, **NOT** a verified PyTorch `memory_viz` payload; no viewer test has
  ever run against a real `memory_viz` build. Plan exit "snapshot opens in
  memory_viz" is **unmet and known-unmet**.
- `--mem-infra=gpu-sanitize` is **not a matrix row.** `config.spl` has seven
  rows and none of them is `gpu`. The wrapper function exists with no route to
  it from the flag the plan names.
- Plan exit "seeded device leak + OOB fixtures caught" — **no such fixtures
  exist**; nothing has been run on GPU hardware.
- No `simple mem gpu` verb (see M8).
- Per the design's own verdict, the **GC** half of the row is satisfied
  *trivially* (the GC is vestigial — no tracing collector over program values).
  That is a defensible answer, but it means "GC coverage" in the cross-cutting
  allocator-model requirement is satisfied by absence, not by instrumentation.

**Remains, concretely:** add a `gpu`/`gpu-sanitize` matrix row and route it to
the wrapper; seeded device-leak and device-OOB fixtures; per-pool stats via
`cudaMallocAsync` pools / `cuMemPoolGetAttribute` + NVML (the plan asks for these
and none are present); either verify the snapshot against a real `memory_viz`
build or rename the claim; ROCm/HIP equivalent.

**Blocked on bootstrap?** **No** — but blocked on **GPU hardware access**, which
is a different and equally hard gate. Everything above the device boundary
(matrix row, wrapper routing, schema) is workable today.

---

## M8 — `simple mem` CLI

**Spec:** yes — plan §M8, design `doc/05_design/app/mem_cli/m8_simple_mem_cli_design.md`,
requirement `doc/02_requirements/runtime/memory_analysis/feature_simple_mem_cli.md`.

**Code that exists:** `src/app/mem/main.spl` (verb dispatch, TSV snapshot
parsing, top-N table, snapshot diff), `src/app/mem/top_tui.spl`,
`src/app/mem/live_poll.spl`, `src/lib/nogc_sync_mut/mem/dump.spl` (v1 TSV
snapshot + SIGUSR2 hook in `signal_handlers.spl`),
`src/app/memstat/main.spl` (the L5 sampler it delegates to).
Dispatch arm at `src/app/cli/_CliMain/main_and_help.spl:504`.

**Genuinely done vs claimed done — this is the largest gap between checkbox and
reality in the campaign.**

The plan (and its embedded status line) says M8 is **"LANDED / COMPLETE / verb
dispatch complete"**. Verbs actually implemented (`src/app/mem/main.spl:396-412`,
`cmd_*` at lines 199/288/327/357/377):

`top`, `diff`, `snapshot`, `gate`, `sample`, `help`

The plan requires: `simple mem top|snapshot|diff|**trace**|**gpu**|gate`.

- **`trace` does not exist.** No `cmd_trace`, not in `print_help()`.
- **`gpu` does not exist.** Measured: `grep -rn "gpu" src/app/mem/*.spl` →
  **zero hits**. `.spipe` state calls it "a stub"; it is not a stub, it is
  absent.
- The claim *"all help-listed verbs dispatch explicitly"* is **true but
  circular** — `print_help()` lists only the verbs that were implemented, so the
  claim cannot fail regardless of scope coverage. This is the checkbox that
  most needs distrusting.
- The plan's own exit criterion — `simple mem trace prog.spl` then
  `simple mem top --profile <file>` — is **not executable**, because `trace`
  does not exist and (per the cross-cutting finding) `simple mem` is not
  reachable from the deployed binary at all.
- `mem_cli_spec.spl` 7/7 PASS (run, seed) — but the spec's own header states it
  invokes `simple run src/app/mem/main.spl <args>`, i.e. it drives the module
  directly and **never exercises the `simple mem` dispatch arm**. Green here is
  compatible with the subcommand being entirely unreachable, which it currently
  is.

Genuinely working (post-mortem file mode): top-N by live bytes from a snapshot
file, two-file diff, snapshot write, gate delegation, sampler delegation.

**Remains, concretely:** implement `trace` (record) and `gpu` (M7 device rows);
live-process polling (`top --pid` without MCP); the interactive TUI render path;
and add a spec that drives `simple mem <verb>` through the real dispatch arm
rather than the module path.

**Blocked on bootstrap?** **For delivery, yes** — `simple mem` cannot be invoked
until a self-hosted `bin/simple` is redeployed. **For implementation, no** — the
missing verbs are pure-Simple code in `src/app/mem/`, developable and
spec-testable today via the `simple run src/app/mem/main.spl` path the existing
spec already uses.

---

## Summary table

| Lane | Spec found | Code exists | Real status | Bootstrap-blocked |
|---|---|---|---|---|
| **M2** guard+harden | yes (plan §M2 + design) | yes — `mem_guard.rs`, `memory.rs`, `runtime_memory.c`, `module_state.spl` | **Partial.** Interpreter guard+harden real and green; C **harden** landed but C **guard page absent** while the matrix claims it (OPEN bug = false safety claim). 1 of 3 required UAF fixture classes. | No (delivery via `--mem-infra` only) |
| **M4** LLVM asan/memprof | yes (plan §M4 + design) | interface only — matrix rows + `BUILD:*` notice | **Not started.** Zero `-fmemory-profile` hits tree-wide; no asan build path. Prior "blocked on 62 symbols" was a misdiagnosis (seed `--features llvm` builds). | Partly — memprof exit needs stage-2 LLVM link; asan half does not |
| **M5** strict interp | yes (plan §M5 + design) | yes — seed `value.rs`/`node_exec.rs` + pure-Simple `env.spl`/`interpreter.spl` | **1 of 4 defect classes.** Uninit-read traps done and green; poison-on-free, per-deref arena provenance, GC dangling-survivor all missing. | No |
| **M6** gen slotmap | yes (plan §M6) | yes — `gen_arena.spl`, 2 green specs | **Overstated as DONE.** Library real; **zero consumers** — the "migrate one ECS store as proof" exit was never done; release zero-cost unproven. | No |
| **M7** GPU lane | yes (plan §M7 + design) | yes — `gpu.rs` counters, `mem_profile.spl` sanitizer wrapper | **Counters only.** No `gpu` matrix row, no device fixtures, no pool stats/NVML, `memory_viz` compatibility explicitly unverified in-source. GC row satisfied by absence. | No — blocked on **GPU hardware** |
| **M8** `simple mem` CLI | yes (plan §M8 + design + requirement) | yes — `src/app/mem/*`, `mem/dump.spl` | **Overstated as COMPLETE.** `trace` and `gpu` verbs **absent** (not stubs); "all help-listed verbs dispatch" is circular; spec bypasses the real dispatch arm. Post-mortem top/diff/snapshot/gate/sample work. | For delivery yes; for implementation no |

## Corrections this report makes to existing status text

1. `.spipe/stage4_memory_harden/state.md` is stale (2026-07-29, superseded by
   ≥5 later commits). Specifically wrong today: M2's `SIMPLE_AST_GEN_HARDEN`
   ("not implemented" — it is), M4's "no design doc yet" (there is one), M5's
   "no code landed" (code landed), M8's `gpu` "is a stub" (it is absent).
2. The plan doc's inline M8 status line overstates completion — see §M8.
3. M6's "DONE" overstates completion — zero consumers, exit criterion unmet.
4. M4's historical "blocked on 62 undefined LLVM symbols" is a conflation of two
   different failures; see `m4_llvm_feature_link_failure_2026-07-30.md`.

## Recommended order (if the campaign resumes)

Nothing here is gated on running a bootstrap, so the sequencing is by risk:

1. **M2 matrix truth** — port the C guard page **or** flip the two matrix
   booleans. A false safety claim shipping in a memory-debugging tool is the
   highest-severity open item in the campaign.
2. **M6 consumer** — cheapest close; one ECS migration converts an overstated
   DONE into a real one.
3. **M5 remaining three classes** — highest capability-per-effort, pure-Simple.
4. **M8 `trace`** — unblocks the plan's own end-to-end exit criterion.
5. **M4 asan half**, then **M7** when hardware is available.

Independently of all five: the M1 attribution ON-path is **+50.5% against a
<15% target**, and the plan concludes no lock-shape variant will close it. Every
lane that reports through attribution inherits that. It should be re-scoped or
re-targeted explicitly rather than left as a standing open number.
---

# Addendum 2026-08-04 — M6 and M8 exit criteria CLOSED (sabotage-verified)

This addendum supersedes the M6 and M8 rows of the summary table above. Both
lanes' stated exit criteria are now **met**, and — unlike the original "DONE"
marks — each is backed by a **sabotage cycle**: break what the test covers,
observe RED, restore, observe GREEN. Green-both-ways is exactly how M6/M8 were
mismarked the first time, so a green run alone was not accepted as evidence.

**Binary identity:** all runs below used `bin/simple`, which is the **RUST
SEED** (`strings bin/simple | grep -c "enum construction: unregistered enum"`
= 0; a bootstrap binary answers 2). Every run passed `--no-session-daemon`,
because a persistent test daemon freezes its environment at daemon start and
would serve a previous run's env to the spec.

## M6 — generational slotmap: consumer migrated, stale handles proven rejected

**Exit criterion (plan §M6):** "migrate one ECS store as proof."

**Met.** `WmWorld` (the window manager's ECS world,
`src/os/services/wm/wm_world.spl`) now holds its window registry as
`win_handles: GenArena<u64>`. `GenArena` is no longer a library with zero
consumers.

Deliverable test: `test/01_unit/os/services/wm/wm_world_gen_arena_stale_handle_spec.spl`
(6 examples). Each stale-handle example holds a handle across a despawn, lets a
NEW window recycle the very same arena slot, then demands the OLD handle resolve
to nothing.

| step | change | result |
|------|--------|--------|
| baseline | none | **GREEN** 6/6, exit 0 |
| sabotage | dropped `stored_gen != h.generation` from `GenArena.get` (`gen_arena.spl`) — i.e. the generation check removed, keeping only the liveness check | **RED** exit 1, 2 failures |
| restore | file byte-identical to origin | **GREEN** 6/6, exit 0 |

The sabotage was applied to the **library implementation**, not to a spec-local
shim. Independently confirmed by a deliberately-wrong-oracle probe that, with
the check removed, `window_id_for_handle(stale)` returns **4242** — the new
occupant's id — i.e. a genuine use-after-free/ABA alias. With the check present
it returns 0.

## M8 — `simple mem` CLI: `trace` and `gpu` implemented, real dispatch arm covered

**Exit criteria:** the six verbs plan §M8 requires, and a spec that can fail on
a broken CLI.

**Met at the source-entry layer** (see the reachability caveat below).
`cmd_trace` and `cmd_gpu` exist in `src/app/mem/main.spl` and are dispatched;
they are implementations, not stubs. `test/03_system/app/mem_cli_spec.spl` is
now 15 examples (was 7).

Two circularity fixes carried by that spec:
- The verb list it asserts, `PLAN_REQUIRED_VERBS`, is **hardcoded from the
  plan**, not read from `print_help()`. The old claim "all help-listed verbs
  dispatch" could not fail, because help listed exactly what was implemented.
- A second `describe` block drives the **real** dispatch arm in
  `src/app/cli/_CliMain/main_and_help.spl` (run as a source program under
  `SIMPLE_MODULE_LIMIT=0` via `env`), with a negative control asserting an
  unrelated subcommand does **not** route to the mem entry.

| step | change | result |
|------|--------|--------|
| baseline | none | **GREEN** 15/15, exit 0 |
| sabotage A | renamed the CLI dispatch tag `"mem"` -> `"mem-SABOTAGE-TAG"` | **RED** exit 1 — dispatch example fails; **the other 13 stay green**, which is precisely why the old 7/7 suite could never have caught an unreachable subcommand |
| sabotage B | renamed the `"gpu"` verb arm | **RED** exit 1, 3 gpu examples fail |
| sabotage C | renamed the `"trace"` verb arm | **RED** exit 1, 2 trace examples fail |
| restore | all files byte-identical to origin | **GREEN** 15/15, exit 0 |

### Reachability caveat — state the layer, do not overclaim

Verified layer: **pure-Simple source entry**. `--mem-infra=` and the `simple mem`
subcommand exist only in the pure-Simple CLI. The deployed `bin/simple` is the
Rust seed and answers `bin/simple mem help` with `error: file not found: mem`.
Implementation and routing are proven; **end-to-end delivery through the
deployed binary still needs a self-hosted redeploy** and is NOT claimed here.

## Test-runner semantics discovered while verifying (affects how any sabotage is read)

`bin/simple test` reports **only the LAST failure per example**, and a failing
`expect` does **not** abort the rest of the example body. Verified with a
three-example probe: an example containing two failing expects printed only the
second one.

Consequence for anyone reading a sabotage log: an example showing one failure
message may have failed several assertions. During M6 verification this made the
headline read `expected 0 to be greater than 0` (the rejection counter, the last
assertion) rather than `expected 4242 to equal 0` (the stale-id check just above
it) — both fired. **Count failing examples, not failure messages.** As always,
bare `assert x == y` in an `it` block is inert; these specs use
`expect` / `assert_true` / `assert_false` throughout.

---

# Addendum 2026-08-05 — M5 (poison-on-free class) and M7 (gpu row + real-hardware
fixture) advanced, sabotage/hardware-verified

Scope note: this pass deliberately did NOT attempt a full bootstrap (two
sibling sessions were already running full-bootstrap attempts concurrently;
see their own reports for stage-3/4 status, which this pass does not touch).
Verification below is a scoped `cargo test -p simple-compiler --lib` build
(Rust seed only, ~4-5 min, no cargo/rustc changes beyond the files listed)
for M5, and a real-hardware run of the existing deployed seed `bin/simple`
for M7 — never a from-scratch bootstrap.

## M5 — strict interpreter mode: 2 of 4 defect classes now covered

The original finding (§M5 above) was 1 of 4 (uninit-read only). Reading the
design doc's own §5 ("what is NOT worth doing") narrows the honest target:
it explicitly rules out a **separate** GC-tier dangling-survivor mechanism —
"strict mode implies harden's GC behavior rather than adding a parallel
path" — so the real remaining scope was always 2 classes, not 3:
poison-on-free (design §3, "stale-state, not stale-memory") and arena
provenance at the SFFI boundary (design §4).

**Landed this pass: poison-on-free / stale-state class, via design §3.2**
("block-env write-back replay" — the `copy_back_block_writes` dirty-names
invariant, described in the design doc as "a regression lock on the
invariant that already broke once").

- `src/compiler_rust/compiler/src/value.rs` — `CowEnv::check_dirty_names_invariant()`
  (new method, ~line 613): returns the first name that is marked dirty but
  absent from the env's own `overlay`, i.e. exactly the state shape the
  historical bug ("copying every shared key instead of only `dirty_names`
  replayed a cloned block env's stale snapshot over values a deeper call had
  since written") could produce. Also adds a `#[cfg(test)]`-only
  `test_mark_dirty_without_overlay()` escape hatch to construct that state
  directly for testing, without needing to reintroduce the historical bug in
  production code.
- `src/compiler_rust/compiler/src/interpreter/block_exec.rs` — new
  `pub(crate) fn assert_dirty_names_invariant(block_env: &Env)`, split out of
  `copy_back_block_writes` specifically so it is testable without touching
  the process-global `strict_mem_enabled()` gate (see below); panics naming
  the offending key when the invariant is violated.
  `copy_back_block_writes` calls it exactly when `strict_mem_enabled()` is
  true (off-path cost: one relaxed bool load, matching the design's
  zero-overhead-when-off requirement).
- `src/compiler_rust/compiler/src/interpreter/mod.rs` — re-exports
  `assert_dirty_names_invariant` crate-wide (mirrors the existing
  `block_exec::{...}` re-export line) so it is reachable from the lib's
  shared unit-test binary.

**A note on where the test lives, and why (important for anyone extending
this further):** `strict_mem_enabled()` is backed by a process-global,
once-set-never-unset `AtomicBool`
(`STRICT_MEM_FORCED`/`strict_mem_enable()`). The existing M5 uninit-read test
(`src/compiler_rust/compiler/tests/interpreter_strict_mem_test.rs`) already
documents this hazard and isolates itself in its **own integration-test
binary/process** for exactly that reason. This pass's new tests live in the
`--lib` unit-test binary instead
(`src/compiler_rust/compiler/src/value_tests_strict_mem.rs`, wired in via
`value_tests.rs`'s existing `include!` chain) — **and deliberately never call
`strict_mem_enable()`**, because that binary is shared with ~3,600 other
`#[cfg(test)]` tests across the crate and flipping a global latch there would
leak into tests cargo runs in an unspecified order. That is exactly why
`assert_dirty_names_invariant` was split out of `copy_back_block_writes`: it
lets the panic-on-violation behavior be exercised directly and unconditionally
(gate-free), while `copy_back_block_writes` itself still gates the *call* on
`strict_mem_enabled()`.

**Sabotage-cycle proof (Rust unit level, not a rebuild-and-diff cycle — the
defect state is constructed directly via the test-only hatch, which is the
correct level for a mechanism that is entirely Rust-internal bookkeeping, not
user-visible `.spl` behavior):**

```
cargo test -p simple-compiler --lib dirty_names -- --test-threads=1
```

```
running 6 tests
test value::tests::assert_dirty_names_invariant_is_silent_when_invariant_holds ... ok
test value::tests::assert_dirty_names_invariant_traps_on_violation - should panic ... ok
test value::tests::dirty_names_invariant_catches_the_historical_violation_shape ... ok
test value::tests::dirty_names_invariant_holds_after_a_real_write ... ok
test value::tests::dirty_names_invariant_holds_on_a_fresh_env ... ok
test value::tests::dirty_names_invariant_ignores_a_correctly_written_name_alongside_a_bad_one ... ok

test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 3636 filtered out
```

`dirty_names_invariant_catches_the_historical_violation_shape` and
`assert_dirty_names_invariant_traps_on_violation` are the RED/GREEN pair:
without the fix (predicate absent, or the panic call removed from
`copy_back_block_writes`), the exact violation state these tests construct
would silently propagate a stale value upward instead of trapping — that is
the pre-fix bug this invariant guards against, by the design doc's own
account of the bug `block_exec.rs` was already patched for once.

**Still open (unchanged from the original finding): arena provenance +
generation enforcement at the SFFI boundary (design §4)** — threading a
`nodes.spl`-minted `(idx, gen)` pair into `interpreter_extern` calls so a
stale index fails at the boundary. Not attempted this pass; scoped as a
separate, larger change (touches the SFFI call-site shape, not just
`value.rs`/`block_exec.rs`). GC-tier stays "satisfied by design's own
argument, not by new code" per §5 above — restated here rather than left
implicit, per the original finding's own instruction to do so.

**Blocked on bootstrap?** No — this is Rust-seed-only work, verified without
a bootstrap (scoped `cargo test -p simple-compiler --lib`, ~4-5 min each of
two runs this pass). No pure-Simple parity work was attempted for this class
this pass (the existing uninit-read class already has parity in
`src/compiler/70.backend/backend/{env,interpreter}.spl`; this new class does
not yet).

## M7 — GPU lane: `gpu` capability-matrix row added, real-hardware seeded-leak fixture

The original finding: real counters (`gpu.rs` `DEVICE_ALLOCS`/
`DEVICE_LIVE_BYTES`/`DEVICE_PEAK_BYTES`, wired to
`rt_cuda_mem_alloc_fn`/`rt_cuda_mem_free_fn`), but no `--mem-infra=` matrix
row, no fixtures, "nothing has been run on GPU hardware."

**This box has 2 real CUDA devices** (RTX A6000, TITAN RTX;
`nvidia-smi -L` verified) with a working driver (`libcuda.so.1` present) —
the same machine the original M7 design doc's author found GPUs on. This
pass used that hardware directly rather than only reasoning about it.

- `src/lib/common/mem_infra/config.spl` — new `gpu` matrix row
  (`interpreter: true, cranelift: false, llvm: false`), with an in-line
  comment recording exactly what was and was not measured (piggybacks on the
  `attr`/`SIMPLE_MEM_ATTR` gate — not a separate env var; interpreter-only
  because `gpu.rs` lives under `interpreter_extern` and zero hits for
  `rt_cuda_mem_alloc`/`rt_gpu_mem_live_bytes` exist anywhere under
  `src/runtime/*.c`, so native/cranelift/llvm builds have no mirror of this
  bookkeeping today — conservative `false`, not measured-and-confirmed-false,
  stated as such). `mem_infra_env_assignments` updated to map `gpu` to the
  same `SIMPLE_MEM_ATTR=1` assignment as `attr`, deduped so requesting both
  together does not double-emit it. `config_spec.spl` re-run clean: 13/13
  (was 12/12 at the original M3 finding — a sibling lane's unrelated addition
  landed one more test between then and now; unaffected by this row).
- `test/fixture/mem_infra/gpu_device_leak_workload.spl` (new) +
  `test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl` (new, 5 examples) —
  drives the real CUDA driver-API choke points end-to-end on this box's
  hardware: a balanced alloc+free pair (negative control, must return to 0
  live bytes) followed by a **deliberately leaked** 1 MiB allocation (never
  freed). Mirrors the established `mem_guard_rate_spec.spl` pattern exactly
  (child-process `SIMPLE_MEM_ATTR=1 SIMPLE_EXECUTION_MODE=interpreter`
  invocation, forced fresh-process because the attribution gate is a
  `OnceLock` and the test daemon freezes env vars — see that spec's own
  comment) rather than inventing a new harness shape.

Raw fixture output on this hardware (`SIMPLE_MEM_ATTR=1 SIMPLE_BOOTSTRAP=1
SIMPLE_EXECUTION_MODE=interpreter bin/simple run
test/fixture/mem_infra/gpu_device_leak_workload.spl`):

```
gpu_device_leak_workload: live_before=0
gpu_device_leak_workload: live_after_balanced=0
gpu_device_leak_workload: live_after_leak=1048576
gpu_device_leak_workload: peak_after_leak=1048576
```

This is the sabotage-style proof required: the "defect" (an unfreed device
allocation) is real, on real hardware, and the counter reports it exactly
(1048576 bytes, the requested size, not some other value) while the balanced
control confirms the counter isn't just monotonically increasing regardless
of frees. Spec verdict via the deployed (seed) `bin/simple`:

```
Results: 5 total, 5 passed, 0 failed
```

**Binary identity caveat, same as the M6/M8 addendum above:** `bin/simple`
here is the Rust seed
(`strings bin/simple | grep -c "enum construction: unregistered enum"` = 0).
This pass did not build or wait on a self-hosted binary — two sibling
sessions were already running full-bootstrap attempts concurrently, and this
task's own scoping explicitly said not to duplicate that. All evidence above
is seed evidence.

**Still open (unchanged from, or narrowed from, the original finding):**
- Seeded OOB fixture (`compute-sanitizer --tool memcheck` around a kernel
  overrunning a `cuMemAlloc_v2` buffer) — not attempted this pass; the
  sanitizer wrapper (`run_under_gpu_sanitizer`) exists and is spec-covered
  for its no-GPU dispatch paths only.
- `memory_viz` viewer compatibility — still explicitly unverified in-source
  (`mem_profile.spl`'s own compatibility note), unchanged.
- NVML cross-check, per-pool stats (`cudaMallocAsync`/`cuMemPoolGetAttribute`)
  — not attempted; the design doc's own §2 already notes the pool API is not
  used anywhere in `gpu.rs` today (every alloc/free is the raw, non-pooled
  driver call).
- ROCm/HIP equivalent — not attempted (no AMD GPU on this box either).
- Whether the counters genuinely move under a **native** (cranelift/llvm)
  build is unverified either way (see the `config.spl` row comment) — this
  pass chose conservative-false over an unverified claim rather than
  investing in a native-build measurement given the harness-contention
  scoping for this task.

**Blocked on bootstrap?** No for everything landed this pass (seed +
existing deployed binary only). The native-backend question above would need
either a scoped native-build probe or a real self-hosted redeploy to answer
either way — deferred as a follow-up, not attempted here.

---

# Addendum 2026-08-05 — M2 stale-slot and after-sweep UAF fixtures landed
(native-C guard allocator), sabotage-verified; owner-attribution filed, not
invented

This addendum supersedes the M2 row's "Remains, concretely" item 2 above
("Add the stale-slot and after-sweep UAF fixtures"). The native-C guard-page
allocator itself (`src/runtime/runtime_memory_guard.h`) landed earlier this
session (`8f3948de5ed`), closing item 1 of the original M2 finding (the
guard-row-false-on-native bug). This pass adds the two missing fixture
classes plan §M2's exit criterion names against that mechanism, and files
the owner-attribution gap rather than inventing a signal handler unreviewed.

**Exit criterion (plan §M2,
`doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
line 32-33):** "seeded UAF fixtures (malloc AND stale-slot AND after-sweep)
each trapped with attribution." The malloc class was already covered by
`rt_mem_guard_native_selfcheck.c` (immediate overflow + immediate UAF on the
same slot). This pass adds the other two:

- `src/runtime/test/rt_mem_guard_stale_slot_selfcheck.c` (new) — frees a
  slot, then churns 40 unrelated sampled alloc/use/free cycles through the
  guard mechanism (well under the 256-entry free-ring capacity), then proves
  the now-*stale* (40-alloc-old) freed slot still `SIGSEGV`s on both read and
  write — distinguishing "the bounded FIFO ring protects every resident
  freed slot" from a weaker design that only protects the single
  most-recently-freed pointer.
- `src/runtime/test/rt_mem_guard_after_sweep_selfcheck.c` (new) — forces
  4,500 sampled alloc/free cycles (> the 4,096-entry slot table and >> the
  256-entry ring), so the free ring must evict ("sweep") repeatedly and
  reclaim array slots for reuse many times over. Then positively proves the
  allocator is still fully sound post-sweep: (a) a UAF read on a slot freed
  immediately after the heavy churn still traps, (b) a fresh allocation made
  after all that sweeping is still guard-protected (one-byte overflow
  traps), and (c) `rt_mem_guard_stats()` confirms every single request
  across the run was actually sampled — no silent fallback to plain
  `malloc()` from a corrupted/exhausted slot table, which is exactly the
  failure mode a broken eviction-reclaim path would produce (silently, with
  no crash of its own).

Both fixtures follow `rt_mem_guard_native_selfcheck.c`'s existing proof
discipline exactly: every trap-shaped assertion `fork()`s, lets the child
touch the guarded byte, and asserts the **parent** observes the child die by
`SIGSEGV` (`WIFSIGNALED` + `WTERMSIG == SIGSEGV`) — never a plain flag a
sabotaged allocator could satisfy by doing nothing.

**Sabotage-cycle proof.** `runtime_memory_guard.h`'s
`rt_mem_guard_free_sampled` was edited to `mprotect(..., PROT_READ |
PROT_WRITE)` in place of `PROT_NONE` (the same sabotage class used to
originally prove `rt_mem_guard_native_selfcheck.c` non-vacuous), objects
rebuilt with the exact flags `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`
uses (`-Os -ffunction-sections -fdata-sections -fno-unwind-tables
-fno-asynchronous-unwind-tables -fno-stack-protector -fPIC -std=gnu11
-DSIMPLE_CORE_C_STANDALONE=1`), then reverted:

| fixture | real `PROT_NONE` | sabotaged `PROT_READ\|PROT_WRITE` |
|---|---|---|
| `rt_mem_guard_native_selfcheck.c` (malloc class, unchanged) | PASSED (0 failures) | *(not re-run this pass; established prior session)* |
| `rt_mem_guard_stale_slot_selfcheck.c` | PASSED (0 failures) | **FAILED (2 failures)** — both the stale read and stale write checks flip to FAIL, double-free check stays ok (orthogonal) |
| `rt_mem_guard_after_sweep_selfcheck.c` | PASSED (0 failures) | **FAILED (1 failure)** — the post-sweep-churn UAF read flips to FAIL; the overflow/canary checks stay ok because they depend on the alloc-time (not free-time) `mprotect`, which the sabotage did not touch — this is why the fixture needed its own dedicated UAF check rather than relying on the overflow check alone |

After reverting, `git diff` against `runtime_memory_guard.h` is empty and
both fixtures pass clean again on freshly rebuilt objects — confirmed before
landing.

`scripts/check/build-core-c-bootstrap-runtime-capsule.shs` is updated to
build, run, and receipt-gate both new fixtures (mirroring the existing
`rt_mem_guard_native_selfcheck` block exactly: `LOCAL_INPUTS_FILE` entries,
a build+run+`grep 'SELFCHECK PASSED'` gate with its own `die` reasons, and
manifest receipt lines). **Not run end-to-end through the pinned script
itself this pass** — the script hard-requires a byte-clean `git status` on
all of `src/runtime` (`die "runtime-source-dirty"`), and the shared working
copy carried unrelated in-flight changes from other lanes
(`runtime_renderdoc.c`, `runtime_simd_dispatch.c`) at verification time. The
manual rebuild above used the identical compiler, flags, and source-file set
the script uses, which is why it is offered as equivalent evidence rather
than a substitute claim of "ran the pinned script" — an isolated-worktree
run against `origin/main` was attempted for a true end-to-end pass but this
repository's `git worktree add` did not complete inside the available
command budget (large tree, pre-existing loose-object backlog) and was
abandoned rather than reported as done.

**Owner-attribution — filed, not implemented.** The design doc's §2 also
promises "owner name from M1" printed on the trap via a
`sigaction`-installed `mem_guard_fault_handler`. Measured: this handler does
not exist on **either** side — the Rust `GuardSlot.owner` field is captured
but `#[allow(dead_code)]` (nothing reads it), and native C's
`RtMemGuardSlot` has no owner field at all. There is no working mechanism to
port; building one is an independent, higher-risk piece (process-wide
signal handler that must coexist with existing crash handling and stay
async-signal-safe — a bug here is worse than the missing report it would
fix). Filed as
`doc/08_tracking/bug/mem_guard_owner_attribution_trap_report_missing_2026-08-05.md`
rather than landed under this pass's scope.

**Blocked on bootstrap?** No — this is pure C-runtime test/tooling work
(`src/runtime/test/*.c`, `scripts/check/*.shs`), verified via direct `cc`
invocation without any bootstrap stage.
