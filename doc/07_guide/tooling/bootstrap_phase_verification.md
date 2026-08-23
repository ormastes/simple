# Per-Phase Bootstrap Verification

Authoritative map of the full bootstrap's phases, the gate that covers each, and
— the most valuable part of this document — the phases that are **not** covered.

Umbrella command:

```sh
sh scripts/check/check-bootstrap-all-phases.shs           # selftest, then scan
sh scripts/check/check-bootstrap-all-phases.shs --list    # print the registry
sh scripts/check/check-bootstrap-all-phases.shs --selftest-only
```

The umbrella's registry is the machine-readable twin of the table below. If you
add, rename, or delete a phase gate, change both.

## Why an umbrella exists

Before this, the gates were scattered across three regimes: some invoked from
inside `scripts/bootstrap/bootstrap-from-scratch.sh`, some run only by hand, and
several never run at all by any path. No single command answered *"is every
phase of the bootstrap covered by a gate, and is every one of those gates
green?"* — so a phase could pass unverified and look identical to a phase that
was verified. That is the exact shape of
`doc/08_tracking/bug/fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`,
where a guard was silently downgraded to advisory and a tree wipe went
undetected.

## Verdict contract

Every gate in this repo, and the umbrella itself, must put its verdict on the
**last line of stdout**:

| verdict | exit | meaning |
|---------|------|---------|
| `PASS — <n> gate(s) checked, ...` | 0 | safe; `n` is always > 0 |
| `FAIL — ...` | 1 | a phase gate is red |
| `ERROR — nothing was checked` | 2 | could not determine; treat as red |

A run that evaluated 0 gates is an ERROR, never a pass. A registry entry whose
script does not exist is an ERROR, never a skip — "the gate isn't written yet"
is precisely the condition this umbrella was built to surface.

**Honest caveat, stated up front:** of the fifteen registry entries, only the
existing gates named below satisfy this contract today. See
[Gap 1](#gap-1-most-phase-gates-do-not-implement-the-verdict-contract).

## Run vs. static modes

A bootstrap takes hours and produces artifacts; an umbrella that required one
could never be run routinely, and an umbrella that is never run is not a gate.
So each registry entry declares a mode:

- **`run`** — the gate is source-static (greps, `sh -n`, its own `--selftest`)
  and is *executed*. Its exit status is the verdict.
- **`static`** — the gate needs a built artifact (a stage binary, a provenance
  receipt) that does not exist outside a real bootstrap. It cannot be executed
  here, so what is verified is that it **exists**, and **parses as POSIX shell**
  (`sh -n`). This is deliberately weaker than running it and is reported
  separately as `PRESENT`, never counted as executed. It still catches the
  failure mode that matters most for an umbrella: a phase whose gate was
  deleted, renamed, or left syntactically broken, which would make that phase's
  verification a silent no-op inside a real bootstrap run.

## Phase → gate map

| # | Phase | Gate | Mode | What it asserts |
|---|-------|------|------|-----------------|
| 0 | Preflight: shell portability | `check-bootstrap-portability.shs` | run | Every bootstrap shell/Perl helper is parseable POSIX; process-lock behavioural tests; immutable bootstrap-authority publication |
| 0 | Preflight: cache lane ownership | `check-cache-scope-ownership.shs` | run | A native build cache dir is not reused across lanes; `.cache_scope` marker matches the owning lane (has its own `--selftest`) |
| 0 | Preflight: cache policy | `scripts/bootstrap/bootstrap-from-scratch.sh` | static | Cache scope/dir policy sourced by `bootstrap-from-scratch.sh` |
| 1 | Seed: typed-reason receipt | `check-bootstrap-reason-receipt-guard.shs` | static | Bootstrap refuses to start without a typed-reason receipt |
| 1 | Seed: planner admission bound | `verify-bootstrap-planner-admission-bound.shs` | static | A planner-admission-v2 receipt is well-formed and bounded before execution is attempted |
| 2 | Stage 2 capability probe | `check-bootstrap-stage2-struct-receiver.shs` | static | A freshly built stage2 compiler can compile a struct-receiver method (fail-fast capability probe) |
| 2 | Stage 2 module-global codegen | `check-bootstrap-nonentry-module-global.shs` | static | A module-level global in a non-entry module survives native build |
| 3 | Stage 3 self-verification | `check-bootstrap-stage3-selfverify.shs` | static | Stage 3 self-host acceptance (owned by the stage3 gate; see that script's header) |
| 3 | Stage 3 diagnostic sweep | `bootstrap-diagnostic-sweep.shs` | static | Compiles independent `.spl` files and aggregates failures; never builds or deploys |
| 4 | Stage 4 self-verification | `check-bootstrap-stage4-selfverify.shs` | static | Stage 4 acceptance (owned by the stage4 gate) |
| 4 | Stage 4 sspec | `check-post-bootstrap-stage4-sspec.shs` | static | Stage4 binary + provenance are canonical, non-symlinked, executable; sspec suite runs on the stage4 binary |
| 4 | Stage 4 essential tools | `check-bootstrap-essential-tools-smoke.shs` | static | The deployed stage4 binary can actually run the essential tool subcommands |
| 5 | Deploy: platform handoff | `check-bootstrap-platform-handoff-readiness.shs` | static | Read-only fail-closed readiness of stage3 manifest / stage3 candidate / stage4 provenance for the handoff |
| x | OS bring-up: collect-parent | `check-bootstrap-user-collect-parent.shs` | run | Scheduler bootstrap wires user collect-parent correctly |
| x | OS bring-up: reap root owner | `check-x86-64-bootstrap-reap-root-owner.shs` | run | Zombie collection releases the exact child address space |

Rows marked `x` are not stages of the compiler bootstrap; they gate the SimpleOS
scheduler bootstrap path and are included because they carry `bootstrap` in
their name and would otherwise be orphaned from any umbrella.

## Honest gap list

### Gap 1: most phase gates do not implement the verdict contract

Measured on `origin/main` `d288f55ea83`: of the twelve pre-existing bootstrap
gates surveyed, **only `check-cache-scope-ownership.shs` has a `--selftest`**,
and **none of the others emits a `PASS —`/`FAIL —`/`ERROR — nothing was checked`
verdict line**. They signal only through exit status and ad-hoc stderr text
(`FAIL: ...`, `post_bootstrap_stage4_reason=...`, `bootstrap-policy-error: ...`).
Consequences:

- A gate that exits 0 having checked *nothing* is indistinguishable from one
  that checked everything. Non-vacuity is unenforced everywhere except the cache
  scope gate.
- Without `--selftest`, no gate proves it can still detect the defect it was
  written for. A gate that has silently stopped detecting anything looks green.

The umbrella cannot fix this from the outside — it can only report the exit
status a gate chose to return. Bringing each gate up to the contract is per-gate
work and is not done here.

### Gap 2: phases with NO gate at all

| Phase / step | Status |
|---|---|
| **Rust seed build** (`cargo build --release --bin simple`) as a bootstrap phase | No bootstrap-phase gate. `scripts/check/check-seed-builds-push.shs` covers it only on the **push** path, over a commit range — nothing verifies the seed compiles at bootstrap time. |
| **Stage 1** (seed → first Simple compiler) | **No gate.** The registry's `p1-*` entries gate the *receipt* and *planner admission* around it, not the artifact it produces. Nothing asserts the stage1 binary is well-formed or capable. |
| **Stage 2 → Stage 3 fixpoint** (byte-identical self-compilation) | **No gate.** The 3-stage self-compilation *verification* that `bin/simple build bootstrap` claims is not asserted by any script in `scripts/check/`. |
| **Deploy step** (writing `bin/release/<triple>/simple`, symlink flip) | **No gate.** `rollback-bootstrap-deploy.shs` exists to undo a deploy; nothing verifies one. |
| **Cross-platform lanes** (FreeBSD, Windows, aarch64) | Only `check-freebsd-bootstrap-qemu.shs`, invoked from the bootstrap driver, and it is not in this umbrella because it needs a VM. `bootstrap-windows.sh`/`.cmd` have no gate at all. |
| **`stage4-tooling-matrix.shs` / `stage4-tools-only.sh`** | No gate. |
| **`preserve-phase-binary.shs`** (per-phase binary preservation) | No gate — nothing verifies the preserved binary matches what the phase produced. |

### Gap 3: gates that exist but are never invoked by any automated path

`bootstrap-from-scratch.sh` invokes only: `bootstrap-cache-policy.shs`,
`check-cache-scope-ownership.shs`, `bootstrap-diagnostic-sweep.shs`,
`check-bootstrap-stage2-struct-receiver.shs`,
`check-bootstrap-essential-tools-smoke.shs`, `check-stage-log-diagnosable.shs`,
`check-mcp-native-smoke.shs`, `check-freebsd-bootstrap-qemu.shs`.

Everything else in the table above — including
`check-post-bootstrap-stage4-sspec.shs`,
`check-bootstrap-platform-handoff-readiness.shs`,
`check-bootstrap-nonentry-module-global.shs`,
`check-bootstrap-reason-receipt-guard.shs`, and
`check-bootstrap-portability.shs` — is invoked by **no automated path**. Until
this umbrella, they ran only when a human remembered them.

### Gap 4: `static` mode is not execution

Eleven of fifteen entries are only proven to exist and parse. That is a real but
narrow assertion. Closing this needs a fixture-based artifact harness (a
throwaway stage-binary stand-in per gate), which does not exist.

## Currently RED on `origin/main`

`check-bootstrap-portability.shs` **fails** at `d288f55ea83`:

```
FAIL: immutable bootstrap authority publication
```

This is reported as RED, not worked around. Per repo policy a gate is never
weakened or downgraded to advisory to make an umbrella green — that is the
documented mechanism by which a tree wipe went undetected. The umbrella
therefore returns `FAIL` on a clean checkout of `origin/main`, which is the
correct and honest result.

## The phase-gating principle (authoritative)

> **"What each phase tests is to check next phase related properly impled. Not
> optional features."** — user, 2026-08-23

Rendered precisely: **each bootstrap phase's test gate exists to verify that the
capabilities the NEXT phase depends on are correctly implemented.** It is a
*prerequisite check*, not exhaustive coverage, and it deliberately excludes
optional / feature-surface tests that no later phase consumes.

This is not a concession to time budgets, it is what makes the gate mean
anything. A phase gate that runs everything is both too slow to run (21,228
spec files) and too noisy to read, so in practice it is skipped — and a gate
that is skipped protects nothing. A phase gate scoped to the next phase's
prerequisites is both fast and meaningful: when it goes red, the next phase is
genuinely unable to proceed.

### Corollaries (each learned the hard way)

1. **A gate must name what it covered — counts and scope.** The verdict line
   states how many items were checked *and* that the set was a subset, so a
   reader can see exactly which subset. Silent narrowing is the failure mode
   being eliminated: a gate that quietly stopped covering something looks
   identical to one that covers everything.
   Recommended shape:
   `PASS — N phase-gate spec(s) run, 0 failed (M out-of-scope deferred, see <record>)`
2. **Excluded-but-incomplete work is recorded as a TODO and explicitly disabled
   or made to assert** — never left silently half-working. (Standing policy:
   *"add assert or todo; disable what not completed optional."*)
3. **A gate that examined zero items reports `ERROR`, never `PASS`.** Absence of
   evidence is not evidence. This is the same non-vacuity rule the pre-push
   guards carry (`.claude/rules/vcs.md`).
4. **Optional-feature failures are held as TODOs — not fixed inside the phase.**
   They are disabled with a skip or an assert *and* a TODO, recorded in the
   gate's **scope declaration**, never sprinkled anonymously through spec files
   and never deleted. Skip is the authorised mechanism for this case; CLAUDE.md's
   prohibition on skipping failing tests without approval still governs
   everything else. See
   [incomplete work is disabled, never deleted](#companion-rule-incomplete-work-is-disabled-never-deleted).

### Measured scope data (at `origin/main`, 2026-08-23 — do not re-derive)

Simple test trees, **21,228** spec files total. The compiler / interpreter /
loader-related scope is **2,106**:

| tree | specs |
|---|---|
| `test/01_unit/compiler/**` | 2,063 |
| `test/02_integration/compiler/**` | 43 |
| `test/01_unit/app/cli/` (driver/loader path) | 69 |
| `test/01_unit/app/compile/` (driver/loader path) | 4 |

Within the compiler tree: backend 272, driver 159, interpreter 159, codegen 147,
hir 143, mir 110, loader 104, frontend 91, linker 83.

Rust seed suite: in scope is compiler / interpreter / loader / tester. **Out of
scope and held as TODOs:** SIMD, graphics / audio / GPU / ML wrappers, engine2d,
browser / UI, and anything behind an optional cargo feature or an external SDK.

Stage 1 build closure is **689 modules** of 15,221 `.spl` files, because
`--entry-closure` follows imports from the entry — so `--source src` does **not**
widen it beyond `--source src/app`.

### Categorically ineligible for any gate, in every tree

| path | why |
|---|---|
| `test/01_unit/bugs/` | specs that document defects by construction and are *expected* to fail |
| `test/fixtures/` | the test runner's own deliberate red inputs — gating or tagging them would neutralise the fixtures that prove the runner reports failure at all |
| `test/tmp_repro/` | scratch reproduction material |

### Per-phase prerequisite scope

| phase | what the NEXT phase needs from it | in scope for the gate | out of scope (TODO-held) |
|---|---|---|---|
| 0 Preflight | a parseable, lane-isolated shell environment | shell portability, cache-scope ownership, cache policy | everything else |
| Rust seed | a seed that can compile Simple | compiler / interpreter / loader / tester in the seed suite | SIMD, graphics/audio/GPU/ML, engine2d, browser/UI, optional cargo features, external SDKs |
| 1 Stage 1 | a stage1 binary able to build the stage2 closure | the **689-module** entry closure; driver/loader specs (`test/01_unit/app/cli/` 69, `test/01_unit/app/compile/` 4) | the other 14,532 `.spl` files, which stage1 never compiles |
| 2 Stage 2 | codegen features stage3 self-compilation depends on | struct-receiver methods, non-entry module globals — the two probes that exist | full feature surface |
| 3 Stage 3 | a self-hosting compiler | self-verification, diagnostic sweep, compiler-tree specs (2,106) | app/UI/ML/graphics specs |
| 4 Stage 4 | a deployable tooling binary | essential-tool subcommands, provenance canonicality | the whole 21,228-spec suite |
| 5 Deploy | a binary the repo can run | platform-handoff readiness | — |

### Gap 5: a gate that reports capabilities it never exercised

`scripts/check/check-post-bootstrap-stage4-sspec.shs` prints
`post_bootstrap_stage4_test_runner=true`, `post_bootstrap_stage4_lint=true`,
`post_bootstrap_stage4_duplicate_check=true` and
`post_bootstrap_stage4_acceptance=true` **unconditionally**, after verifying only
provenance canonicality and smoke-log stability. No test runner, linter, or
duplicate check is invoked anywhere in the script. Its name promises an sspec
run it does not perform.

This directly contradicts corollary 1 (a gate must name what it *covered*) and
corollary 3 (zero items examined must be `ERROR`). It is **filed, not silently
re-scoped here** — changing what it asserts is a behavioural change and belongs
in its own reviewed commit:
`doc/08_tracking/bug/stage4_sspec_gate_reports_unexercised_capabilities_2026-08-23.md`.

## Companion rule: what belongs in rust simple (the Rust seed)

**The bootstrap path contains exactly what the next step requires.** That single
sentence covers testing and implementation alike:

- **Tests** — each phase's gate verifies what the *next* phase depends on.
- **Implementation** — the seed carries what the *next* phase needs, and nothing
  else.

### The rule

**For rust simple (the Rust seed, `src/compiler_rust/**`): do not implement
optional features unless requested, or needed to build phase 2.**

Two exceptions, and only these two:

1. **Requested** — the user asks for it.
2. **Needed to build phase 2** — the next phase genuinely cannot be built
   without it.

The second exception is not a loophole. The need must be **demonstrable**: a
concrete phase-2 build failure that the feature resolves. *"Phase 2 will probably
want this"* is not the exception; *"phase 2 does not build without this"* is.
Anyone invoking it records what broke.

Simple is the default implementation language, per CLAUDE.md's
*"Impl in Simple unless it has big performance differences."* This rule sharpens
that line for the optional-feature case rather than replacing it.

### Why the seed specifically

The Rust seed is bootstrap-only tooling whose single job is to compile Simple
until the self-hosted compiler takes over. Every optional feature added to it
must then be maintained in two languages and eventually replicated on the
self-hosted path — so it directly enlarges the bootstrap problem this phase
exists to shrink.

Concrete supporting fact: the seed's own test suite **could not even build**
until 2026-08-23 — `simple-native-all` (lib test) never linked, because
`rt_mem_snapshot_open` / `rt_mem_snapshot_close` / `rt_mem_snapshot_record` and
`rt_file_atomic_write` were defined in both `native_all` and the
`simple_runtime` rlib **with different signatures**. Any claim about seed test
health before that fix was unfounded. The more surface the seed carries, the
more of this there is.

### Scope of the rule

Applies to **new** work. It is not a mandate to retroactively strip existing
optional surface from the seed — record anything you find as an **observation**,
not a defect.

## Companion rule: incomplete work is disabled, never deleted

Optional or incomplete work that a phase gate excludes is **disabled with a skip
or an assert, plus a TODO. Never deleted, never left silently half-working.**

Skip is the authorised mechanism *for this case specifically* — excluding
out-of-scope optional surface from a phase gate — and it is recorded in the
gate's scope declaration and a TODO, not sprinkled anonymously through spec
files. CLAUDE.md's prohibition on skipping failing tests without approval still
governs everything else. In the Rust seed the equivalent is `#[ignore]` (or an
assert) plus a TODO.

Deleting the excluded work would make it invisible, which is the same failure
mode as a silently narrowed gate: nothing distinguishes "deliberately out of
scope" from "never existed".

## The three policies together

| policy | statement |
|---|---|
| **Scope** | Each phase's tests verify the next phase's prerequisites, not optional features. |
| **Incomplete work** | Disable with skip or assert plus a TODO — never delete, never silently half-working. |
| **rust simple** | Do not implement optional features unless requested, or needed to build phase 2. Simple is the default implementation language. |

Together: the bootstrap path is deliberately small, explicitly gated, and
everything outside it is **visible rather than silently absent**.

## Phase -> artifact map (read this before saying "phase 1")

**"Phase 1" is NOT a native-build.** This is the single most repeated mistake
against this document; it cost ~26 unusable runs on 2026-08-22/23
(`doc/08_tracking/bug/phase1_mislabelled_as_native_build_2026-08-23.md`).

| phase | artifact | produced by | is it a `native-build`? |
|---|---|---|---|
| 0 | host toolchain / preflight | `scripts/setup/setup.shs` | no |
| **1** | **Rust seed** — `src/compiler_rust/target/bootstrap/simple` (`bootstrap-from-scratch.sh:1393`) | **cargo**: `build --locked --offline --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap` (`:1772-1775`); preserved as the phase-1 lineage snapshot at `:2117` | **NO — never** |
| **2** | `stage2/<platform>/simple` | the **seed** runs `native-build` (`:2254-2275`) — **the FIRST native-build of the whole bootstrap** | **yes** |
| 3 | `stage3/simple`, `stage3/<triple>/simple` | the stage2 binary runs `native-build` (`:2551`) | yes |
| 4 | full CLI / release deploy | stage3 artifacts installed by the script's deploy step | — |

Consequences, stated so they cannot be re-derived the hard way:

- A command containing `native-build` is **Stage 2 or later, by definition**.
  If a log or a report calls it "phase 1", the label is wrong, not the stage.
- Phase 1 failing is a **cargo** failure. Phase 1 succeeds routinely (~4m18s
  measured); a "phase 1 is slow / hanging" report almost always means someone
  hand-ran a Stage-2 native-build under the wrong name.

### The stage native-build line is never typed by hand

`sh scripts/bootstrap/bootstrap-from-scratch.sh` is the only sanctioned way to
run any of these stages. The Stage-2 line (`:2254-2275`) carries **three**
`--source` roots plus `--backend`, `--target`, `--runtime-bundle
core-c-bootstrap`, `--runtime-path`, `--mode`, `--cache-dir`, `--threads`, and
the env `SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_NO_DEPRECATED_WARNINGS=1`. Every one is load-bearing:

- Drop `--cache-dir` and `SIMPLE_CACHE_SCOPE` has nothing to partition — the
  cache **cannot hit**, silently. Zero cache-hit lines in a 23,718-line log is
  the signature.
- Drop `--source src/compiler --source src/lib` and the closure walker must
  discover those trees through import edges from one root.
- Drop `--runtime-bundle` / `--runtime-path` and the stage links against a
  runtime the stage's provenance snapshots do not describe.

Gated by `scripts/check/check-sanctioned-bootstrap-invocation.shs`.

### `--strategy=adhoc` is a failure policy, not a lighter build

`scripts/bootstrap/bootstrap-from-scratch.sh:22` — `adhoc` maps to `fail-fast`
(vs `phase-isolated` for `normal`, `inventory-to-end` for `full`). It changes
**nothing** about what is compiled. **There is no reduced-closure stage-1 path
in this repo.**

### Frozen progress counter = livelock, not slowness

If a stage's module counter stops advancing while CPU stays high, that is a
**livelock** (the same modules re-entered), not an O(n^2) throughput problem, and
the two have opposite fixes. Diagnostic signature from the 2026-08-23 incident:
counter frozen at 389/688 for 2,700s, `dim_constraints.spl` and `narrowing.spl`
re-emitting every 11-14s, `module_surface_registry_index.spl` parsed 73 times.

### How to actually run it (or you WILL hand-roll a command)

Running the script bare now fails **before Stage 1** with:

```
bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl ...'
```

exit **64** (`bootstrap-from-scratch.sh:466-483`). A staged bootstrap requires a
planner-issued receipt. There is exactly one trust-root exception
(`:468-475`): `--stop-after-stage2` **and** `--full-bootstrap` together, with no
receipt, reason `stage2-trust-root-refresh` — the first independently admitted
pure-Simple parent cannot require a receipt produced by that parent.

So the working stage-2 invocation, verified against a live lane run:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<dir>
```

`--strategy=adhoc` here is a normal, sanctioned flag (fail-fast failure policy),
**not** a lighter build. Anyone who hits exit 64, concludes "the script is
broken", and hand-rolls a `native-build` line has just reproduced the 2026-08-23
incident.

Flag resolution note: the script passes `--mode "${bootstrap_mode}"`, which
defaults to `dynload` (`:277`, `SIMPLE_BOOTSTRAP_MODE` override) — so a live run
shows `--mode dynload` and `--backend llvm`. Read the resolved values off a real
run; do not paraphrase them from memory.

## See also

- `.claude/rules/bootstrap.md` — bootstrap architecture, stage semantics, known blockers
- `.claude/rules/commands.md` — build/test fast paths, cache scope
- `.claude/rules/vcs.md` — the seven pre-push guards (a different, push-time regime)

## Bootstrap failure classes ported from the macOS aarch64 lane (2026-08-23)

Ported from `origin/codex/stage3-hir-owner-fixes` (`c9ce33e2234`). **Each entry
is labelled with the platform its evidence came from.** A Darwin-only finding is
not a general claim; two entries below were re-measured on Linux and one of them
came back materially different — read the correction, not the original.

### The two `--timeout` flags are different knobs — and the "no override" claim is WRONG on the seed path

*macOS lane finding, CORRECTED by Linux re-measurement — the correction is the
portable part.*

The macOS lane recorded `FAILED FILES (1): ... => timeout (300s)` and concluded
that the per-file 300 s budget is "a hard default with no env var or CLI flag
override". Half of that is right and half is not:

- **Right, and confirmed on Linux:** `file_timeout: 300` is the struct default
  at `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:537`, and
  the `--timeout` flag of the **pure-Simple** `simple native-build`
  (`src/app/cli/native_build_main.spl`) is a *different* knob — the worker
  subprocess timeout, `DEFAULT_TIMEOUT_MS = 7200000` (7200 s) at
  `native_build_main.spl:89`. Confusing the two costs a debugging session.
- **Wrong:** an override does exist on the path the bootstrap actually uses.
  The **Rust seed driver** CLI, `src/compiler_rust/driver/src/cli/native_build.rs`,
  parses its own `--timeout <secs>` (`:229-240`) into `let mut timeout: u64 = 300`
  (`:129`) and assigns it straight to `file_timeout` (`:584`); the SFFI entry
  does the same at `src/compiler_rust/compiler/src/native_build_sffi.rs:598`.
  Since the bootstrap runs the Rust driver (`SIMPLE_NATIVE_BUILD_RUST=1`),
  `--timeout 900` on that invocation *does* raise the per-file budget.
- **Latent doc bug found while checking this:** the same file's header comment
  (`:17`) and its `--help` text (`:805`) both say "default: 60", while the code
  says 300. Two out of three statements in one file are wrong; trust `:129`.

Operationally the macOS advice still holds and is platform-neutral: `--jobs=full`
on a small host saturates CPU and can push a big file (there,
`src/compiler/10.frontend/core/__init__.spl`) past the budget. Retry with
`--jobs=half` — the native cache resumes and only failed/uncached files
recompile. **Same file passing with fewer jobs means contention, not a compile
hang** — the opposite diagnosis to the frozen-progress livelock recorded above,
and the two must not be confused.

### Bootstrap ops hygiene (macOS lane; mechanism is platform-neutral, not re-measured here)

- **Stale locks.** A killed bootstrap leaves
  `build/.simple-bootstrap-locks/.output-*.lock` / `.claim-*`; the next run
  fails fast with `timed out waiting for bootstrap output ownership`. Verify the
  holder is genuinely dead (PPID first), then remove the stale lock files.
- **Killing a wrapper does not kill its children.** Orphaned cargo / rustc /
  native-build processes survive with PPID 1. Check `ps -o pid,ppid` before
  killing anything mid-build; killing the wrong child aborts a *healthy* build.
- **A 0-byte log does not mean stalled.** `native-build` buffers stdout/stderr
  to a non-tty until completion. Judge liveness by
  `build/bootstrap/bootstrap-progress.log` milestones and `ps` CPU, never by log
  size. Progress-monitor `tree_processes=0` samples are an artifact during
  single-child phases.

### `jj` colocated-repo pitfalls (macOS lane; VCS-level, host-independent)

- `jj rebase -r X -d Y` rebases X **and its descendants only**, re-parenting X
  directly onto Y — ancestors of X are left behind and the stack is silently
  dropped. Move a stack with `jj rebase -s <stack-root> -d Y`.
- A commit showing `(empty)` after a rebase means its diff collapsed (e.g. a
  revert whose target files do not exist on the new base) — re-apply it.
- `git worktree remove/prune` in a colocated repo does not snapshot jj state;
  prefer jj-native operations.

### Fresh-seed requirement (macOS lane; CONFIRMED portable on Linux)

Current `src/` uses `unsafe(...)`. Any seed or deployed binary older than
~2026-08-19 fails with `error[E1002]: function 'unsafe' not found`. Verified on
Linux at `origin/main`: `src/lib/**` contains **2,245** `unsafe(` uses, so this
is a property of the source era, not of Darwin. A `--full-bootstrap` rebuild of
the Rust seed from current `src/compiler_rust` is the only way to compile
current source.

### Deliberately NOT ported

- **Mach-O weak-definition detection** (`2857d5f7346`). Apple `llvm-nm` prints
  weak *definitions* as `T` in POSIX `-g -p` output; the weakness appears only
  in the `-m` flag field as `weak external`, so the seed parsers
  (`native_project/tools.rs::archive_weak_global_symbols`,
  `native_project/linker.rs::read_global_symbol_types`), which accept only
  GNU/ELF `W`/`V`, misread every `__attribute__((weak))` C fallback as STRONG
  and the stage-4 capsule gate refused the link. **Darwin-only and inert on
  Linux** — ELF `nm` reports `W`/`V` correctly, so the Linux path was never
  affected. Recorded here so the symptom string ("Stage4 runtime capsule defines
  owner-provided runtime symbols STRONGLY … `_rt_heap_live_bytes`,
  `_rt_heap_peak_bytes`") is searchable, not because a Linux fix is owed.
- **The streaming-owner test fence** (`ddfbc573eee`) — reverted on its own
  branch by `23490cf9b5d`. Not resurrected.
- **`rt_heap_ref_wellformed` + fail-closed driver guards** (`4dd2f956a83`) —
  already on `main` as `57271d9ba49`, reconciled with this tree's assert policy
  and with a double-entry defect in `RUNTIME_SYMBOL_NAMES` fixed. Re-verified
  2026-08-23: all eight mirrors present
  (`src/runtime/runtime_native.c`, `runtime.h`,
  `src/runtime/test/rt_heap_ref_wellformed_selfcheck.c`,
  `src/runtime/simple_core/core_enum.spl`,
  `src/compiler_rust/runtime/src/value/{objects.rs,mod.rs}`,
  `src/compiler_rust/common/src/runtime_symbols.rs`) plus the
  `E-DRIVER-HIR-OWNER-MALFORMED` guard at
  `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`. No drift.

### Where the two lanes' SEGVs agree — and why that matters

Both lanes hit "self-hosted stage binary SIGSEGVs on a three-line hello world",
and they are **two different defects**: the macOS crash is a *zeroed Option
payload* (`x0 == 0` into a live `hir_cache_closure_digest`), the Linux crash was
*NULL-GOT* (`rip == 0`, undefined `rt_unwrap_or_trap` left a zero GOT slot,
root-caused at `c4b84dc9aaf`). The macOS lane states the distinction explicitly.
**Classify a hello-world SEGV by `rip == 0` vs `arg == 0` before concluding
anything** — fixing one class leaves the other untouched, and a green NULL-GOT
gate is no evidence about the payload class. Detail:
`doc/08_tracking/bug/stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md`.

**Note on skill/spipe homes:** the macOS lane also wrote these notes into
`.codex/skills/unstable-build-fixes/SKILL.md` and
`.spipe/bootstrap-pure-simple-dynload/state.md`. The `.spipe` submodule is
unpopulated at `origin/main` (`.spipe/spipe/doc/.../template/` does not exist
here), so the portable content lives under `doc/07_guide/` and
`doc/00_llm_process/` instead; nothing was written into `.spipe/`.
