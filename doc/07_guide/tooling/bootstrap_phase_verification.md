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
| 0 | Preflight: cache policy | `scripts/bootstrap/bootstrap-cache-policy.shs` | static | Cache scope/dir policy sourced by `bootstrap-from-scratch.sh` |
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

## See also

- `.claude/rules/bootstrap.md` — bootstrap architecture, stage semantics, known blockers
- `.claude/rules/commands.md` — build/test fast paths, cache scope
- `.claude/rules/vcs.md` — the seven pre-push guards (a different, push-time regime)
