# check-cpu-backend-artifacts.shs passes having verified nothing, and the fix blocks every push

**Status:** RESOLVED 2026-08-17 — vacuity removed at the source, not reported.
The guard now verifies 3 real compiler-independent claims on this host, so
`pass > 0` honestly and ERROR-on-zero-verified could land without blocking
anyone. **Fix uncommitted at time of writing** (coordinator commits with
explicit paths).
**Filed:** 2026-08-17
**Component:** `scripts/check/check-cpu-backend-artifacts.shs`, wired into
`scripts/check/pre-push-conflict-tree-guard.shs:177`
**Class:** vacuous guard — exits 0 with a zero verification count

## Measured (BEFORE)

Executed, not inferred. Exit code read into a variable on the line AFTER the
command, never through a pipe:

```
sh scripts/check/check-cpu-backend-artifacts.shs
CPU_RC=0
cpu_backend_matrix status=SKIP_UNAVAILABLE failures=0 skips=18 require_all=0
```

**`pass=0`.** All 18 backend steps skipped with `reason=rust-seed-forbidden`, so
the guard verified literally nothing and reported success. It could not be
anything but green on any seed-only host, which is every host this campaign has.

This is the shape recorded in
`engine_divergence_guard_hardcodes_stale_seed_2026-08-17.md`: a guard that
passes by construction retires real defects behind a green audit trail. It was
found by the census in `check_scripts_vacuity_census_2026-08-17.md`.

## The first attempt was correct and unacceptable

Reporting `ERROR — nothing was checked (18 backend step(s) skipped as
unavailable, 0 verified)` (rc=2) is the right verdict under
`.claude/rules/vcs.md`. But `run_guard`
(`pre-push-conflict-tree-guard.shs:256-273`) fails closed on **either** signal:

```sh
if "$GREP" -q -e 'DO NOT PUSH' -e 'ERROR —' "$_out" || [ "$_st" -ne 0 ]; then
```

so it trips twice over and blocks **every push from a seed-only host,
permanently** — the host structurally cannot un-skip those 18 steps. Correct
verdict, unacceptable consequence. That attempt was reverted.

## Resolution: an artifact-first tier

Modelled on `check-gpu-backend-layer-evidence.shs`, which reports `pass=7`
because its artifact-first stages read real evidence off the committed tree and
need no compiler. The CPU guard had no such tier — all 18 of its steps require
running a compiler.

Six compiler-independent steps were added — three under `backend=contract` and
one per driven backend. They check claims the 18 compiler-driven steps
**presuppose**, and each one can fail:

| step | verifies | fails when |
|---|---|---|
| `fixture present` | the probe fixture is committed and non-empty | fixture deleted/emptied |
| `fixture return contract` | the fixture's `main()` actually computes the exit code the run/readback stage asserts | fixture arithmetic or call argument edited |
| `run assertion wired to constant` | the run stage asserts `$EXPECT_RUN_CODE`, not an inlined literal | a literal `41` is reintroduced, letting guard and fixture drift apart |
| `backend registered` (x3: llvm, cranelift, wasm) | each driven backend is a registered `BackendKind` in `src/compiler/70.backend/backend/backend_types.spl` mapping to exactly that lowercase name | enum variant renamed, `to_text()` string renamed, or registry file missing |

The second is the substantive one. `test/fixtures/.../probe.spl` computes
`backend_probe_value(20) = 20*2+1 = 41`, and the guard's run stage asserted a
hardcoded `41`. Nothing tied them together: an edit to the fixture would have
made the run stage silently assert the wrong value. The guard now recomputes the
value from the fixture's own source text and compares against the constant, and
`run_expect_41` was changed to use that constant rather than an inline literal.

## Measured (AFTER)

```
sh scripts/check/check-cpu-backend-artifacts.shs
CPU_RC=0
cpu_backend_matrix status=PASS_WITH_SKIPS pass=6 failures=0 skips=18 require_all=0
PASS — 24 backend step(s) checked, 6 verified, 18 recorded skip(s)
```

Pre-push hook consequence, evaluated with the hook's own predicate against this
output: `HOOK_VERDICT=WOULD_PASS`. Pushes are not blocked.

Other modes, exit codes captured on the line after the command:

```
--require-all   RA=1   FAIL — 24 backend step(s) checked, 18 skip(s) not allowed under --require-all
--backend llvm  BL=0   PASS — 10 backend step(s) checked, 4 verified, 6 recorded skip(s)
--selftest      ST=0   cpu_backend_selftest status=PASS cases=20
```

`--require-all` still fails on the 18 skips: no existing step was weakened and
no exclusion was added.

## Ablation (constructed, measured, restored)

Via `CPU_BACKEND_FIXTURE`, which overrides only the scan target — the selftest's
must-PASS case asserts `CANONICAL_FIXTURE` unconditionally, so an override can
never make the selftest vacuous.

```
# arithmetic corrupted: input * 2 + 1  ->  input * 2 + 7
A_RC=1
backend=contract step=fixture return contract status=FAIL reason=computes-47-expected-41
FAIL — 24 backend step(s) checked, 1 failure(s), 18 skip(s)

# fixture absent
B_RC=1
backend=contract step=fixture present status=FAIL reason=missing-or-empty-fixture
backend=contract step=fixture return contract status=FAIL reason=missing-or-empty-fixture
FAIL — 24 backend step(s) checked, 2 failure(s), 18 skip(s)

# registry: case Cranelift: "cranelift" -> "cranelift_renamed"
R_RC=1
backend=cranelift step=backend registered status=FAIL reason=variant-Cranelift-does-not-map-to-cranelift
FAIL — 24 backend step(s) checked, 1 failure(s), 18 skip(s)

# registry file absent
R2_RC=1
FAIL — 24 backend step(s) checked, 3 failure(s), 18 skip(s)

# restored
C_RC=0
PASS — 24 backend step(s) checked, 6 verified, 18 recorded skip(s)
```

## Selftest

Fatal, runs before every scan, suppressed only inside its own child invocations
(`CPU_BACKEND_SELFTEST_CHILD=1`). 20 cases: 6 verdict-contract (2 must-PASS, 2
must-FAIL, 2 must-ERROR including the all-skipped case that was this bug), 6
probe-contract (1 must-PASS on the canonical committed fixture; must-FAIL on
tampered arithmetic, tampered call argument, unparseable shape, empty file,
missing file), 6 registry (3 must-PASS on the canonical committed registry;
must-FAIL on renamed enum variant, renamed `to_text()` string, missing registry
file), and 1 end-to-end asserting the whole guard exits 1 with a `FAIL` verdict
when pointed at a missing fixture.

`CPU_BACKEND_FIXTURE` / `CPU_BACKEND_REGISTRY` override only the SCAN targets;
the selftest's must-PASS cases assert `CANONICAL_FIXTURE` / `CANONICAL_REGISTRY`
unconditionally, so an override can never make the selftest vacuous.

## Second latent fail-open found while fixing this one (NOT fixed)

`has_backend_identity` (this guard) greps compiler log output for the literal
lowercase `Backend: llvm` / `Backend: cranelift` / `Backend: wasm`. A source
survey found that string is emitted **only by the Rust driver**, via runtime
`{}` formatting:
`src/compiler_rust/driver/src/cli/native_build.rs:507`,
`src/compiler_rust/native_all/src/lib.rs:576`,
`src/compiler_rust/driver/src/cli/commands/misc_commands.rs:376`.
The only pure-Simple emission is
`src/compiler/80.driver/bootstrap_main_minimal.spl:14`, which prints
`Backend: Cranelift` — **capitalized**, so the guard's grep cannot match it.

This guard explicitly forbids the Rust seed (`reason=rust-seed-forbidden`).
So in the configuration the guard is built for — a pure-Simple compiler — the
backend-identity assertion can never fire. That is a second fail-open in the
same file, on a code path this host cannot reach and therefore could not
ablate. It is **not fixed here** and needs its own row: either the pure-Simple
driver must emit the lowercase identity line, or the guard's matcher must
accept the capitalized form. Fixing it blind, with no host able to execute the
path, is exactly the unverified-claim failure this campaign exists to stop.

## Not verified

- **No end-to-end PASS of the 18 compiler-driven steps.** They still all skip
  with `reason=rust-seed-forbidden`. This fix makes the guard honest about that;
  it does not make those steps run. A host with a non-seed compiler is still
  needed to exercise them, and their PASS text remains fixture-proven only.
- **`--backend` acceptance is not checked, only registration.** The registry
  check proves each name is a registered `BackendKind`. It does not prove the
  CLI accepts it: `src/app/io/_CliCompile/compile_opt_and_driver.spl:345-352`
  parses `--backend` as a free-form string with no whitelist, and its help text
  (line 289) enumerates `auto, cranelift, llvm, vhdl, c, cuda, vulkan` —
  **omitting `wasm`**, which the dispatch chain nonetheless handles at line 578.
  Declared-vs-implemented divergence in the help text, not chased here.
- **No audit of non-hook consumers** of this guard's exit code. Only
  `pre-push-conflict-tree-guard.shs:177` was confirmed (by the coordinator).
  The guard now exits 0 on this host as it did before, so no consumer changes
  behaviour, but a consumer keying on the literal `status=SKIP_UNAVAILABLE`
  summary line would now see `status=PASS_WITH_SKIPS`.
- **Whether the other 16 category-A guards in the census are stale-sensitive in
  practice** was not tested.
