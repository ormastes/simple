# Stage 2 admitted while unable to native-build hello world (argument-form gap)

Date: 2026-08-25
Status: gate landed (regression fencing). Underlying compiler defect already fixed at origin 2026-08-24.
Lane: lane-admit-gate, worktree from `origin/main` `dee716eaa7c`.

## Symptom

`bootstrap-from-scratch.sh` printed `Stage 2 admitted` for a candidate that
SIGSEGV'd (rc=139) native-building a two-line hello world:

```
[build] mir 1/1 step 4/6 +256ms dt=146ms hw
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module
surface payload malformed at HIR entry (heap-typed payload word is 0 or in the
zero page)
```

Stage 3 then consumed that "admitted" compiler and died far from the cause.

## What the two admission gates actually verify

`bootstrap-from-scratch.sh:6246` — `Stage 2: running bootstrap compiler sanity`
calls `bootstrap_stage_sanity` (`:3745`), five checks:

1. `--version` equals `simple-bootstrap $(cat VERSION)`;
2. `run <fixture>` is rejected with `unknown command 'run'` and status 1;
3. `candidate_frontend_smoke` with `SIMPLE_BOOTSTRAP=0`;
4. the same with `SIMPLE_BOOTSTRAP=1`;
5. the candidate's own sha256 is unchanged across the probes.

`:6266` — `Stage 2: proving struct receiver/runtime capability` runs
`check-bootstrap-stage2-struct-receiver.shs` and requires the candidate sha and
the frozen runtime snapshot to be unchanged.

## The naive diagnosis is FALSE, and matters

"The gates never native-build a trivial program" is **wrong**.
`candidate_frontend_smoke`
(`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:36`) already
native-builds **and executes** two fixtures — `p2_add.spl` (requires stdout `5`)
and `stage2_mir_retention.spl` (requires stdout `3`) — with a log-size cap and a
dead-lexer signature check.

Measured: the known-bad binaries **pass that smoke completely**
(`SMOKE0_RC=0` on `build/bootstrap/s5full/.../stage2/simple`). A gate that
merely "native-builds and runs a hello world" via `--entry` would ALSO have
admitted them. That is why this record does not stop at the obvious answer.

## Actual root cause of the gap: an ARGUMENT-FORM axis

Same binary, same flags, same env, same fixture — only the entry form differs:

| form | result |
|---|---|
| `... --mode one-binary --entry hello.spl --output hw.bin` | rc=0, prints `hello` |
| `... --mode one-binary        hello.spl --output hw.bin` | **rc=139 (SIGSEGV)** |

Both admission probes name the entry with the `--entry` FLAG. The positional
form — the form a human types, and the form the Stage 3 investigation used
(`evidence/stage3_finding_s5.md`) — was never exercised by any gate. Confirmed
to still crash under the smoke's exact env
(`SIMPLE_FRONTEND_DELEGATED=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_EXECUTION_MODE= ...`).

Reproduced on **both** artifacts on this host: `build/bootstrap/s5` (02:11) and
`build/bootstrap/s5full` (02:25) stage2, rc=139 each.

## Underlying compiler defect: already fixed

`src/runtime/runtime_native.c:8438` (`rt_heap_ref_wellformed`, 2026-08-24)
records this exact failure: a formation probe that required the HEAP tag
false-rejected every live CLASS instance on the native lane, breaking the two
driver HIR-entry guards unconditionally
(`E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` on a valid hello world). The tag
requirement was removed; zero-page rejection retained. This is one of the
"fail-closed hardening correct for ~100 sites, catastrophic for one" cases.

**So this record fences the GATE-COVERAGE hole, not an open compiler defect.**

## Fix

1. `scripts/check/check-stage2-hello-world-native-build.shs` — standalone
   fail-closed gate. `--selftest` first and fatal; verdict last on stdout;
   `PASS — <n> case(s) checked` / `FAIL` / `ERROR — nothing was checked`;
   build half under `timeout` with **rc=124 a distinct HANG class** and rc>=128
   a distinct CRASH class. Exit codes read directly into a variable on the line
   after each command, never through a pipe.
2. `candidate_frontend_admission.shs` — the minimal wiring: a positional-entry
   no-crash probe appended to `candidate_frontend_smoke`. Because
   `bootstrap_stage_sanity` is shared, this covers **Stage 2 and Stage 3** in
   one edit.
3. `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` — the fixture.

### Two deliberate scope limits

**Arm 2 is a NO-CRASH check, not a must-succeed check.** A healthy compiler may
reject a positional entry with a clean non-zero diagnostic; demanding success
would false-reject it. Only death-by-signal and hangs fail. A dedicated selftest
fixture (`positional-clean-error`) pins this so the gate cannot drift into
over-scoping.

**The fixture must be IN-TREE.** Measured: an out-of-tree fixture is rejected by
a *healthy* compiler (`missing importing module surface`, rc=1), so an
out-of-tree fixture would have made the gate false-reject every good binary.
This was caught during validation and corrected before landing.

`--entry-closure` is mandatory on both arms: without it the candidate scans the
default source roots and runs unbounded (>20 min on a two-line fixture).

## Evidence

Selftest: `PASS — 7 case(s) checked (selftest only)`. Fixtures mutate both
directions — `good` and `positional-clean-error` must PASS; `positional-segv`
(the incident shape), `hang`, `wrong-output`, `silent-success` must FAIL with
the right class.

Real artifacts:

| candidate | verdict |
|---|---|
| Rust seed, paired with its own tree (**known-good**) | `PASS — 2 case(s) checked` (rc 0) |
| `build/bootstrap/s5` stage2 (known-bad) | `FAIL — 2 case(s) checked, simple:positional-form:crash(killed by signal 11 (rc=139))` |
| `build/bootstrap/s5full` stage2 (known-bad) | same FAIL |

Note both known-bad binaries **pass the entry-form arm** — the gate names the
specific broken form rather than blanket-condemning the binary.

End-to-end through the wired admission path, on the previously-admitted binary:

```
WIRED_SMOKE_RC=1
candidate_frontend_smoke: candidate CRASHED (signal 11, rc=139)
native-building a two-line hello world with a positional entry
```

The same function returned 0 on the same binary before this change.

### Known-good availability (stated explicitly)

**No Stage 2 artifact on this host passes both arms** — `s5` and `s5full` both
crash on the positional form. The known-good positive control is the Rust seed
paired with its own tree, which PASSES both arms. With no candidate supplied the
gate exits **2 (ERROR — nothing was checked)**, never a silent pass; a
non-executable candidate and a missing fixture are likewise ERROR.

## Stage 3 / Stage 4 (reported, scope not expanded)

- **Stage 3: same gap, now closed by the same edit.** Stage 3 admission calls
  `bootstrap_stage_sanity "${stage3_bin}"` (`check-bootstrap-portability.shs:115`),
  which routes through the same `candidate_frontend_smoke`. No separate change.
- **Stage 4: different shape, NOT addressed here.** Stage 4 admission consumes
  provenance receipts from an admitted Stage 3 and runs a tools-only matrix
  (`stage4-essential-tools-smoke`); it does not re-run the frontend smoke. It
  therefore inherits whatever Stage 3 certified. Whether the tools matrix needs
  its own positional-form probe is left as a reported observation, deliberately
  unfixed in this lane.

## Not claimed

The gate proves the candidate does not crash or hang building and running a
trivial program in either argument form. It does not prove the compiler is
correct, and it does not re-verify the already-landed `rt_heap_ref_wellformed`
fix by a fresh bootstrap — no redeploy was run in this lane.

`scripts/check/check-bootstrap-portability.shs` fails on this tree with
`FAIL: MinGW runtime DLL is not staged`; verified **pre-existing and identical
at baseline** (`git stash`-ed run), unrelated to this change.
