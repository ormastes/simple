# Stage-2 sanity dies before any probe runs: `COMPILER_BUILD_TIMEOUT_SECONDS: parameter not set`

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-5, `work/bootstrap-full-3-2026-09-12`, rebased onto
  `origin/main` `3a3e0121a7e`
- Severity: **Stage-2 sanity cannot produce a probe verdict at all.** It is not a
  compiler failure — Stage 2 built and linked clean — but it fails admission and
  produces no evidence about the candidate.

## Verdict, verbatim

```
error: sanity FAIL - frontend smoke exited 2 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=2 candidate_unchanged=true
```

and the ENTIRE preserved frontend-failure log is one line:

```
scripts/bootstrap/bootstrap-from-scratch.sh: 234: COMPILER_BUILD_TIMEOUT_SECONDS: parameter not set
```

Note `frontend_status=2`, not 1: the probe script aborted, it did not fail a
probe. No `stage2-sanity.env.env.txt` was written, and both
`frontend-bootstrap-{0,1}.log*` files are empty — the run died before the first
probe.

Stage 2 itself was healthy in the same run:

```
Build complete: 886 compiled, 0 cached, 0 failed
Linked: .../bootstrap-boot5b/stage2/aarch64-unknown-linux-gnu/simple (148632 KB) via clang++
  Time: 651.9s compile + 54.0s link = 705.8s total
```

## Mechanism

`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:238`
dereferences the variable unguarded, inside a `set -u` shell:

```
        --timeout-seconds="$COMPILER_BUILD_TIMEOUT_SECONDS" \
```

Every other reader in the tree defaults it — `bootstrap-from-scratch.sh:1519`,
`resume-stage3-from-admitted.sh:666`, `check-stage2-sanity-diagnostic.shs:82`
and `check-bootstrap-stage2-sanity-gate.shs:106` all use
`${COMPILER_BUILD_TIMEOUT_SECONDS:-180}`. This one site does not, so it depends
on the sanity environment carrying the variable in.

`COMPILER_BUILD_TIMEOUT_SECONDS` is **not** in the canonical Stage-2 environment
set (`scripts/check/lib/bootstrap-stage3/authority.shs:396`), and was not there
before either — so the carry came from the invocation path, which the
LLVM-env changes rewrote.

## Bisect evidence

Measured in this worktree, same host, same command shape:

| run | base | outcome |
|---|---|---|
| `bootstrap-boot5` | `12599a86242` (pre-rebase) | probes RAN; real probe verdicts recorded |
| `bootstrap-boot5b` | `3a3e0121a7e` (post-rebase) | aborts at the unset variable, no probe runs |

Three commits in that range touch this path and are **not** ancestors of the
old base: `621a4d6b2ab` ("give Stage 2 a PATH so it can find llc"),
`80c1099f466` ("let Stage 2 see the LLVM toolchain it is configured with") and
`63c8fd91f5d` ("carry the LLVM tool dirs through the sanity env scrub").
`f95d935d2b7`, whose subject claims "probe-timeout knob survives the sanity
scrub", IS an ancestor of the old base — i.e. that property held before this
range and does not hold after it.

There is a guard for exactly this property,
`scripts/check/check-bootstrap-timeout-env-overridable.shs`, which names
`COMPILER_BUILD_TIMEOUT_SECONDS` in its header. It did not prevent the
regression.

## Fix, not applied here

One line at the call site would make it fail-soft like every sibling:

```
--timeout-seconds="${COMPILER_BUILD_TIMEOUT_SECONDS:-180}"
```

That is a one-character-class change to a gate script this lane does not own and
which sits on the admission path, so it is reported rather than applied; the
alternative (re-adding the variable to the carried set) is a different decision
with different blast radius, and picking between them belongs to the owner of
the LLVM-env change.

## Reproduction

    cd <worktree at origin/main 3a3e0121a7e>
    sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap \
      --backend=llvm --mode=dynload --jobs=10 --stop-after-stage2 --output=<fresh>
    # ~45 min later, at Stage 2 sanity:
    cat <fresh>/stage3/<triple>/stage2-sanity.env.frontend-failure.log
