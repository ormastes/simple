# No self-hosted binary deployed — bootstrap smoke cannot run, stage gate blocked

**Date:** 2026-08-09
**Status:** OPEN
**Severity:** blocks every gated push on this machine; silently degrades all agent verification

## Symptom

`scripts/check/check-bootstrap-essential-tools-smoke.shs` fails on a **clean
baseline tree**, with no campaign work involved:

```
essential_tools_identity_rc=0
error=rust_seed_binary
EXIT=1
```

Consequence: `scripts/check/check-cache-v2-stage-gate.shs` cannot pass, so no
stage of the semantic-incremental-build-v2 campaign can clear its pre-push
bootstrap check.

## Root cause

`bin/simple` resolves to `bin/release/x86_64-unknown-linux-gnu/simple`, which is
the **Rust seed**, not a self-hosted binary. The smoke gate correctly refuses to
certify bootstrap using the seed.

This violates the standing rule in `.claude/rules/bootstrap.md` and
`CLAUDE.md`: the default tooling is the pure-Simple self-hosted binary; the seed
is bootstrap-only. The rule further says that when the self-hosted binary is
unavailable or unstable, the fix is to repair it in pure Simple and re-deploy —
not to fall back to the seed.

## Why this is worse than one failing gate

Every agent on this machine is silently running the seed:

- Agent C7 disclosed that all its spec greens ran under the seed's interpreter,
  so **they do not prove self-hosted behaviour**. Its 13/13 green is real but
  narrower than it looks.
- Agent C5's differential dataflow specs (8/8) likewise ran under the tree-walk
  interpreter only; JIT and native lanes are untested.
- This is the documented `simple test silently delegates to seed` trap: GREEN
  under the seed is not evidence about the self-hosted compiler.

So the gate failure is not the problem — it is the only thing that *surfaced*
the problem. Without it, the campaign would have accumulated seed-only evidence
and called it verification.

## Fix

```bash
scripts/setup/setup.shs && bin/simple build bootstrap
```

3-stage self-compilation, then re-deploy so `bin/simple` points at the
self-hosted artifact. Not attempted during the campaign wave: machine load was
32-42 with 4+ concurrent agents, and a bootstrap under that contention would
thrash and likely fail. Run it once the wave drains.

After deploying, verify provenance with a **positive capability probe** — size
and banner both lie about which binary is live.

## Gate correction made in the same session

The stage gate originally reported this as `FAIL — pushing this would break
sibling agents`. That was wrong: it is an environment blocker, not a defect in
the staged commit, and misreporting it that way makes the gate permanently red
for a reason no stage can fix — which is how a gate gets ignored into
uselessness.

It now classifies `error=rust_seed_binary` as `ERROR — nothing was checked`
(exit 2). Still blocks the push, because bootstrap genuinely cannot be proven,
but no longer blames the commit. Verified: exit 2 with the environment-blocker
message.

## Impact on landed work

`6f815bd0dd7` (C0 schema + plan + design + stage gate) was pushed to `main`
having run only the three pre-push guards, **not** the bootstrap smoke. It is
docs, a `.sdn` data file, and a shell script — nothing in a compiled path — so
the risk is low, but it was not fully gated and should not be described as such.

C6 (`7a7e9f67adc`, generated Lean model + fail-closed formal gate) is committed
locally, independently verified (selftest 8/8, lake build OK), and **held
unpushed** pending a bootstrap-capable environment.

## Re-confirmed 2026-08-09 (fresh session)

Reproduced with no changes to source:

```
$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
$ sh scripts/check/check-bootstrap-essential-tools-smoke.shs
essential_tools_identity_rc=0
error=rust_seed_binary
$ sh scripts/check/check-cache-v2-stage-gate.shs
ERROR — nothing was checked: check-no-conflict-tree-push could not check anything ...
```

Still an environment blocker, not a source defect: `bin/simple` is still the
Rust seed. The only real fix is `scripts/setup/setup.shs && bin/simple build
bootstrap` to deploy a fresh self-hosted binary, which this task's instructions
explicitly forbid running in this session (risk of a long/contended bootstrap
under a shared, possibly loaded machine). No .spl/.shs source change is
warranted here — the gate is already correctly classifying this as `ERROR —
nothing was checked` rather than blaming a commit, per the "Gate correction"
section above. Leaving OPEN; someone with a drained, bootstrap-capable
environment still needs to run the fix command and re-deploy.

## 2026-08-17 re-triage (triage shard) — STILL OPEN, reproduced byte-for-byte

Binary identity: `readlink -f bin/simple` =
`bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes, mtime
2026-08-16 22:59:37 — still the Rust seed (prints the seed banner). Note the
mtime is FRESH: a new seed was copied in on 2026-08-16, which is exactly the
`.claude/rules/bootstrap.md` trap of a freshly-dated seed masquerading as a
deployed self-hosted binary. Freshness is not provenance.

Gate re-run (read-only; the script builds and deploys nothing — verified by
grepping it for `deploy`/`cargo`/`cp` into `bin/` first):

```
$ sh scripts/check/check-bootstrap-essential-tools-smoke.shs ; echo rc=$?
essential_tools_identity_rc=0
error=rust_seed_binary
rc=1
```

Identical to the 2026-08-09 report. The gate is behaving correctly; the defect
is the absent self-hosted artifact.

### Why this shard did not fix it

The only fix is `bin/simple build bootstrap` + redeploy of the shared
`bin/release/**`. This checkout is shared by ~15 concurrent lanes and a redeploy
clobbers all of them, so the shard was explicitly forbidden from deploying.
**Left OPEN for a lane that owns the deploy window** — recorded as an honest
non-verification rather than a fabricated green.

### Spec added (fences the dangerous half)

`test/01_unit/app/cli/bootstrap_smoke_gate_seed_fail_closed_spec.spl` —
`Results: 3 total, 3 passed, 0 failed`.

The row's own text makes the point that the gate failing "is the only thing that
*surfaced* the problem". So the spec pins the inverse-of-usual invariant: **while
`bin/simple` is a Rust seed, the smoke gate must NOT pass** — a green from the
gate is the failure condition. It also requires the gate to *name* the reason
(`rust_seed_binary`) rather than exiting non-zero mutely, and reads rc directly
from the `rt_process_run_timeout` 3-tuple, never through a pipe.

**Ablation (causation proved):** repointing the spec's `GATE` at `/bin/true` — a
gate that passes vacuously, i.e. the false-green this row warns about — gives
`Results: 3 total, 1 passed, 2 failed`. Restoring the real gate returns it to
3/3.

## 2026-08-17 triage (wave W3) — FAMILY: no source-matched self-hosted binary deployed

This row is one member of a single family, not an independent defect. On this
host `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` is the **Rust
seed**, so every remaining blocker in this row requires building and deploying a
source-matched self-hosted CLI. The rows sharing that blocker are:

- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`
- `stage4_full_cli_source_check_blank_exit8_2026-07-23`
- `self_hosted_cli_native_build_silent_no_artifact_2026-08-14`
- `self_hosted_simpleos_target_native_build_crash_2026-07-11`
- `native_selfhosted_run_segfault_startup_normalize_2026-07-24`
- `bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17`
- `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`
- `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09` (the family
  statement itself: an ENVIRONMENT fact on this machine, not a code defect)

W3 was explicitly barred from rebuilding or redeploying `bin/simple` /
`bin/release/**` (~16 concurrent lanes share them), so **no execution evidence
for this row was produced or is claimed**. Status is unchanged: OPEN, blocked on
deploy. What W3 did instead was pin, by source spec, the fail-closed checks these
rows depend on, so they cannot be silently lost again while the deploy blocker
persists: `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl`
(native-build worker exit 0 without an artifact; driver Success without a fresh
staged artifact; argv read through `rt_cli_get_args` rather than a same-named
import). Ablation-verified: neutralising the native_build_main.spl guard takes
that spec from `Results: 3 total, 3 passed` to `3 total, 2 passed, 1 failed`.

