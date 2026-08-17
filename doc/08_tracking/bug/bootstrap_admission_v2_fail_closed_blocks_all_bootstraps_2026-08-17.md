# bootstrap admission v2 is unconditionally fail-closed — no bootstrap can start (2026-08-17)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Status:** OPEN — worked around, not fixed.

`scripts/check/lib/bootstrap-planner-admission-bound.shs` (working-copy edit
02:14, also present on origin/main) ends `bootstrap_planner_v2_verify` with:

```sh
bootstrap_planner_v2_verify_structure "$1" "$2" || return 1
echo "bootstrap-policy-error: planner-admission-v2-producer-unavailable" >&2
return 1   # ALWAYS fails — "no canonical producer yet exists"
```

Every `bootstrap-from-scratch.sh` invocation therefore exits 64 with
`malformed-or-untrusted-planner-admission-v2` **before stage 1**, regardless of
receipt content. A gate whose producer does not exist yet must not be wired as
the only admission path: this is a self-imposed denial of service on the
bootstrap, observed twice tonight (runs at 02:3x and 03:0x).

**Workaround used:** ran the last pre-v2 script version
(`git show b1ff6537ed8:scripts/bootstrap/bootstrap-from-scratch.sh`) inside an
isolated frozen snapshot tree (`/mnt/data/worktrees/simple-boot-snap`), where
the v1 typed-reason receipt validates:
`bootstrap-policy: receipt-valid target=//bootstrap:stage4 reason=self-host-convergence-check`.

**Fix needed (choose one):**
1. Ship the canonical producer the comment promises, then keep fail-closed; or
2. Until it ships, fall back to the v1 receipt path (structural verify passes
   → accept with a logged downgrade note) instead of unconditional `return 1`.

Related: `030b35543b9` "security: reject unbound bootstrap planner receipts"
introduced v2; the 02:14 hardening removed the last working entry path.

## 2026-08-17 investigation — reproduced, plus a second finding

**Reproduced.** Built a receipt satisfying every one of the 29 structural
checks (all key names in order, all ten path/sha256 pairs hashing correctly,
canonical non-symlink paths, `planner_source_path` equal to
`$root/src/app/cli/bootstrap_reason_planner.spl`, `cache_scope_key` equal to
`sha256(runtime_sha:closure_sha)`, and a byte-exact
`simple-bootstrap-authorization-v2|...` authorization file). Result:

```
verify_structure rc=0   (all 29 keys + hashes + authorization text OK)
verify           rc=1   stderr=bootstrap-policy-error: planner-admission-v2-producer-unavailable
```

Confirmed no producer exists: `planner-admission-v2` appears in exactly five
files — the bound library, its two verifier/guard scripts, and the two
bootstrap entry scripts. Nothing in `scripts/bootstrap/`, `scripts/check/`, or
`src/app/cli/` ever *emits* a v2 receipt. The gate is not fail-closed, it is
**closed**: no input admits.

**Second finding — v2 structural verification is forgeable, so option (2) is
not the downgrade it looks like.** The receipt above was hand-written by an
unprivileged agent in under a minute. Every hash matched because the receipt
*names the files it hashes*, and those files were fixtures the forger created.
`build_argv_sha256` and `build_env_sha256` are only checked to be
64-hex-shaped — never compared against the actual argv or environment — and
`planner_smoke_path` is only checked to hash to its own recorded digest.
Nothing binds the receipt to a real build.

The consequence is that v2-as-implemented provides **no authorization strength
over v1**; its strength lives entirely in the not-yet-written producer. This
does not make option (2) safe — it means options (1) and (2) differ in
convenience, not in security, and the real security work is the producer.

**What the canonical producer must do** (the non-circular part, in order):
1. Take a pre-exec lock so the parent compiler, runtime dir, and source
   closure cannot change between measurement and use.
2. Hash the parent compiler, stage2 sanity/provenance artifacts, runtime
   snapshot, planner source and its transitive source closure, and git state
   — under that lock.
3. **Execute** the admitted planner, capturing its exact argv and environment,
   its stdout, and its exit status, and hash argv/env into
   `build_argv_sha256` / `build_env_sha256` **from what was actually
   executed** — the fields exist today but are never populated from reality.
4. Run the planner smoke check and record its receipt.
5. Emit the authorization line and re-verify the artifacts are unchanged
   (lock still held) before releasing.

The verifier must then additionally *re-derive* argv/env hashes at admission
time and compare, rather than only shape-checking them. Without step 3 and
that comparison, a v2 receipt means nothing more than a v1 one — which is
precisely what
`bootstrap_planner_v1_unbound_authorization_2026-08-14.md` filed against v1.

**Recommendation: OWNER DECISION — not implemented here.** Option (2) was
deliberately not implemented: it is a security-model change, and while the
analysis above shows it would not weaken any protection that actually exists
today, "the control was already vacuous" is an argument the owner should get
to weigh, not one a lane should act on unilaterally. The bootstrap currently
running proves the workaround path is viable in the meantime.

**Detection artifact shipped:** `scripts/check/check-gate-satisfiable.shs`
generalises the class — a verification function that does guarded work and
then ends in an unconditional `return 1`/`exit 1`, i.e. a gate no input can
satisfy. Deliberately-closed gates opt out with a greppable
`# gate-intentionally-closed: <reason>` comment in the body. Fatal
`--selftest` with 5 fixtures, including a must-FAIL replay of this incident's
exact shape.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (reproduced by content).** `scripts/check/lib/bootstrap-planner-admission-bound.shs`
header (lines 2-3) still reads 'It never executes the planner and cannot produce
authoritative admission', and `bootstrap_planner_v2_verify()` still ends with
`echo "bootstrap-policy-error: planner-admission-v2-producer-unavailable" >&2; return 1`
— i.e. structural equality is checked and then unconditionally rejected. Three callers
depend on it: `scripts/check/verify-bootstrap-planner-admission-bound.shs`,
`scripts/bootstrap/bootstrap-from-scratch.sh`, `scripts/bootstrap/resume-stage3-from-admitted.sh`.
This is a deliberate fail-CLOSED posture, not a fail-open defect: it refuses rather than
forges authority. The fix is the missing non-circular producer (execute an admitted planner
while capturing build lineage, pre-exec lock, argv/env, stdout/exit, smoke receipt), which is
a design-sized change and was NOT attempted here. Explicitly NOT proven: whether any bootstrap
currently in flight is blocked by this path.
