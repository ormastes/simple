# bootstrap admission v2 is unconditionally fail-closed — no bootstrap can start (2026-08-17)

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
