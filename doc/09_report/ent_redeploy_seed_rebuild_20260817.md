# Enterprise Redeploy — Seed Rebuild + Redeploy Milestone (2026-08-17)

**Tree:** git worktree `/mnt/data/worktrees/ent-redeploy`, detached at certified
enterprise tip `25595abd62d93eff90984901d8d116cafdd8a905`.
**Verdict: BLOCKED at the bootstrap policy admission gate — no deploy performed.**
Recorded honestly per redeploy rule step 5. Nothing committed, nothing pushed.

## Starting binary identity (before)
- `bin/simple`: **does not exist** (`readlink -f bin/simple` → non-existent path;
  `setup.shs` refuses: "…/x86_64-unknown-linux-gnu/simple not found — run bootstrap first").
- `bin/release/simple`: 2181-byte bash wrapper; its runtime target
  `bin/release/x86_64-unknown-linux-gnu/simple` **does not exist**, and its seed
  fallback `src/compiler_rust/target/bootstrap/simple` **also does not exist**.
- **No Rust seed anywhere** in the worktree (`find … target/bootstrap/simple` and
  `find build/bootstrap -name simple` both empty).
- Reference: the main tree's deployed binary
  (`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
  59,536,728 bytes) is itself still the **RUST SEED** — `--version` prints
  "WARNING: this Rust-built Simple binary is a bootstrap seed only …
  Simple Language v1.0.0-beta". Consistent with the gate blocking every session.

## Tier reached
Never reached Stage 1. Blocked at the pre-Stage-1 policy admission gate.

## The blocker (exact)
- **Command:** `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
  → exit 64, `bootstrap-policy-error: reason-receipt-required`.
- The receipt must be produced by the pure-Simple planner and pass
  `bootstrap_planner_v2_verify`. That function is **unconditionally closed**:
  - File: `scripts/check/lib/bootstrap-planner-admission-bound.shs:99-107`.
  - After the structural check passes, it always executes
    `echo "bootstrap-policy-error: planner-admission-v2-producer-unavailable" >&2; return 1`.
  - Its own comment (lines 100-103): *"No canonical producer yet executes an
    admitted planner while capturing its build lineage… Until that non-circular
    producer exists, every body remains unadmitted."*
  - Consequence: **no receipt — however well-formed — can ever be admitted**, so
    `bootstrap-from-scratch.sh` (line 313) exits 64 before Stage 1. The task's
    literal command `bin/simple build bootstrap` routes through the same gate
    AND additionally cannot run at all here because no `bin/simple`/seed exists.
- No bypass exists: `grep` for `producer-unavailable|BYPASS|override|SIMPLE_BOOTSTRAP_ALLOW`
  in the wrapper found no escape env var; the gate is by design.

## Chicken-and-egg summary
1. Deploy needs a self-hosted Stage 4 binary → produced only by the bootstrap.
2. Bootstrap requires an admitted planner receipt.
3. The receipt verifier is hard-wired to fail (`producer-unavailable`).
4. Even the internal stage-replay path
   (`SIMPLE_BOOTSTRAP=1 <seed> native-build …`) is unavailable: there is **no
   Rust seed** to replay from, and building one ad-hoc via `cargo` + copying to
   `bin/release` is explicitly forbidden (`.claude/rules/bootstrap.md:38-50`) —
   it yields a seed masquerade, not a self-hosted binary, and never passes the
   admission gate.

## Native-store ACID proof
**Not obtained** — impossible without a deployed self-hosted binary. Not faked.

## Positive finding
The previously-documented Stage-3 defect (`unresolved type: ByteOrder` in
`cache_validator.spl`, `.claude/rules/bootstrap.md:10-22`) appears **fixed in
this certified tree**: `grep ByteOrder src/compiler/80.driver/cache/cache_validator.spl`
returns nothing. So the compiler-side Stage-3 blocker is likely resolved; the
remaining wall is purely the planner-admission-producer gate above.

## Precise resume command (once the planner-admission producer is wired)
```
cd /mnt/data/worktrees/ent-redeploy
# 1. Warm cache from a real warm tree (main's native_cache is only ~14 .o here — cold).
# 2. Produce an ADMITTED receipt via the canonical pure-Simple planner
#    (bootstrap_planner_v2_verify must return 0 — currently impossible).
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --bootstrap-receipt=<admitted-receipt-path>
# 3. On success: atomic deploy
#    cp build/bootstrap/stage4/x86_64-unknown-linux-gnu/simple bin/release/x86_64-unknown-linux-gnu/simple.new
#    mv …/simple.new …/simple
# 4. Verify: bin/simple --version (no seed banner); scripts/check/check-store-open-acid.shs → store_backend_acid=true
```

## Files
- This report.
- Bootstrap attempt log:
  `…/scratchpad/bootstrap.log` (single line: reason-receipt-required).
