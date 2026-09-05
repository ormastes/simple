# The pre-push hook was UNPASSABLE from every Linux host, permanently, by construction

- **Filed:** 2026-08-17
- **Severity:** P0 — this is the mechanical cause of the `--no-verify` epidemic.
  A chain that cannot be satisfied forces every push to bypass ALL of it.
- **Status:** FIXED for the platform axis (this row). 11 other fatal guards
  remain red — see the census at the bottom.

## The defect

`scripts/check/check-x25519mlkem768-metal-ntt.shs:36-39` (before this fix):

```sh
if [ "$(uname -s)" != Darwin ]; then
    echo "STATUS: BLOCKED X25519MLKEM768 Metal NTT requires native macOS"
    exit 2
fi
```

It is a **FATAL** member of the chain: `pre-push-conflict-tree-guard.shs`'s
`run_guard()` (line 255) sets `status=1` on any non-zero rc **or** on the text
`ERROR —`/`DO NOT PUSH`. There is no advisory path in that hook — all 62
invocations are fatal.

Metal does not exist on Linux and cannot be installed there. So the condition was
**unsatisfiable by construction**: no action by any Linux lane, at any time, with
any amount of debt paid down, could ever clear it.

Measured on this host:

```
$ sh scripts/check/check-x25519mlkem768-metal-ntt.shs
STATUS: BLOCKED X25519MLKEM768 Metal NTT requires native macOS
rc=2
$ uname -s
Linux
```

## Why this is the root cause of something much bigger

Every lane on this Linux machine was told, correctly, "never use `--no-verify`",
while the hook was mathematically incapable of passing. The observable result is
a repo where `--no-verify` is normal, two unbuildable trees reached `main` in one
day, and the guards that *do* work were bypassed along with the one that never
could. A gate that always says no teaches people to walk around it, and they then
walk around the gates that were protecting something.

## The distinction that makes this a bug and not a policy

The sibling guards `check-x25519mlkem768-cuda-ntt.shs` and
`-vulkan-ntt.shs` also print `BLOCKED` and exit 2 — **and they are right to.**
Their blocked condition is "`ptxas` / `glslangValidator` is not installed":
satisfiable, actionable, correctly fail-closed. (Both in fact PASS on this Linux
box, which is the point.)

"You are not running macOS" is a categorically different statement. Conflating
"this tool is missing, go install it" with "this platform cannot host this
technology" is the defect.

## The fix

Absent platform => `SKIP`, exit 0, stated loudly and never counted as evidence.
Platform present but tooling missing => unchanged `BLOCKED`/exit 2. On macOS the
guard's behaviour is byte-for-byte what it always was, so the lane that CAN
produce this evidence still enforces it exactly as before.

`SIMPLE_REQUIRE_METAL=1` restores the hard failure for a macOS-only CI lane that
wants "this must actually have run" rather than "this was allowed to skip".

This mirrors the three-way classification `check-c-runtime-compiles-push.shs`
already uses and that this repo already blesses: compiled / SKIP for a genuinely
unavailable external dependency, reported separately and never counted as
compiled / FAIL for everything else.

Verified 2026-08-17:

```
default on Linux      -> STATUS: SKIP ... NO Metal evidence was produced by this
                         run and none is claimed          rc=0
SIMPLE_REQUIRE_METAL=1 -> STATUS: BLOCKED ... host is Linux  rc=2
```

## What this does NOT fix

Making the hook *satisfiable* is not the same as making it *green*. A full census
of all 62 fatal invocations on 2026-08-17 found **11 fatal guards red and 4
UNVERIFIED** (killed at a 15-minute timeout — cost, not verdicts):

| guard | attribution |
|---|---|
| `check-tree-size-push` | local commits (net −244 files); fixed separately for the banding defect |
| `check-test-tree-divergence` | pre-existing repo-wide debt (878 vs 814 baselined) |
| `check-wm-lane-boundary` | pre-existing (131 total), 11 flagged NEW |
| `check-lint-binary-staleness` | environmental — deployed `bin/simple` lacks 2/2 fresh lint markers; needs a redeploy, forbidden to lanes |
| `check-class-identity-engine-matrix` | pre-existing pureSIMPLE gap (10/11), same root as the stale seed |
| `check-engine-differential` | pre-existing single unbaselined divergence |
| `check-render-perf-milestone-gate` | pre-existing — no Results line from the perf spec |
| `check-implicit-self-field-assignment` | stale deployed oracle; PASSES against a seed built from this tree |
| `check-engine-claiming-specs-use-probe` | fixed separately (committed-content scoping) |
| `check-native-trailing-default-param` | real compiler bug: multi-module native-build loses the entry module's own class methods |
| `check-jit-closure-blockers` | fixed separately (counted baseline) |

Two of these are **not fixable by any individual lane**: `lint-binary-staleness`
and `implicit-self-field-assignment` both require redeploying `bin/simple`, which
~16 concurrent lanes share and which lanes are forbidden to touch. Until a
redeploy lane exists, the hook cannot go green on this host no matter what else is
fixed. That is a policy question, not an engineering one, and it needs an owner.
