# SFFI-v2 authority audits: brittle exact-count assertions + silent failure

- Date: 2026-09-02
- Status: fixed for 5 of 46 guards (group 1); same class open in the rest
- Gate: `scripts/check/check-sffi-v2-authority.shs` (blocking push gate, was
  `FAIL — 18 of 46 guard(s) failed`, now `FAIL — 13 of 46`)

## Two defect classes

### 1. Silent failure (all 46 audits)

Every audit is `set -eu` plus bare `test`/`grep -q`. A failing assertion aborts
the script **before** its `echo ... PASS` line, so the whole guard exits 1 with
**zero output**. Reproducing required `sh -x`. A guard that fails with no output
is how this sat RED long enough that every push in the repo switched to
`--no-verify`, bypassing all 19 push gates.

Fix (this change, 5 audits): a verdict framework per `.claude/rules/vcs.md` —
assertions are recorded, never `set -e`-aborted, and the verdict is the LAST
line on stdout:

- `PASS — <n> assertion(s) checked; <summary>` exit 0
- `FAIL — <label> (expected X, actual Y)` exit 1
- `ERROR — nothing was checked (<reason>)` exit 2

Non-vacuity is absolute: 0 assertions checked, or a missing audited module, is
ERROR, never PASS.

### 2. Brittle exact-count assertions

Four of the five audits asserted `grep -c '^extern fn rt_' == N`, conflating
*declaration count* with *raw-owner count*. Commit `1b0172a392a`
("refactor(rt): migrate direct rt_* calls in 80.driver to typed std aliases —
batch 3", ratchet 6609 -> 6478) legitimately replaced raw `extern fn rt_*`
declarations with typed `use std.…` aliases. The `unsafe(capabilities: [ffi])`
wrapper blocks — the actual invariant — were untouched, but the declaration
count fell (lease 8->1, admission 4->2, fast_gc 12->4, mark_sweep 7->1) and the
audits went red on a *correct* change, in the safe direction.

**Classification: legitimate drift, not a violation.** Fix is in the audits:
assert the stable invariants instead of the stale constant —

- `unsafe(ffi)` block count == N (unchanged: 8 / 4 / 12 / 7);
- every `unsafe(ffi)` block wraps exactly one call on the next line;
- every remaining `extern fn rt_` carries an `@unsafe(capabilities: [ffi])` tag;
- raw `extern fn rt_` count `<=` a recorded ratchet ceiling — further migration
  may only lower it, a NEW raw extern fails.

Verified the ratchet still bites: appending a tagged `extern fn rt_bogus` to
lease.spl yields
`FAIL — raw rt_* extern declarations (ratchet ceiling; migration may only lower it) (ceiling 1, actual 2)`.

## Real violation found: bootstrap argument probe

`scripts/audit/bootstrap-probe-args-sffi-authority.shs` was **not** stale drift.
`src/app/cli/bootstrap_probe_args.spl` had lost its SFFI-v2 annotations:

```
-@unsafe(reason: "raw bootstrap argument-array ABI", capabilities: [ffi])
 extern fn rt_get_args() -> [text]
-    val args = unsafe(capabilities: [ffi]): rt_get_args()
+    val args = rt_get_args()
```

Removed by `e274cd33719` ("chore: merge all share-history worktree branches into
main") — a stale-snapshot merge clobber of the hardening landed in `1b4edca296c`
(SFFI v2 source-boundary hardening, #75). This is the sync-clobber class in
`.claude/rules/vcs.md` § "Sync must never clobber". A raw FFI extern with no
capability annotation and an unwrapped call site is exactly what this gate
exists to block. **Fixed in the SOURCE** (restored from `1b4edca296c`); the
audit's assertions were left unchanged.

## Guidance for the remaining 13

Do not bump a count to green without reading what moved it. An exact-count
assertion that dropped because raw FFI was migrated to typed aliases is drift;
an annotation or wrapper that vanished is a violation and the source is wrong.
