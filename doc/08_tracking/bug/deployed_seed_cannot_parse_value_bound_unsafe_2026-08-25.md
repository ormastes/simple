# Deployed seed cannot parse current stdlib — every seed-run gate is blind

**Date:** 2026-08-25
**Severity:** CRITICAL (not one gate — every tool that runs on the deployed `bin/simple` and touches `std.io_runtime` fails at parse time)
**Status:** FIXED 2026-08-25 05:16 UTC — seed-sibling refresh deployed (see "Resolution" below). Self-hosted redeploy remains a separate, still-open item.
**Found by:** re-measuring `check-engine-differential.shs` with a pinned binary and a clean bracket

## The skew

| what | commit | time (2026-08-24) |
|---|---|---|
| seed parser learns value-bound `val v = unsafe(capabilities: [ffi]):` | `d2d0bec2e40` "fix(parser): retain value-bound unsafe blocks" | 17:03 |
| stdlib starts USING that form (`env_get`, `getpid`, `time_now_unix_micros`, … 18 sites) | `7ef30bafe0e` "fix(sffi): harden environment and clock owners" | 17:34 |
| deployed `bin/simple` was built | — | **2026-08-23 04:47** |

The deployed seed predates both. It parses `unsafe(...)` as a function call:

```console
$ cat unsafe_vb.spl
extern fn rt_env_get(key: text) -> text?
fn main():
    val v = unsafe(capabilities: [ffi]):
        rt_env_get("HOME")
    print("V=" + (v ?? "?"))
$ bin/simple run unsafe_vb.spl          # 60650360 B, 2026-08-23 04:47, sha f6521b60…
error[E1002]: function `unsafe` not found
```

Five lines, no stdlib import — the parser itself is the failure.

## Blast radius

`std.io_runtime.env_get` is imported by essentially every check driver. Measured
on `check-engine-differential.shs` with `DIFF_FILTER=utf8`:

```
error[E1002]: function `unsafe` not found
ERROR — nothing was checked (harness failed but printed no parsable
  'divergences: N (M NEW, unbaselined)' summary; the count is unknown)
```

exit 2 in ~1 s, binary identity identical before and after. So the engine-
differential gate has **no verdict at all** on current origin — not RED, blind —
and the same is true of any gate whose driver reaches `env_get`. The hardening
plan's §22.5 "interpreter/JIT/native diff = 0" is currently unmeasurable.

## Why this was missed once already

An earlier check reported "env_get works, does not reproduce". That check ran
on the shared working tree, whose `io_runtime.spl` was an OLDER generation with
**zero** value-bound `unsafe` sites (origin has four). The seed parsed the old
file fine. Same lesson as §28.5 of the hardening plan: a result from the shared
tree is not evidence about origin.

## Not a divergence, not a gate bug

Nothing here says any engine disagrees with another. The gate's corpus (13
fixtures: lists, strings, utf8, numerics) never reached comparison. Do NOT
baseline anything and do NOT "fix" the harness by removing its `env_get` — the
harness is correct; the compiler running it is stale.

## Resume

- **Owner:** bootstrap / seed-redeploy lane. This is the same redeploy the two
  JIT records (`jit_option_of_enum_payload_double_unwrap_2026-08-24.md`,
  `match_arm_bound_value_method_call_returns_none_2026-08-24.md`) and the
  stage-binaries guard are already waiting on.
- **Unblock:** deploy a seed built from `≥ d2d0bec2e40`. A local build was
  attempted (`/mnt/data/cargo-target-engdiff-a7f95`) and failed with dep-info
  files vanishing mid-build — consistent with an external cleaner on the box.
- **Done when:** the 5-line probe above prints `V=/home/…`, and
  `check-engine-differential.shs` prints a `PASS —`/`FAIL —` line (either is
  progress; `ERROR — nothing was checked` is the current blind state).

## Resolution (2026-08-25 05:16 UTC — seed-sibling refresh, NOT a self-hosted redeploy)

- Deployed `bin/release/x86_64-unknown-linux-gnu/simple`:
  pre `f6521b60b67d38944016b82451ac60c522375410c60dec7178d5c06bd063bde7`
  (60650360 B, 2026-08-23 04:47) -> post
  `706fa63677e053add9e09b8a2238dbece43019ce43cdaca5e95bc30be53689d6`
  (60641352 B, 2026-08-25 05:16). Deployed via `cp -> simple.new && mv`.
- Provenance: Rust seed, `cargo build --release --bin simple` from a CLEAN
  worktree at origin/main `e8db788629b` (`>= d2d0bec2e40`, so the parser
  carries "retain value-bound unsafe blocks"). Banner still says seed — that is
  the honest state; this does not close the self-hosted (Stage 4) redeploy.
- Done-when evidence: the 5-line probe now prints `V=/home/ormastes` on
  `bin/simple run` (was `error[E1002]: function `unsafe` not found`);
  arithmetic smoke prints `5`.
- Rollback receipt (pre/post copies, hashes, smoke, exact restore command):
  `/mnt/data/tmp/claude-1000/seed-rollback/RECEIPT.md`.
- `DIFF_FILTER=utf8 sh scripts/check/check-engine-differential.shs` on the refreshed seed: `PASS — 17 fixture(s) checked, unbaselined divergence(s)=0` (exit 0) — the gate has a verdict again, no longer blind.

## Re-confirmed 2026-08-26 (audit pass)

Re-ran the 5-line probe against the currently-deployed
`bin/release/x86_64-unknown-linux-gnu/simple` on the host (hash
`ae73a992d514f353005adcddcf252497e80fb52ccda5eab8b9db4b35e795427e`, mtime
2026-08-26 01:16 — redeployed again since this record's 05:16 UTC entry, still
post-fix):

```
$ bin/release/x86_64-unknown-linux-gnu/simple run unsafe_vb.spl
V=/home/ormastes
```

Fix still holds; no regression. No change needed to this record beyond this
confirmation.
