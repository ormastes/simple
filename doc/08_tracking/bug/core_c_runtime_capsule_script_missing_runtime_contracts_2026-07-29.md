# `build-core-c-bootstrap-runtime-capsule.shs` fails: `simple_contract_check` provider moved

- **Filed:** 2026-07-29
- **Status:** SUPERSEDED
- **Script:** `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`
- **Severity:** blocks the C-capsule lane for rebuilding `libsimple_runtime.a`

## Symptom

The script fails with `archive-simple_contract_check-provider-missing`.

## Cause

`simple_contract_check` moved to `src/runtime/runtime_contracts.c`, which the
script neither compiles nor accepts as a provider. The script's source list is
stale relative to the runtime tree.

## Why it matters

Found while recovering the stage-4 bootstrap from a stale-runtime link failure
(undefined `rt_transient_heap_promote` / `rt_file_is_regular_no_follow`: every
prebuilt `libsimple_runtime.a` on the host was missing symbols that
`src/runtime/runtime_native.c` defines). The C-capsule script is one of the two
lanes for rebuilding that archive; with it broken, only the cargo lane works:

```
cargo build --profile bootstrap -p simple-runtime   # inside the (work)tree
nm target/bootstrap/libsimple_runtime.a | grep -c 'rt_transient_heap_promote\|rt_file_is_regular_no_follow'  # must be >= 2
```

A stale archive fails at STAGE-3 LINK time with plain `undefined reference`
errors — nothing names the archive as the culprit, so it reads like a compiler
bug. Check the archive with `nm` before suspecting codegen.

## Fix

Add `runtime_contracts.c` (and audit for other moved providers) to the capsule
script's compile list, then prove the gate both ways: capsule build succeeds
from a clean tree, and deleting a provider makes it fail naming that provider.

## 2026-11-10 status — P3 runtime-lane triage (worktree simple-p3-rt-20261110)

**Verdict: SUPERSEDED — the requested fix is in the tree at base
1504212d788b.** `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`
now:

- compiles `runtime_contracts.c` as a first-class `SOURCE_FILES` entry
  (alongside the runtime_native/legacy_core/simd sources), and
- proves the provider exactly as this doc's "Fix" section asks: `nm`
  text-symbol assertions that `simple_contract_check` /
  `simple_contract_check_msg` resolve in the archive AND in
  `runtime_contracts.o`, plus `assert_single_provider` checks pinning each to
  `runtime_contracts.o` alone (no duplicate-definition escape).

Pickaxe (`git log -G runtime_contracts -- <script>`): the composition arrived
with PR #7597 (merge `9e7e7a526edb`, 2026-11-07) — the only history touching
this script for that provider.

Execution label: **host-limited** — the capsule script intentionally supports
only Linux/Darwin (`*) die "unsupported-host:$PLATFORM"`), so it cannot be run
to completion from this Windows (MINGW64) host; the verdict above is
script-content evidence at a pinned base, recorded honestly rather than
claimed as a run. No change made.


## Triage 2026-11-10 (p3-boot4 lane, assignment row 27)

**Verdict: SUPERSEDED (corroborated at this lane's base).**

Independently re-verified on the p3-boot4 worktree, confirming the
2026-11-10 p3-rt note:

- `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` compiles
  `runtime_contracts.c` as a first-class source entry (`:135`), proves the
  provider with `nm` text-symbol assertions against both the archive and
  `runtime_contracts.o` (`:336`, `:384`), and pins single-provider ownership
  via `assert_single_provider simple_contract_check runtime_contracts.o` and
  the `_msg` twin (`:425-426`) — exactly the two-way proof (build succeeds;
  deleting a provider fails naming it) this doc's "Fix" section demanded.
- Fix merge `9e7e7a526edb` (PR #7597) is an ancestor of this lane's base.

Host-limited: the script intentionally supports only Linux/Darwin
(`*) die "unsupported-host:$PLATFORM"`), so it cannot be executed to
completion from this Windows (MINGW64) host; verdict is script-content
evidence at a pinned base, recorded honestly rather than claimed as a run.
No change made in this lane.

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: SUPERSEDED-by-prior-lane** — spot-check corroborates both
2026-11-10 addenda (p3-rt and p3-boot4). No deep triage redone.

Spot-check at this lane's base (790b54f7c4fc):

- `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` still compiles
  `runtime_contracts.c` as a first-class source entry (:135), asserts the
  two `simple_contract_check*` text symbols via `nm` against the object
  (:336, :384), and pins single-provider ownership (:425-426) — exactly the
  two-way proof the doc's "Fix" section demanded.
- Fix merge `9e7e7a526edb` (PR #7597) is an ancestor of this base.
- Host-limited unchanged: the script intentionally supports only
  Linux/Darwin (`*) die "unsupported-host:$PLATFORM"`), so it cannot be run
  to completion from this Windows host; the verdict is script-content
  evidence, recorded honestly rather than claimed as a run.
- seed-smoke (refreshed seed 0791c2b7f4a7): `bin/simple.exe check
  src/lib/common/contracts/contracts.spl` exit 0 (W-STR-BRACE-001 lint
  warnings only) — contracts stdlib surface healthy under the seed check
  path.

No change made in this lane.
