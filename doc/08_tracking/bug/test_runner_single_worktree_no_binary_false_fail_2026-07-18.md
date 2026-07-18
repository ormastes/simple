# `simple test <spec>` false-FAILs "no examples executed" in binary-less worktrees

**Date:** 2026-07-18
**Severity:** high — blocks single-file spec verification in every detached
worktree that lacks a deployed release binary (the majority of campaign lanes).
**Status:** ROOT-FIXED in `.spl` (pure-Simple); verified on the deployed seed.
**Lane:** B4 (test-runner hang/SIGSEGV-under-load root-cause).

## TL;DR

The campaign symptom "single-file spec runs hang or SIGSEGV under concurrent
load" is **four distinct phenomena**, only one of which actually blocks spec
verification, and it is neither a hang nor a segv:

1. **Hang (rc=124)** — NOT reproducible on the current deployed binary for
   single-file targets. The "hang" reports are timeout-masquerade: each spec
   takes ~55–74s (see #4), and under CPU contention from concurrent build lanes
   a run can cross a per-file timeout and return rc=124, which reads as a
   "hang". The genuine indefinite hang is a **directory-target** issue in
   `test_runner_main.spl:307` (see `test_runner_fresh_seed_silent_noop_2026-07-17.md`),
   not single-file.
2. **SIGSEGV (rc=139)** — REAL and live on the current binary (kernel log shows
   `segfault at 11/12/1b … in libc.so.6`, error 4, at 14:35+ i.e. after the
   14:35 redeploy), but it is a **seed tag-box / pointer-as-int deref**, NOT
   memory pressure (ZERO oom-kill events; 80GB free). It correlates with
   **compiler/codegen-heavy invocations** (build/bootstrap/native-build lanes,
   TODO 548 = SimpleOS host-GPU *rebuilds*), NOT the test path: 40 concurrent
   `simple test` runs (vanilla + Vulkan specs) produced 0 crashes. Redeploy
   territory (seed-baked; pure-Simple codegen is documented clean for this
   class). Repro harness: `scratch_b4/repro_concurrent_139.sh`.
3. **"no examples executed" false-FAIL (THIS bug)** — the actual, deterministic
   blocker for worktree spec verification. Root-fixed here.
4. **Slowness** — every single-file `simple test` on the deployed seed spends
   ~55–74s loading the whole compiler + dumping ~200k lint/gc-warning lines
   during module load before the 140ms test phase. A timeout risk, not a wedge.

## Root cause (phenomenon #3)

`src/app/test_runner_new/test_runner_single.spl` runs the child spec by spawning
`process_run_bounded(binary, ["run", exec_path], …)` where
`binary = find_simple_binary()`, then counts ✓/✗ example markers in the child's
stdout. In a **detached git worktree**, `bin/release/<triple>/simple` (the
target of the `bin/simple` symlink) is gitignored and absent, so
`find_simple_binary()` misses both its `argv[0]` check and its `bin/simple`
check and returns a **dead `./bin/simple`**. The child launch then fails:

```
B4DBG binary=./bin/simple exec_path=…vanilla_spec.spl code=-1 out_len=0 err_len=0
```

`code=-1`, empty stdout/stderr ⇒ `count_real_examples` sees 0 markers ⇒ the run
falls into the zero-executed branch and prints **"error: test-runner: no
examples executed"**, marking `Passed: 0, Failed: 1, FAIL` — for EVERY spec,
including a vanilla `describe/it`. The message blames the spec for a
runner/environment fault.

Proof it is purely binary resolution (not the seed, not the spec, not the
counter): pointing `SIMPLE_BINARY` at the real deployed binary makes the exact
same spec PASS —

```
SIMPLE_BINARY=<real> simple test vanilla_spec.spl
  → code=0 out_len=66 → Passed: 1, Failed: 0, PASS
```

The sibling `test_runner_client.spl:100` already carries a `/proc/self/exe`
fallback (with a comment claiming parity with `test_runner_single.spl`); the two
had **drifted** — the single-file runner never got it.

## Fix (pure-Simple, root)

`src/app/test_runner_new/test_runner_single.spl`:

1. `find_simple_binary()` — add the `/proc/self/exe` fallback (reuse the running
   interpreter) before the dead `./bin/simple`, mirroring
   `test_runner_client.spl`'s `simple_binary()`.
2. New fail-closed branch: when the child returns `code == -1` with empty
   stdout+stderr and it is not a timeout, print
   `"failed to launch test binary '{binary}' … set SIMPLE_BINARY …"` instead of
   letting it fall through to "no examples executed". Purely additive to the
   diagnostics; does NOT weaken the zero-executed / timeout greenwash guards.

**Caveat (Linux-only):** the `/proc/self/exe` fallback is Linux-only. On
macOS/BSD a binary-less worktree still falls through to the dead `./bin/simple`
(no regression vs. before, but the auto-resolution does not reach non-Linux
worktrees). Those hosts must use the `SIMPLE_BINARY` workaround below.

**Propagation boundary:** the deployed seed interprets *each worktree's own*
`test_runner_single.spl`, so this committed fix only helps the worktree it lands
in. Other NO-BIN lanes stay broken until this change reaches main and they
rebase — OR they use the zero-landing workaround: `SIMPLE_BINARY=~/.local/bin/simple`
(proven to PASS even on the un-fixed source).

**Verified on the deployed seed in a binary-less worktree (no SIMPLE_BINARY):**

```
simple test scratch_b4/vanilla_spec.spl            → Passed: 1, PASS  (was: no examples executed)
simple test test/01_unit/app/io/io_numeric_guard_spec.spl → Passed: 2, PASS  (matches S88 fresh-seed)
```

## Deterministic repro / regression guard

`scratch_b4/repro_no_examples_false_fail.sh` — asserts a trivial spec PASSES
under default binary resolution in the worktree (guards against re-drift of the
`/proc/self/exe` fallback).

## Is verification blocked? (campaign answer)

**No — not blocked for any lane with a resolvable binary.** After this fix, a
binary-less worktree resolves `/proc/self/exe` and runs specs for real
(~60s/spec, real PASS/FAIL). Interim workaround for un-rebuilt lanes:
`SIMPLE_BINARY=~/.local/bin/simple simple test <spec>`. The only hard block that
remains is the seed **SIGSEGV (#2)** for build/codegen-heavy SimpleOS lanes,
which is redeploy-gated (seed rebuild; out of pure-Simple scope), NOT a
test-runner defect.

## Files

- Fixed: `src/app/test_runner_new/test_runner_single.spl`
- Repro (segv): `scratch_b4/repro_concurrent_139.sh`
- Repro (this bug): `scratch_b4/repro_no_examples_false_fail.sh`
