# BIP-39 mnemonic_to_seed KAT block cannot complete — 60 s run watchdog vs interpreted PBKDF2

- **Date:** 2026-07-28
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Resolution (2026-07-28, later the same day)

Three stacked defects, all fixed:

1. **The ~60 s killer was a detached daemon**, not the runner or CLI:
   `scripts/resource/kill_simple_monitor.shs` SIGKILLed any `simple run|test` at
   ≥95% CPU past 60 s and never saw the run's env. Fixed in `a6819dcc788`
   (reads `SIMPLE_TIMEOUT_SECONDS` live from `/proc/<pid>/environ`, writes an
   explicit `error: TIMEOUT: killed by kill_simple_monitor` into the victim).
   Details: `reference` in the fail-open ledger; the daemon's own log names
   every kill.
2. **TV2's expected seed was FABRICATED** — 35-byte shared prefix, then
   divergence. The implementation was correct and the test was failing it.
   Verified against independent PBKDF2-HMAC-SHA512 and the official BIP-39
   vectors. Also: TV4/TV5/TV6 asserted only `len()==64` and the empty-passphrase
   example asserted only inequality. All made real KATs in `ea4ae7e4062`.
3. With (1) raised via `SIMPLE_TIMEOUT_SECONDS` and (2) corrected, the full spec
   is green: **24 examples, 0 failures**, including all six TREZOR seed vectors
   and the no-passphrase KAT (blocks 1+7+6+3+7). Evidence:
   `~/.claude/jobs/4403a7d8/tmp/bip39_kat2.log`.

Still true and still open elsewhere: the seed-number caveat below (all timings
are SEED + debug-build numbers), the unrouted `rt_pbkdf2_hmac_sha512` fast-path
(header claim corrected in `3a19e6640ef`), and the `_set_bit` W1006 demotion —
which must NOT be "fixed" with `mut` until the list-`.get()` unbox fix
(`ca2d18fac83` line) is in the deployed binary.

---
- **Spec:** `test/01_unit/os/crypto/bip39_kat_spec.spl`
- **Module:** `src/os/crypto/bip39.spl`, `src/os/crypto/bip39_wordlist.spl`
- **Binary that produced all evidence below:** the **Rust bootstrap seed**
  (`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, prints the
  "bootstrap seed only" banner). The `simple test` single-file path re-execs
  `src/compiler_rust/target/debug/simple` — an **unoptimized debug build**.
  No pure-Simple self-hosted binary was available for this run, so every number
  here is a SEED + DEBUG-BUILD number and must be re-measured after redeploy.

## Observed result (not inferred)

`bin/simple test test/01_unit/os/crypto/bip39_kat_spec.spl`

```
Results: 18 total, 17 passed, 1 failed
Duration: 61451ms
FAIL test/01_unit/os/crypto/bip39_kat_spec.spl
```

The 17 passes are the four non-PBKDF2 describe blocks (1 + 7 + 6 + 3):

- `BIP-39 wordlist integrity` — 1 example, 0 failures
- `BIP-39 entropy_to_mnemonic` — 7 examples, 0 failures
- `BIP-39 mnemonic_to_entropy (round-trip)` — 6 examples, 0 failures
- `BIP-39 error cases` — 3 examples, 0 failures

The fifth block, `BIP-39 mnemonic_to_seed` (6 `it` blocks), prints its header
and then produces **nothing**. Not one of its six examples ever reports. The
process is killed before the first one finishes.

**Calibration performed** (per the runner caveat that a green may be vacuous):
`expect(bip39_word(0)).to_equal("abandon")` was temporarily changed to expect
`"CALIBRATION_SHOULD_FAIL"`. The run went red —
`✗ is the official 2048-word BIP-39 English list` / `1 example, 1 failure`.
The edit was reverted. The 17 greens are therefore real executed assertions.

## Root cause: a hard ~60 s wall-clock watchdog on the run path

Running the child binary directly, outside the test runner, reproduces it:

```
src/compiler_rust/target/debug/simple run test/01_unit/os/crypto/bip39_kat_spec.spl
  → Command terminated by signal 15
  → CHILD_WALL=63.42s  CHILD_CPU=63.05s  CHILD_MAXRSS=89600kB  exit 143
```

This is **not** the test runner's limit — `test_runner_single.spl` defaults
`timeout_secs = 120`. It is a global watchdog in the `run` path. Control test,
a trivial arithmetic spin loop with no crypto at all:

```
simple run /tmp/spin.spl  → signal 15, SPIN_WALL=64.02s, exit 143
```

Any run exceeding ~60 s is SIGTERMed. `SIMPLE_TIMEOUT_SECONDS` (documented in
`src/compiler_rust/driver/src/cli/init.rs` as the knob, "0 = disabled,
default: 0") does **not** raise it — `SIMPLE_TIMEOUT_SECONDS=3600` still died
at 62.03 s. So the ceiling is not overridable from the environment on this
binary, and the seed KAT vectors cannot be proven with this toolchain.

## Where the time actually goes — measured, per block

Timestamped from process start, real spec, one run:

| t | block |
|---|---|
| t+1s | `BIP-39 wordlist integrity` starts |
| t+2s | 1 example, 0 failures |
| t+2s | `BIP-39 entropy_to_mnemonic` starts |
| t+3s | 7 examples, 0 failures |
| t+3s | `BIP-39 mnemonic_to_entropy (round-trip)` starts |
| t+6s | 6 examples, 0 failures |
| t+6s | `BIP-39 error cases` starts |
| t+7s | 3 examples, 0 failures |
| t+7s | `BIP-39 mnemonic_to_seed` starts |
| t+63s | SIGTERM — still inside the FIRST example |

**Everything that touches the wordlist finishes in 7 seconds.** The
scan-heaviest block — six full `mnemonic_to_entropy` round-trips, i.e. 90 word
lookups plus the 2048-entry ordered self-check — costs **3 seconds**. One
`bip39_mnemonic_to_seed` costs **more than 56 seconds** and does not finish.

Isolation probe, one `bip39_mnemonic_to_seed` and nothing else, **zero**
wordlist lookups in the whole file:

```
PROBEB_WALL=64.87s  PROBEB_CPU=64.59s  exit 143 (signal 15) — did not complete
```

That settles attribution: the cost is entirely inside PBKDF2, and none of it is
the wordlist.

## Verdict on `bip39_word_index`'s linear scan: NOT the bottleneck. Change nothing.

The linear scan is roughly **3 seconds out of a >63 second run**, and the probe
that performs zero scans is just as slow. Replacing it with a lookup dict would
save ~3 s on a cold path while doing nothing about the ~56 s wall.

The scan should stay exactly as it is. It uses `==` rather than a binary search
deliberately: ordered text `<`/`>` has lowered to raw pointer comparison in this
toolchain (the sspec false-green root cause, 2026-07-22), which would make a
binary search over 2048 words silently return **wrong indices** — and a wrong
BIP-39 index means mnemonics no other wallet can recover. Correctness dominates
absolutely here. No optimization was applied.

## Contributing factor: whole-program JIT fallback

Every run logs:

```
[INFO] JIT compilation failed, falling back to interpreter:
  HIR lowering error: Memory safety error [W1006]: mutation without mut
  capability: mutation requires `mut` capability while lowering _set_bit at 87:21
```

That is `src/os/crypto/bip39.spl:77` `_set_bit`, which does
`bytes[byte_idx] = new_byte` on a `bytes: list` parameter carrying no `mut`
capability. Per `.claude/rules/testing.md`, one unsupported operation demotes
the **whole program** to the tree-walk interpreter — so the pure-Simple
SHA-512/HMAC chain under PBKDF2 runs interpreted.

The chain is pure Simple end to end with no native fast path on the hot route:
`bip39_mnemonic_to_seed` → `pbkdf2_sha512_bytes` (c=2048) → `hmac_sha512_bytes`
→ `sha512_bytes`. Neither `hmac.spl` nor `sha512.spl` declares an `extern`.

Note the spec's own header comment is **wrong** on this point:

> `NOTE: mnemonic_to_seed uses PBKDF2-HMAC-SHA-512 with c=2048. The native`
> `rt_pbkdf2_hmac_sha512 fast-path handles interpreter-mode performance`
> `(see pbkdf2.spl for details).`

`rt_pbkdf2_hmac_sha512` does exist as an interpreter extern
(`src/compiler_rust/compiler/src/interpreter_extern/pbkdf2.rs`, registered in
`interpreter_extern/mod.rs:2189`), but **nothing routes to it**:
`pbkdf2_sha512_bytes` in `src/lib/common/crypto/pbkdf2.spl` calls
`_pbkdf2_block_sha512`, which loops `hmac_sha512_bytes` in pure Simple. The
"fast-path handles it" claim is unsupported, and `pbkdf2.spl`'s own header says
the opposite — it documents interpreter PBKDF2 as a known limitation and cites
`doc/08_tracking/bug/pbkdf2_interpreter_slow_c4096_2026-06-15.md`.

## What is and is not established

- **Established:** the wordlist module resolves, the 2048-entry table is intact
  and index-aligned, and all four non-PBKDF2 blocks genuinely pass (17/17,
  calibrated red). Before `627552a041c0` the module did not exist at all and the
  whole spec was dead code, so this is a real forward step.
- **NOT established:** that `bip39_mnemonic_to_seed` produces the correct
  Trezor seed vectors. Those six examples have never executed to completion on
  this toolchain. The end-to-end BIP-39 seed path remains **unverified**.

## Suggested routes (none applied here — out of scope for this pass)

1. Route `pbkdf2_sha512_bytes` to the already-registered
   `rt_pbkdf2_hmac_sha512` extern, and correct or delete the spec's false
   fast-path comment.
2. Fix `_set_bit`'s missing `mut` capability so the program stops falling back
   off the JIT.
3. Give the run path an overridable watchdog — `SIMPLE_TIMEOUT_SECONDS` is
   documented as the knob but does not take effect.

Until one of those lands, mark the `BIP-39 mnemonic_to_seed` block as a known
incomplete rather than reporting the spec as passing.
