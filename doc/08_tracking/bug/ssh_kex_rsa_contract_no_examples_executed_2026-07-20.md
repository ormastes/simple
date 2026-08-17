# ssh_kex_rsa_contract_spec: import path fixed, but 0 examples execute (likely private-helper symbol collision)

## Symptom

`test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` originally failed with:

```
semantic: function `ssh_sign_exchange_hash` not found
```

Fixed (value-preserving, verified the symbol actually lives there): the spec
imported `ssh_sign_exchange_hash` from `os.apps.sshd.ssh_kex`, but that function
is defined in `os.apps.sshd.ssh_kex_crypto` (confirmed via
`grep -rn "fn ssh_sign_exchange_hash" src/` — only one definition, at
`src/os/apps/sshd/ssh_kex_crypto.spl:352`). Split the single `use` line into:

```spl
use os.apps.sshd.ssh_kex.{HostKeySet}
use os.apps.sshd.ssh_kex_crypto.{ssh_sign_exchange_hash}
```

After the import fix, the module now compiles and resolves, but the spec still
does not pass — it takes ~64s to run (previously ~444ms when it failed fast on
the unresolved-symbol error) and terminates with:

```
error: test-runner: no examples executed
```

with zero `✓`/`✗` lines printed for the single `it` block (`"produces a
rsa-sha2-512 blob that verifies with a real RSA key"`) — only the `describe`
header line appears, then compiler warnings, then the error. This suggests the
`it` block itself crashes/hangs during real RSA + X25519/exchange-hash
computation rather than failing a normal assertion.

## Root-cause hypothesis

The build emits 4 `compiler_cross_module_private_symbol_collision` warnings for
helpers used by this exact crypto path (`_cswap_pair`, `_hex_digit`,
`_ladder_step`, `_u8_at` — all X25519/hex/byte-access primitives), which is a
**pre-existing tracked defect**: see
`doc/08_tracking/bug/compiler_cross_module_private_symbol_collision_2026-06-16.md`.
That doc already warns that JIT call sites can dispatch to the wrong
co-compiled definition when signatures differ across modules. Given this spec
exercises real RSA-SHA2-512 signing + verification, a wrong-helper dispatch
into the crypto path (e.g. `_u8_at` picking the `([u8], u64)->u8` overload vs
`([u8], i64)->u8`, or `_hex_digit`/`_ladder_step` picking an X25519 vs generic
variant) is a plausible cause of a silent crash/hang that swallows the `it`
block's execution entirely. Not confirmed by stepping through — flagging the
correlation for whoever owns the collision bug to check this spec as a
concrete repro once that's fixed.

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl --no-session-daemon
```

## Affected specs

- `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` (import path fixed
  in-place; spec still does not go green — 0 examples executed)

## Re-reproduced 2026-08-17 — symptom has CHANGED, still OPEN
`bin/simple test test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl --no-session-daemon`
(seed binary `bin/release/x86_64-unknown-linux-gnu/simple`, exit code read
directly, never through a pipe) now ends:

    ... executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=child-timeout budget_ms=120000
    Results: 1 total, 0 passed, 1 failed   Duration: 120250ms   (rc=1)

So this is **not** the old "0 examples in ~64s / suspected private-helper symbol
collision". The example is discovered and started; the child is killed at the
runner's default 120s budget. Raising it with the supported
`# @timeout_secs 600` header directive (parsed by
`src/app/test_runner_new/test_runner_main.spl:120 spec_timeout_secs_directive`)
did NOT produce a result either — still no output after >600s. The cost is
therefore in the pure-Simple RSA path exercised by the spec
(`os.crypto.rsa.rsa_sha512_verify` modexp, plus `openssl genpkey` fixture) under
the tree-walk interpreter that `bin/simple test` hard-defaults to, i.e. a
src/lib-side perf defect, not a runner budget or a symbol collision.
The directive was deliberately NOT left in the spec: a fast honest 120s red is
better than a >10min hang in the suite. A note recording this sits in the spec
header.
Unblock: make `os/crypto/rsa` modexp usable under the interpreter (or give the
spec a smaller key / precomputed fixture). Owner: crypto lane (src/ scope).
