# bcrypt salt encoding is corrupted on the JIT lane (`list<i64>` param miscompile)

Status: DUPLICATE of jit_param_passed_list_element_read_returns_tagged_2026-08-08.md
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Filed:** 2026-08-08 · **Severity:** high (silent wrong output in shipped security
code; no diagnostic) · **Engine:** JIT via `bin/simple run` on the Rust **seed** binary
`bin/release/x86_64-unknown-linux-gnu/simple`. **Interpreter: CORRECT.**
**Root cause:** `jit_param_passed_list_element_read_returns_tagged_2026-08-08`
(see Sighting C there) — this doc exists so the *security consequence* is findable by
name rather than buried in a codegen entry.

## Summary

`src/lib/common/bcrypt/salt.spl` declares two functions that index a `list<i64>`
parameter:

```simple
fn bcrypt_encode_base64(bytes: list<i64>) -> text
fn encode_salt(salt_bytes: list<i64>, cost: i64) -> text
```

Under the JIT, an element read from a `list`/`list<T>`-spelled parameter returns the
value still carrying its small-int tag (a pure arithmetic left-shift-by-3 that is never
undone). Both functions therefore encode the **wrong bytes**.

## Reproduction

`.nvprobe/bcrypt_reach.spl`, using the FIXED input `[0,1,…,15]` — no randomness is
involved, so any difference between lanes is a miscompile, not entropy:

| check | interpreter | JIT |
|-------|-------------|-----|
| `bcrypt_encode_base64([0..15])` | `..CA.uOD/eaGAOmJB.yMBu` | `..eOEA.mKBf.QD/WWEfuc.` |
| `encode_salt([0..15], 10)` | `..CA.uOD/eaGAOmJB.yMBu` | `..eOEA.mKBf.QD/WWEfuc.` |
| `bcrypt_decode_base64 ∘ bcrypt_encode_base64` | `0,1,2,…,15` (identity) | `0,8,16,24,…,120` (each ×8) |

The roundtrip is **not an identity** under the JIT: the recovered bytes are
`0,8,16,…,120`, i.e. the input scaled by 8.

Note this last row describes *what was measured*, not a mechanism. It is the composition
`decode ∘ encode` where **encode is already corrupted**, and `bcrypt_decode_base64` reads
its own input via the same defective path — so the ×8 that lands at the end is the
product of two affected stages, not a single clean shift applied to the input. Do not
quote it as "decode shifts by 3".

Source pin: `src/lib/common/bcrypt/salt.spl` blob
`9aebf245c612c6e1865fb874aaad1b656306f752`, byte-identical to `origin/main` at the time
of measurement.

## What this is NOT

This is **not** a regression in `c4f186314c4` ("bcrypt salt and TLS server_random used
seeded LCGs, not the CSPRNG"). That fix **holds**: `generate_random_bytes` now returns
genuinely varying bytes per call and never the old constant-seeded LCG output
`126,223,44,245`. Verified on both interpreter and JIT (`.nvprobe/gate_a.spl`).

The defect is downstream — the *encoding* of the correctly-generated salt bytes. Keep
the two entries separate; merging them would make it look as though the CSPRNG fix
failed, which it did not.

## Blast radius

Any caller that encodes a salt through these functions on the JIT lane gets a salt
string that does not correspond to its bytes, and cannot be recovered by
`bcrypt_decode_base64`. `encode_salt` is reached from `bcrypt/hash.spl`
(`use std.bcrypt.salt.{bcrypt_encode_base64, encode_salt, generate_salt}`).

## Attribution — MEASURED: seed-JIT only, pure-Simple codegen is CLEAN

The discriminating question — *does pure-Simple codegen share the `list<T>` param
defect?* — is answered only by `native-build` with a **bare positional** `.spl`, which
is the only form that reaches the pure-Simple `CompilerDriver` (an explicit `--entry`
delegates back to the Rust runtime and proves nothing about the self-hosted lane).

`.nvprobe/scope_id.spl` was built that way (`RC=0`, 30,168-byte binary) and run:

| param annotation | interpreter | **native (pure-Simple codegen)** | seed JIT |
|------------------|-------------|----------------------------------|----------|
| `data: list` | 8 | **8 — correct** | 64 BROKEN |
| `data: list<i64>` | 8 | **8 — correct** | 64 BROKEN |
| `data: [i64]` | 8 | **8 — correct** | 8 |

**The tagged-element defect is confined to the Rust seed's JIT codegen. The
pure-Simple native codegen — the deliverable — is correct on every spelling.**

Under the standing "rust is seed; pure-Simple must be implemented, verified and used"
rule this is therefore a **disposable-seed defect**: recorded, not chased. It still
matters operationally, because `bin/simple run` is the seed and is what most sessions
actually execute — anyone reading bcrypt salt output from that lane is reading corrupt
bytes.

**Correction to an earlier draft of this doc:** it stated that the native builds "did
not complete" under load. That was wrong and is retracted — `scope_id` completed in
roughly seven minutes at load ~60–92 with ~21 competing `native-build` processes.
Native-build is slow here, not broken, exactly as `a9c8effc054` concluded when it
refuted the earlier "total native-build outage" report. Slowness was mistaken for
failure once in this session; that is the same error the outage report made.

## Engine identity was established by capability probe

Not by mtime or size, both of which provably lie in this repo.
`.nvprobe/engine_id.spl` reproduces the open tagged-element defect on the default lane
(`via_param=64`) and not under `SIMPLE_EXECUTION_MODE=interpret` (`via_param=8`),
proving the default lane really is the JIT rather than a silent interpreter fallback.
