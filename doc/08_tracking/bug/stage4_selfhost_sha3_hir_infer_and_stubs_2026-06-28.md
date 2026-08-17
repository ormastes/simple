# Pure-Simple deploy blocked: stage3 self-host fail + stage4 sha3 hir infer + 574 stubs

Date: 2026-06-28
Status: open
Severity: high

## Summary

Deploying the self-hosted pure-Simple compiler as `bin/simple` (to replace the
Rust seed) is blocked. A `--pure-simple` bootstrap from a working seed produces
a **silent no-op** stage4 binary, so `bin/simple` must stay on the seed.

This matters because the Rust seed is the only build that emits the
`Avoid 'export use *'` parser warning (1,576 sites repo-wide) and the
`Use 'val'/'var'` info notes; the pure-Simple parser emits neither. Deploying
pure-Simple would clear all of them with zero source churn — but only if it works.

## Evidence (2026-06-28)

`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple`:
- **Stage 3 self-host fails (exit 1)** → falls back to the seed for stage 4.
- **Stage 4** (seed → full CLI `main.spl`): `804 compiled, 1 failed`, then
  **"Generating 574 stub functions for unresolved symbols"** (Array, Dict,
  alloc, *ParserModule, common__crypto__sha3__sha3_256_bytes, …).
- Resulting `build/bootstrap/full/x86_64-unknown-linux-gnu/simple` (25 MB):
  `-c "print(1+1)"` → **0 bytes output** (expected `2`); `run` and `lint`
  likewise produce nothing. Silent no-op — the 574 stubs gut the entry paths.

## Concrete leaf bug (actionable)

The 1 hard compile failure is a HIR element-type inference bug:

```
src/lib/common/crypto/sha3.spl: hir: Cannot infer element type for index into
'empty tuple while lowering sha3_update: receiver=Identifier("ctx"), index=Integer(0)'
```

`sha3_update` indexes `ctx[0]` where `ctx`'s type lowers to an empty tuple, so
the seed's HIR can't infer the element type. Fixing this removes the 1 failed
file; the 574 unresolved-symbol stubs (cross-module resolution gap) and the
stage3 self-host failure remain the larger blockers.

## Not done

`bin/simple` left on the working Rust seed (verified: prints `2`). No deploy.
Related: long-standing stage3 self-host break; 574-stub cross-module gap.

---

## Re-investigation 2026-08-17 (worker W7) — the leaf bug is NOT what was filed

Binary for every number below: `bin/release/x86_64-unknown-linux-gnu/simple`
(the Rust seed; `readlink -f bin/simple` confirms). No bootstrap was run.

### The HIR "empty tuple" error did not reproduce

`sha3_update`'s `ctx[0]`/`ctx[3]` tuple indexing lowers cleanly now: the whole
module compiles and executes through the Cranelift JIT (`bin/simple run`), and
a minimal `fn take(ctx: (list, list, i64, i64))` probe reads indices 0/2/3
correctly on BOTH engines. The `Cannot infer element type for index into
'empty tuple'` diagnostic could not be produced. The native-build lowering
behind the original stage-4 message is not reachable from this seed
(`simple build native` -> `unknown build subcommand`), so that half stays
**BLOCKED-NEEDS-BOOTSTRAP**; the tuple-index claim is retired.

### What IS live: SHA-3 is wrong under the JIT, and the KAT spec cannot see it

`test/01_unit/lib/common/crypto/sha3_kat_spec.spl` is green
(`Results: 7 total, 7 passed, 0 failed`) — but `test` is the tree-walk
interpreter and `run` is the JIT, so the suite never touched the engine real
programs run on.

| SHA3-256 input | interpreter | JIT |
|---|---|---|
| `""` | `a7ffc6f8…` (FIPS 202, exact) | `c0e8cca8…` WRONG |
| `"abc"` | `3a985da7…` (FIPS 202, exact) | `6061633038…` WRONG |

SHA3-512("abc") under the JIT begins with SHA3-256("abc")'s exact 32 bytes —
structurally impossible for two different rates, and the tell that the state
arithmetic, not the plumbing, is broken.

### Root cause, minimally isolated — the 61-bit boxed-int family

The JIT boxes an integer as `value << 3 | 3-bit tag`, leaving a 61-bit payload.
A computed `i64` is destroyed the moment its magnitude reaches 2^60:

| expression | interpreter | JIT |
|---|---|---|
| 2^60 | `1152921504606846976` | `-1152921504606846976` (payload sign bit) |
| 2^61 | `2305843009213693952` | `0` |
| 2^62 | `4611686018427387904` | `0` |
| 2^63 | `-9223372036854775808` | `0` |

**Threshold: |v| >= 2^60 (1152921504606846976).** Keccak-f[1600] lanes are full
64-bit, so every SHA-3 digest computed under the JIT is corrupt. This is the
same defect family the briefing names as the root of three other bug docs, and
it explains this row without any tuple/HIR involvement.

`src/lib/common/crypto/sha3.spl` is **correct** and needs no change.

### Fence shipped (deliberately RED)

- `test/01_unit/lib/common/crypto/sha3_jit_engine_divergence_spec.spl` —
  shells out with `SIMPLE_EXECUTION_MODE=jit|interpreter` (a spec body cannot
  reach the JIT) and asserts the FIPS 202 vectors plus the 2^60..2^63 ladder.
  `Results: 3 total, 0 passed, 3 failed` — a correct spec asserting behaviour
  the implementation lacks, left RED per `.claude/rules/testing.md`.
- `test/01_unit/lib/common/crypto/_sha3_jit_probe.spl` — the subprocess body.

**Unblock condition:** widen the JIT's integer representation (or unbox i64) in
`src/compiler_rust/**`. Out of this lane's file ownership — **BLOCKED-CROSS-OWNER**.
