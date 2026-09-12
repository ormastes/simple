# Pure-Simple deploy blocked: stage3 self-host fail + stage4 sha3 hir infer + 574 stubs

Date: 2026-06-28
Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
