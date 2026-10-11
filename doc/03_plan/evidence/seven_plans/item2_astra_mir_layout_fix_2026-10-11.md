# Item 2 — Astra native MIR layout fix

Status: focused bootstrap regression PASS; whole bootstrap and item-2 acceptance
remain incomplete. The user requested “fix with astra and land the fix”.

## Scope and review

Authored in the isolated `work/astra-mir-layout-fix-20261011` worktree from
`origin/release/1.0` at `26589b27e60d613605f75d395cd0334870801015`.
Only the MIR verifier, its native regression fixture, and repair evidence are
included. The original item-2 worktree's 157 staged paths are excluded.

Astra (`gpt-6-astra`, high effort) localized the native failures, implemented
the enum membership guard, expanded the native fixture, and reviewed the final
source hashes. The root agent reviewed the exact diff and focused test evidence.
Both reviews found no P0/P1 issue in the narrow repair.

## Final source and producer bindings

| Input | SHA-256 |
|---|---|
| Frozen Phase-1 compiler | `96b223750119a95a4f0582076285de13888f3ebc77e99ca5a6f4996553a9cd07` |
| `src/compiler/50.mir/mir_verify.spl` | `ffbe3b1cf9f4fc2dffd894da91c0af462482f4528cd1e241a4e2e4425a5fdef2` |
| Native fixture source | `3c04464dfe5b8af347945e6360e5e0c9c9579c4e15dcb7e6268c2e664071a4a1` |
| Native fixture executable | `7250c32ebae5cbc9e8f23cf666cba69e4a6bd916730bab17bc74960e6473fb1a` |

## Executed checks

- Final focused Phase-1 interpreter suite:
  `mir_verify_cfg_layout_spec.spl` reported
  `Results: 19 total, 19 passed, 0 failed`, exit 0, 4.64 seconds.
  The verifier source hash stayed unchanged throughout the run.
- Final native compilation reused 105 objects and rebuilt 2, linked the
  executable, and returned build exit 0. The resulting executable returned 0
  after all 11 exit-coded checks, including repeated enum cache hits for slots
  0 and -1. Native build elapsed 4.22 seconds.
- Working and staged direct-env runtime guards: PASS. No env/process APIs were
  introduced. The staged whitespace check passed and `doc/06_spec` contained
  zero executable `*_spec.spl` files.

Local machine receipts:

- `build/test-artifacts/astra-mir-layout-fix-20261011/phase1-mir-layout-final.json`
- `build/test-artifacts/astra-mir-layout-20261011/native-regression-cycle3.json`
- `build/test-artifacts/astra-mir-layout-20261011/native-build-cycle3.log`
- `build/test-artifacts/astra-mir-layout-20261011/enum-cache-miss.log`
- `build/test-artifacts/astra-mir-layout-20261011/enum-slot-cycle2-disasm.log`

The first expanded native fixture linked but exited 4 on valid cached enum
construction. The second, explicitly typed optional binding still exited 4.
Debugger inspection proved eager scalar lookup unboxing before the nil check.
The third used a dictionary membership guard and passed. This was a bounded
three-cycle repair of a newly observed native enum defect; no passing native
check was rerun afterward.

## Reproduction

Use the admitted immutable Phase-1 producer and runtime bundle for bootstrap
validation. The following environment is bootstrap-only:

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_INCREMENTAL=1 \
  "$PHASE1_COMPILER" native-build --backend cranelift \
  --runtime-bundle core-c-bootstrap --runtime-path "$BOOTSTRAP_RUNTIME" \
  --source src/compiler --source src/lib \
  --source test/fixtures/compiler/native_mir_layout_lookup --entry-closure \
  --entry test/fixtures/compiler/native_mir_layout_lookup/main.spl \
  --threads 2 --cache-dir "$OWNED_PRODUCER_CACHE" --output "$NATIVE_FIXTURE"
"$NATIVE_FIXTURE"
```

An exit of 0 is required from both commands. Preserve the producer-bound cache
and reject stub fallback. Ordinary application tooling uses the self-hosted
runtime, not this bootstrap producer.

## Remaining qualification

This repair handles verifier layout identity and enum-cache absence. It does
not globally repair native boxed-key hashing or scalar optional-index lowering.
The interpreted coordinator's unlocalized Nil iteration failure remains open.
Whole Phase-1/2/3 testing, Phase-4 compilation/linking, and full bootstrap are
not marked complete. The installed self-hosted runtime's checksum/receipt
mismatch prevents broader compiler/lib/MCP runtime qualification in this lane.

The fetched main snapshot lacks this release-line MIR verifier owner, so an
automatic lookup-only forward port is inapplicable until that feature exists.
