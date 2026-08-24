# `E-HIR-BLOCK-VALUE-TYPE-DECAYED` / `cannot convert object to int` blocks native-build of `io_runtime`

**Status:** Open — FOURTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 30.hir / 35.semantics (block tail expression type capture)

## Position in the chain

`use std.nogc_sync_mut.io_runtime` has now shed three blockers:

1. seed-interpreter expression-position `if val` binding gap — FIXED `9e3eb1adccd`
2. Return borrow-check false positive on `Ref`-containing functions — FIXED `9e3eb1adccd`
3. `E-BACKEND-LLVM-INST-ResultMatchSemantic` — FIXED in `838f5e2e08c` (see
   `llvm_backend_no_result_match_semantic_2026-08-24.md`); that signature is
   now measured at **0 occurrences**, down from 7.

This is what is underneath. It is a **distinct** defect, not a recurrence.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`,
`BUILD_RC=0`). Exit code read DIRECTLY into a variable on the line after the
command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 1200 "$SEED" native-build control.spl -o control.bin > fix.log 2>&1
$ NB_RC=$?
NB_RC=1
$ grep -c ResultMatchSemantic fix.log
0
```

## Verbatim error

```text
error: semantic: type mismatch: cannot convert object to int
E-HIR-BLOCK-VALUE-TYPE-DECAYED: block tail expression type_ word became a
non-well-formed heap reference between capture and HirBlock construction;
substituting a placeholder
error: native-build worker exited with code 1.
```

The `E-HIR-BLOCK-VALUE-TYPE-DECAYED` line repeats many times; the
`cannot convert object to int` errors appear to be the downstream consequence
of the substituted placeholder type.

## Why this looks like the 2026-08-24 defect family

Same family as `7d657439fa8`, `c3c4357063e`, `eaac3400b86`, `51a7b28e220`: a
type word crossing a boundary and being **lost or replaced**, with the
consequence surfacing far from the cause. The diagnostic text is unusually
specific and self-aware — it says the type word "became a non-well-formed heap
reference **between capture and HirBlock construction**", i.e. the producer
already knows the value decayed in transit and chooses to substitute a
placeholder rather than fail. That substitution is what turns a type-word
lifetime bug into a misleading `object to int` mismatch downstream.

Suggested first measurement: find the emitter of
`E-HIR-BLOCK-VALUE-TYPE-DECAYED` and log the *pre-decay* type word plus the
span, so the failing block tail can be localized. The placeholder substitution
should probably be a hard error under a debug env flag, the same way
`SIMPLE_DEBUG_UNDEFINED_VAR=1` made the previous blocker localizable.

## Not this defect

Two further independent MIR-lowering gaps, measured on the same pass:

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`
