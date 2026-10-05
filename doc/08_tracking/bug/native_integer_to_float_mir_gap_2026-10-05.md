# Native integer to_float has no MIR conversion arm

Status: focused repair qualified by an actual Phase2-produced LLVM executable,
13 checks passed. This numeric fixture has not been qualified on Cranelift.

The repaired Phase 2 compiler
`edcd1f43720d11aa611f8b1868e35809e78bf0c6de64781891293ad76d0f4eb7`
passed the canonical Hello gate and advanced the small DB import through
13-module parsing/HIR. Its native build then failed with exit 1 at MIR:
`unresolved method call: to_float` in `src/lib/nogc_sync_mut/db/accel.spl:130:19`.
The density implementation calls `self.count().to_float()` and
`self.row_count.to_float()`, both integer-to-f64 conversions.

The interpreter defines integer `to_float` and `to_f64` as aliases
(`interpreter_method/primitives.rs:31`). Existing MIR numeric lowering emits
a real Cast for `to_f64`/`to_f32`; the text-specific `to_float` repair in
`9c517cc79a5` intentionally excluded numeric receivers and documented the gap.
Neither it nor the earlier numeric-conversion commit `3fec678b29a` fixes this
alias. That was the source state at the original diagnosis.

The repair admits `to_float` only after existing primitive type recovery
identifies an integer, excluding declared Any and custom owners, then shares
the existing f64 Cast emission. Text parsing keeps its earlier dedicated
dispatch. No library call is rewritten to avoid the compiler defect.

`test/04_smoke/numeric_to_float_native.spl` checks zero, positive and negative
integers, exact values near 2^53, nearest-even rounding beyond it, signed i64
bounds, a typed function result, and existing text parsing. Its expected
values are explicit f64 literals. The original attempted run exposed a separate
bootstrap float-literal/type-transport defect; that failure was retained rather
than weakening these assertions. The unchanged fixture now compiles and runs.

## Executed evidence

Producer SHA256:
`744f90c14a63c1b9bc819f225ba800392e2b2493a480371db40a5923b21085e8`.
The parent qualified this Phase2 compiler with two Hello checks on each of LLVM
and Cranelift. Numeric evidence here is **LLVM only**: build exit0, run exit0,
`NUMERIC_TO_FLOAT_NATIVE_PASS checks=13`.

Retained evidence directory:
`/var/tmp/simple-item5-phase2-20261005/build/item5-hosted-numeric/`.

| Artifact | SHA256 |
| --- | --- |
| Produced `probe` executable | `97d31475718717c5394dc52468197f7c400584b26c35e112a05a305bc595a816` |
| Unchanged numeric fixture | `88e804e5420c5966be27740a1f09f7a691f6cd0fdef9a3a8cb69fb5ab1a283a7` |
| Tested `method_calls_literals.spl` | `73842e5f0f0a179628af7d97bcdc4c43b71ffb415ed9cee6c9e562004fbdc7ce` |
| `build.log` | `b1ae4e1762f74e70460aa41177f551d2121ebe0a1d17d5fa75c7c51831303335` |
| `run.log` | `f2fda6d68bc2d025d5c4bda9f7ad601726e507d0e4dbd1766211fc9348ebcc4e` |
| `status.txt` | `df0b86fd7130623d359c205c1bd0cdab9c551ecdcebc3b30bc83bbb0ff7ac4bf` |

Packaging on release `7b529f345df2a89f9b391efd774e846895b1e8d7` preserves
the exact tested owner and fixture bytes. The already-green native run was
not repeated. The producer includes other independently owned repairs; this
change packages only the numeric alias, fixture and this evidence record.

Separate failures recorded during the original diagnosis: retained FixedVec helper bodies in `simd_scan.spl`
have unresolved `cmp_eq`, `all`, `any`, and `lane_active`; the full DB/web
probe also exited 139 during MIR. Neither deleting unused helper bodies nor
changing scalar dispatch is part of this repair. It does not qualify DB/web,
SIMD execution, performance, or full bootstrap.
