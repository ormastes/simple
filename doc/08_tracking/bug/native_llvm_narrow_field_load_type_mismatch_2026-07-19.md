# LLVM backend: narrow struct-field readback emits mistyped load → llc rejects

**Filed:** 2026-07-19 · **Status:** OPEN · **Area:** LLVM backend / struct field access
**Lane:** interpreted native-build worker (`SIMPLE_NATIVE_BUILD_WORKER=1
bin/simple run src/app/cli/native_build_worker.spl --backend llvm ...`,
llc from /opt/homebrew/opt/llvm/bin). Pre-existing; surfaced while verifying
the omitted-defaulted-field fill fix.

## Symptom
Reading back a NARROW-typed struct field (`k: i32`, `flag: bool`) loads the
64-bit slot as `i64` but then widens it assuming the narrow type, producing
ill-typed IR that llc rejects:

```
%l6 = load i64, ptr %t6      ; field slot load (i64)
%t7 = sext i32 %l6 to i64    ; llc: '%l6' defined with type 'i64' but expected 'i32'
```
bool variant: `%l12 = load i64` then `zext i1 %l12 to i64`.

Store side is fine (widened to i64 slots correctly: `zext i1 ... to i64`).
i64-typed fields round-trip cleanly.

## Repro
`struct Cfg: name: text; k: i32 = 5; flag: bool = true` + `print
"k={c.k} flag={c.flag}"`, compile via the worker lane above → llc exit 1
with the sext/zext type error. All-i64 fields → compiles.

## Expected
Either load the slot as i64 and truncate (`trunc i64 -> i32/i1`) before the
widening, or emit typed loads matching the declared field width. The
mismatch is in the field-access lowering's readback of sub-64-bit fields
(struct slots are uniformly 8 bytes).
