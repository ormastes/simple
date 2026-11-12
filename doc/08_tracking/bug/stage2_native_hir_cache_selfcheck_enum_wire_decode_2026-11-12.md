# Stage 2 native HIR cache selfcheck fails to decode its own entry (enum wire allocation)

**Status:** OPEN (observed 2026-11-12, aarch64, Linux; lane bootstrap-fable-8/9/10)
**Area:** compiler / HIR cache codec under pure-Simple native codegen

## Symptom

While the Stage 2 (pure-Simple, cranelift) compiler builds the admission
fixture `src/compiler/bootstrap_admission/stage2_module_path_naming.spl`:

```
[hir-cache] SELFCHECK FAILED module=<snapshot>/src/compiler/bootstrap_admission/stage2_module_path_naming.spl
  path=<same> reason=decode bytes=259591 cause=reader kind=malformed
  detail=enum wire enum allocation failed line=3569/19823 token=0; entry not stored
```

(`src/compiler/80.driver/driver_hir_cache.spl:764`). The build continues —
the selfcheck refuses to store the entry, so the module is lowered again by
the main build — but every module that trips it loses HIR cache reuse. The
same message appeared on runs 8, 9 and 10 for this fixture; it is not known
how many of the 1,634 Stage 2 closure modules trip it.

## Why it matters

Stage 3 and the Phase 2 matrix tool builds rely on the HIR cache for warm
reuse; a codec that cannot round-trip its own encoding on the native lane
silently turns every build cold. Decoding fails at a fixed line/token of a
259,591-byte entry, which points at a specific enum wire shape (an enum with
payload inside the HIR of this fixture) rather than I/O.

## Reproduce

Any Stage 2 native-build of the fixture logs the line, e.g. the
run-10 admission smoke: `stage2-sanity.env.frontend-failure.log` of
`build/bootstrap-fable-10` under the lane's pinned snapshot, or the direct
replay in this lane's probe script (`probe_fixtures.sh`).

## Unanswered

- Which HIR node at line 3569 of the encoded entry carries the enum whose
  wire payload cannot be allocated, and whether the seed-built encoder or the
  native decoder is wrong (compare the seed interpreter's decode of the same
  bytes).
- Whether the matrix's `hir-cache` hit counters (`[hir-cache] hits=… refused=…`)
  show the same refusal class across the closure.

## Root cause located 2026-11-12 (lane fable-bug-hircache-20261112; fix identified, withheld)

Reproduced in 9 s on aarch64 Linux with the admitted Stage 2
(`build/bootstrap-fable-13/stage2/aarch64-unknown-linux-gnu/simple`, pinned
f8ad54b28467): `SIMPLE_HIR_CACHE_SELFCHECK=1 native-build
src/compiler/bootstrap_admission/stage2_module_path_naming.spl --backend=cranelift
--threads 1` -> `SELFCHECK FAILED ... reason=decode bytes=117902 ... detail=enum wire
enum allocation failed line=5151/22676 token=0`. The blob was quarantined with
`SIMPLE_HIR_CACHE_FAILED_DIAGNOSTIC_DIR`.

**Node.** Blob line 5151 is `\N` directly after tag `37`:
`HirExprKind.Break(label: text, value: HirExpr?)` — an unlabeled `break` encodes
its non-optional `label` as the nil word. The generated decoder
(`src/compiler/20.hir/generated/hir_codec.spl`, `if tag == 37`) builds
`HirExprKind.Break("", f_value)` and calls `hc_restore_enum_nil(r, proto, 2, [0])`
-> `enum_wire_restore_nil` (`src/lib/nogc_sync_mut/sffi/enum_wire.spl`).
Any module containing an unlabeled `break` (or any other nil-encoded
non-optional scalar) is affected; this is not Stage-2-specific.

**Not a native-only decoder fault.** The Rust seed (`run` engine) fails to decode the
same bytes at the same line. An isolated probe (`enum_wire_restore_nil(Pair("", None),
2, [0])` and `(One(""), 1, [0])`) returns `Err("enum wire enum allocation failed")` on
the seed `run` engine and in a Stage-2-built native binary alike; `[]` (no nil slot)
is `Ok`.

**Root cause.** `enum_wire.spl:12` declares
`extern fn rt_enum_new(enum_id: i32, discriminant: i32, payload: i64) -> i64`
(the `@workaround bug=rti007_any_return_rows_2026-11-01` from `99a45712909`, which
replaced `rt_enum_new<T>(..) -> T`), and `enum_wire.spl:106` assigns that i64 to
`val restored: T`. Exactly the contract break the RTI-007 record already corrected
for `rt_tuple_get` ("the runtime returns an already-tagged value; integer boxing
between that i64 declaration and the generic wrapper corrupts aggregate handles"):
`rt_enum_id(restored)` reads -1 and the function refuses its own result.

**Candidate fix (3 lines, verified partially; NOT landed):**
```
-# @workaround bug=rti007_any_return_rows_2026-11-01 ...
-extern fn rt_enum_new(enum_id: i32, discriminant: i32, payload: i64) -> i64
+extern fn rt_enum_new<T>(enum_id: i32, discriminant: i32, payload: i64) -> T
-        val restored: T = rt_enum_new(owner as i32, variant as i32, payload)
+        val restored: T = rt_enum_new<T>(owner as i32, variant as i32, payload)
```
With it: seed `run` decodes the quarantined blob (`hir_module_decode` -> Some, path
correct); the isolated probe is `Ok` with the right identity on the seed `run` engine
and in a Stage-2-built native binary. Why it is withheld:
1. **Native generic-return wrap.** In a Stage-2-built binary the handle survives a
   plain `-> T` return (`direct id=25684258 len=2`) but is destroyed when returned
   through `Result<T, text>.Ok(restored)` (`result id=-1 len=-1`); after
   `enum_wire_restore_nil` returns, `rt_enum_id`/`rt_enum_payload` on the value give
   -1/nil and `enum_wire_nil_slot` says `enum wire invalid enum`, although `match`
   still destructures it (`bits=64`). A re-encode of such a node cannot see its nil
   slot, so sampled/forced selfcheck would still refuse the entry, and an adopted
   node is a silent-wrong-value risk. Owner: native lowering of a generic `T` payload
   into `Result`/`Option` (`src/compiler/50.mir`), same family as RTI-007's tuple note.
2. **Seed `run` smoke crashes further on.** `test/04_smoke/enum_wire_boundary_native.spl`
   (instrumented) fails at its 13th `require` before the fix (the `Err` arm); with the
   fix it proceeds to `require` 32 and then SIGSEGVs (rc 139) on the seed `run` engine.
   Natively (Stage 2 build) it still fails at `require` 13 with the fix because the
   restored payload carrier is observed as an array (`rt_tuple_len == -1`) while the
   prototype's is a tuple (len 2) — the item-1 degradation seen through `rt_enum_payload`.
3. **Seed `test` lane has no `rt_enum_new` at all.** `simple test` on the Rust seed
   reports `semantic: unknown extern function: rt_enum_new` for every spelling
   (`-> i64`, `-> T`, `-> T?`, with/without `<T>` at the call) and
   `type mismatch: cannot convert string to int` when `rt_tuple_set(value: i64)`
   receives a text word. `interpreter_extern/mod.rs` registers `rt_enum_id`/
   `rt_enum_discriminant`/`rt_enum_payload` (373-375) and `rt_tuple_new`/`rt_tuple_set`/
   `rt_tuple_get` (846-849) but no `rt_enum_new`; the interpreter's `Value::Enum` is
   name-based, so backing it needs an id -> enum-name mapping.

**Red witness committed:** `test/01_unit/lib/sffi/enum_wire_restore_nil_spec.spl`
(3 examples: 1 pass / 2 fail at the release tip; stays red until all three items
above are fixed; do not weaken it).

**Probe limits recorded.** A Stage-2 native-build of a probe importing
`compiler.hir.hir_codec` aborted the compiler with
`E-BACKEND-CRANELIFT-CALL-ABI: compiler.hir.hir_codec_support.HirCodecWriter.put_f64:
callee signature unknown; arg 1 is f64 and cannot be passed through the all-i64 import`
(rc 134), so the HIR-level native decode could not be exercised outside the compiler
itself. `hir_module_decode_stable` cannot be driven from a standalone `run` script
either: the encoder rejects the decoded module with `unregistered HirModule node`
(`rt_heap_ref_registered`), independent of this bug.

**Relation to `hir_cache_never_hits_header_rejected_2026_10_26`:** different class.
That bug was the cache key/header identity (verified fixed 2026-11-12: repeat build
hits, two targets write two keys). This one is the HIR codec's enum wire restore;
with the key/header fixed it is now the reason some Stage 3 modules stay cold.
