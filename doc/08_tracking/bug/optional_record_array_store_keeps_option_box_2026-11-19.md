# A `T?` record stored into a `[T]` array keeps the Option box (Stage 3 SIGSEGV in the HIR codec)

- **Date:** 2026-11-19
- **Status:** crash site already fixed in source (`0483fdd22ed`, `630291ab3b9`, both after
  the crashing binary's pin); lowering fixed in source here (MIR-level proof on the seed
  interpreter; native proof needs a new Stage 2)
- **Lane:** Stage 2 (seed-built, cranelift) -> Stage 3, aarch64 Linux
- **Source pin of the crashing Stage 3:** release/1.0.0 `9f89b7d0b55`
- **Not** `stage3_array_copy_unique_static_leaf_2026-11-19.md` (PR #10298): no method
  dispatch is involved; the value is boxed and stored exactly as written.

## Symptom

Stage 3 dies with SIGSEGV on any native-build that stores a HIR-cache entry, including a
two-line hello world (about one second):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 SIMPLE_FILE_WORKERS=0 \
  stage3 native-build main.spl --backend=cranelift --entry-closure --cache-dir c -o out
```

```
#0 compiler.hir.generated.hir_codec._hc_enc_hir_block_body
#1 compiler.hir.generated.hir_codec.hc_enc_hir_block
#2 compiler.hir.generated.hir_codec._hc_enc_hir_function_body
#6 compiler.hir.hir_codec.hir_module_encode
#7 compiler.driver.driver_hir_cache.hir_cache_selfcheck_blob
#10 compiler.driver.driver_hir_cache.hir_cache_store
```

With `SIMPLE_HIR_CACHE=0` the same binary finishes HIR, MIR and borrow check.

The Stage 3 self-build (14 MIR shard workers, every one `status=CRASH exit=-139`, in MIR
lowering or as its HIR phase started) is attributed to the same defect by inference only:
the coordinator stored 471 HIR blobs (the selfcheck is sampled, so it survived) and the
workers consume decoded HIR. No worker backtrace was taken.

## Root cause

`hir_cache_selfcheck_blob` decodes the blob it just wrote and encodes it again. The
generated decoder at the pin was

```
var ev0: HirStmt? = None
if r.next_i64() == 1:
    ev0 = hc_dec_hir_stmt(r)
f_stmts.push(ev0)                 # f_stmts: [HirStmt]
```

On the pure-Simple native lane a `T?` local assigned from a `-> T` producer holds the
canonical Option box (`rt_enum_new(1, 0, record)`). Declared-`T` call arguments, struct
fields, typed bindings and returns unwrap it; the two array element stores did not:

- `xs.push(v)`: `lower_unresolved_array_push`,
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
- `xs[i] = v`: the `Index` arm of `lower_assign`, `src/compiler/50.mir/mir_lowering_stmts.spl`

Both hand the local to `box_runtime_value`, which passes a runtime-value handle through
unchanged, so the BOX became the element. gdb on the crash: the faulting element is
`kind=4 (enum) enum_id=1 discriminant=0 payload=<HirStmt>`, created by `rt_enum_new`
called from `hc_dec_hir_block+1872`; the encoder's `for e0 in node.stmts` copied it as a
`HirStmt`, took the box's discriminant word for `span` and dereferenced it.

## Fix

- `option_record_element_payload_v1` (array-store twin of
  `option_record_argument_payload_v1`): when the receiver's declared element is
  `Named(S)` and the value's optional payload is the same `S`, the stored value goes
  through `rt_unwrap_or_self`. A `[T?]` receiver, a plain record and a different record
  are untouched; a None stores nil, as the interpreter does. One HIR-type lookup per
  push / index store, no extra pass.
- The crash site needs no new workaround: the generated decoder on the release tip
  already pushes `if val present = ev0` (`0483fdd22ed`) and that shape compiles correctly
  on the 24941411f54 Stage 2 (checked with the tip-shaped variant of the fixture).

## Evidence

- Spec `test/01_unit/compiler/mir/optional_record_array_store_unwrap_spec.spl`: 2 of 3
  without the lowering change, 3 of 3 with it (seed built from `24941411f549`).
  `optional_record_argument_unwrap_spec.spl` stays 3 of 3.
- Fixture `test/fixtures/native_optional_record_array_store/main.spl`: the seed
  interpreter prints the expected 8 lines; the Stage 2 binaries built from `9f89b7d0b55`
  and `24941411f54` print `3`, a garbage `4`, then SIGSEGV (cranelift and llvm alike).

## Not proven

- No native proof of the lowering change: that needs a Stage 2 built from it.
- Receivers with no remembered declared HIR type (for example a struct-field array,
  `self.items.push(v)`) are not covered by this change and were not measured.
- Other source sites storing a `T?` record into a `[T]` were only searched heuristically
  (none found outside the already-fixed generated codec).
- That the self-build worker crashes are this defect (inferred, see Symptom), and that
  the self-build has no second, independent crash after it.
