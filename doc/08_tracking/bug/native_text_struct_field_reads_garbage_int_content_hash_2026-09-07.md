# `text` struct field reads as garbage int under native codegen — root cause NOT where predecessor localized it

**Status: OPEN — investigation, not fixed.** A predecessor localized this to
`resolve_global_field_info` (`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:89`)
picking the wrong struct's field type across an ambiguous global field-name
scan. Direct instrumentation below shows that mechanism does **not** fire for
this reproducer at all — the field's type is resolved correctly at every
layer that was traced. The corruption source is still unknown; do not re-apply
the predecessor's fix location without new evidence.

## Symptom (reproduced, 2026-09-07)

```
use compiler.driver.driver_build.incremental.{FileFingerprint}

fn takes_text(t: text) -> text:
    "GOT:" + t

fn main():
    val object_fp = FileFingerprint.from_file("<path>")
    if val fp = object_fp:
        print(fp.path)
        print(fp.size)
        print(fp.content_hash)          # <-- wrong even WITHOUT takes_text
        print(takes_text(fp.content_hash))
```

Interpreted (`bin/simple run` equivalent, via the Rust seed hosted interpreter):
```
<path>
391
0
GOT:0
```

Natively compiled (`SIMPLE_NATIVE_BUILD_RUST=1 native-build --backend cranelift`,
`SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` for unrelated unbacked runtime stubs):
```
<path>
422
5064169361185293926     <- garbage, non-deterministic across rebuilds
GOT:5064169361185293926
```

`fp.path` and `fp.size` are correct in both modes. `fp.content_hash` (a `text`
field) is wrong **even as a bare `print(fp.content_hash)`**, before any `+`
concatenation or call — this rules out a `+`/text-coercion-specific bug inside
`takes_text`. The value differs between rebuilds (5064169361185293926 vs
3991975224931997820 on a second run), consistent with an uninitialized/raw
pointer bit pattern being printed as a decimal integer rather than dereferenced
as a string.

## What the predecessor found (still true, but not the cause of THIS symptom)

`FileFingerprint` (`src/compiler/80.driver/driver_build/incremental.spl:342`,
`path`@0:text, `content_hash`@1:text, `modified_time`@2:i64, `size`@3:i64) is
one of several structs that also declare a field literally named
`content_hash` as `i64`: `FileHash` (`80.driver/incremental.spl:16`, idx1
count3), `SmfDependencyEntry` (`80.driver/smf_writer.spl:79`, idx1 count2),
`ModuleSurface` (`hir_lowering/module_surface_types.spl:378`, idx11),
`CacheEntry` (`monomorphize/cache.spl:102`, idx3), `SourceInfo`
(`80.driver/incremental_builder.spl:34`, idx1 **count7** — the only one that
can out-rank `FileFingerprint` on the documented smallest-index/largest-count
tie-break), and `_BgImageCacheEntry`
(`src/os/compositor/background_image_provider.spl:188`, **idx0** — beats
`FileFingerprint` outright on index alone). `resolve_global_field_info`
(type_resolver.rs:89) and the ANY-branch "LOCAL-BEST" scans in
`get_field_info` (same file) are receiver-blind: they pick the
smallest-index/largest-count struct across ALL known structs declaring a field
NAME, ignoring which struct the receiver actually is. This mechanism is real
and independently reproducible (see the `BgLike`/idx0 experiment below), but
it is not what fires in the `FileFingerprint.content_hash` reproducer above.

## Direct instrumentation (this session, reverted before commit)

Added a debug print (`SIMPLE_DEBUG_FIELD_SCAN=1`) inside `get_field_info`'s
`TypeId::ANY` branch printing every candidate struct/idx/type visited when
scanning for a field name, plus a probe on the print builtin's MIR lowering
(`mir/lower/lowering_expr_builtin.rs`, "print/println... box numeric args")
printing each `HirExpr` argument's `.ty` before the `arg.ty == TypeId::I64`
special-case check. Ran the reproducer through
`SIMPLE_NATIVE_BUILD_RUST=1 native-build --source src/compiler --source src/lib
--source <repro-dir> --entry <repro-dir>/repro.spl --backend cranelift` (the
Rust seed's native_project pipeline — same `type_resolver.rs`/MIR code the
default `native-build` reaches through this env var).

Findings, in order:

1. **HIR lowering (`get_field_info`) resolves `content_hash` correctly.**
   `[SCAN-ANY] field=content_hash candidate struct=FileFingerprint idx=1
   ty=TypeId(12) count=4` is the ONLY candidate ever printed for this field in
   the whole build (searched across `repro.spl` and `incremental.spl`) —
   `FileFingerprint` is the only struct with a real (non-stub) field-name
   table registered in `self.module.types` at that point, because it is the
   only content_hash-bearing struct actually imported by name
   (`use ... .{FileFingerprint}`) into this compilation unit. `FileHash`,
   `SourceInfo`, etc. are never referenced from this file, so they never reach
   a full (non-empty-fields) registration and never compete. TypeId(12) is
   `STRING` — correct.
2. **MIR-level FieldGet codegen agrees.** `[TRACE FieldGet] ... byte_offset=8
   field_type=TypeId(12) func=main` fires twice (once per `fp.content_hash`
   use) — offset 8 is `FileFingerprint`'s real offset for field index 1, type
   STRING. This matches the predecessor's own disassembly evidence
   (`ldr x1, [x10, #8]`) — the offset fix already on `main` is holding.
3. **The print builtin's argument type is also correct.** `[PRINT-ARG]
   arg.ty=TypeId(12) arg.kind=FieldAccess { receiver: HirExpr { kind:
   Local(2), ty: TypeId(14) }, field_index: 1 }` for the bare
   `print(fp.content_hash)` call — `arg.ty` is STRING, not I64, so the
   print lowering's `arg.ty == TypeId::I64` raw-integer-formatting special
   case (`lowering_expr_builtin.rs:652`) does **not** fire. The
   `takes_text(fp.content_hash)` call site shows the same: `arg.kind=Call {
   ..., args: [HirExpr { kind: FieldAccess { ..., field_index: 1 }, ty:
   TypeId(12) }] }`.
4. **Surprising: `fp`'s own local type is concrete, not ANY, at this point**
   (`Local(2), ty: TypeId(14)`), even though step 1's HIR-lowering-time trace
   only fires from the `struct_ty == TypeId::ANY` branch of `get_field_info` —
   meaning `fp`'s receiver type WAS `TypeId::ANY` at HIR-lowering time (when
   the field access was first built) but reads as a concrete `TypeId(14)` by
   the time MIR lowering/print-argument inspection runs. This is consistent
   with a later pass (monomorphization or a narrowing fixup) assigning a
   concrete type to the `Local(2)` slot after the `if val fp = object_fp`
   unwrap, without needing to change the already-built `FieldAccess`'s
   `field_index`/`ty` (which happened to already be correct). **Not yet
   confirmed which pass does this or whether `TypeId(14)` is genuinely
   `FileFingerprint` — this is the most promising lead for a follow-up.**

Every layer traced (HIR field-type, MIR FieldGet instruction, print-builtin
argument type) agrees the field is `text`/`STRING` at the correct offset. None
of the six call sites named in the predecessor's diagnosis
(`type_resolver.rs:770,852,965,1023`, `expr/access.rs:369,404`) ever printed a
trace for `content_hash` in this reproducer — they are all guarded by
`is_ambiguous_global_field`/receiver-blind fallback paths that are only
reached when the FIRST (receiver-scoped or ANY-local) resolution fails, and it
never fails here.

## Confirmed: the ambiguous-global-field mechanism is real, just not the cause here

Extended the reproducer with a decoy struct in a separate file,
`BgLike { content_hash: i64, ... }` (mirrors `_BgImageCacheEntry`, field index
0 — beats `FpLike`'s index 1 outright). When `BgLike` is only referenced
through a function call (not `use`d as a type), it registers as an
EMPTY-fields stub in the consuming file's `self.module.types` and never
competes in the ANY-branch scan — so it does NOT reproduce the bug either.
Making `BgLike` a real competitor (full field data registered locally,
`idx=0` visible to the same scan `fp.content_hash` uses) was not reached in
the time available. This means the *precondition* for the predecessor's
mechanism (a same-name field fully registered locally with a smaller
index/larger tie-broken count) does not hold for `FileFingerprint` in either
the synthetic repro or the real `driver_native_capsule_result_invalid_reason_v1`
call site — `SourceInfo` (idx1, count7) and `_BgImageCacheEntry` (idx0) are
never imported by name into `driver_aot_native_output.spl`, so per finding 1
above they'd only ever register as empty stubs there too, not as scan
competitors.

## Suspected real cause (unconfirmed) — construction/boxing side, not field-type resolution

Since every *read*-side type/offset is correct, the corruption most likely
happens on the *write* side: inside `FileFingerprint.from_file`
(`incremental.spl:349-368`), `content_hash` is assigned from
`incremental_hash_text(content).to_text()` (a method-call chain) or
`rt_file_hash_sha256(path)` (an extern call) into a `var hash: text`, then
passed into the named-field constructor `FileFingerprint(path:, content_hash:
hash, ...)`. A follow-up should instrument struct-init field lowering
(`lower_struct_init_fields`, referenced from `expr/access.rs` comments) and
`.to_text()`'s MIR-level return-type/boxing decision the same way this session
instrumented `get_field_info` and the print builtin, to see whether the VALUE
written into the `content_hash` slot at construction time is a properly boxed
string pointer or a raw/unboxed integer. The non-determinism of the garbage
value (differs per rebuild) is consistent with an uninitialized-memory or
wrong-representation read, not a fixed wrong-struct-picked constant.

## Reproducer

Task-shape repro (needs the real `FileFingerprint`, so needs the whole
`src/compiler` + `src/lib` closure — a few seconds once cached):

```bash
SIMPLE_RUST_SEED_WARNING=0 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 \
SIMPLE_LIB=<worktree>/src \
<rust-seed-release-binary> native-build \
  --source src/compiler --source src/lib --source <repro-dir> \
  --entry <repro-dir>/repro.spl --backend cranelift \
  --cache-dir <repro-dir>/nb_cache -o <repro-dir>/repro_bin
```
(run from the worktree root; run <repro-dir>/repro_bin and compare against the
same file run through the seed's plain interpreter mode, `<seed> repro.spl`).

## Do not repeat these mistakes

- Do not assume the six candidate call sites from the predecessor's diagnosis
  fire just because the SYMPTOM (a `text` field printing as an int) matches —
  confirm with `SIMPLE_TRACE_FIELD_GET=1` before touching `type_resolver.rs`.
- A struct referenced only via a function call (not `use`d as a named type)
  registers as an EMPTY-fields stub locally; it will never compete in the
  ANY-branch "LOCAL-BEST" scan in that file, even though it resolves correctly
  by name via `try_resolve_global_field_for_struct` for its OWN direct field
  accesses. This asymmetry cost significant time to find and is worth its own
  note if `type_resolver.rs` is touched again.
