# Native MIR layout lookup recovery

The native MIR verifier rejected valid struct field access when independently
boxed `SymbolId(700)` values identified the same layout. A debugger inspection
confirmed that the module contained the definition, but native dictionary lookup
used different boxed addresses for the stored and requested keys. The verifier
reported `MIRV-006b` instead of resolving the owner.

## Repair

Build a `Dict<i64, MirTypeDef>` from the module's type definitions once per
`mir_verify_module` invocation. Struct field checks, enum cache construction,
and uncached enum checks use the semantic `SymbolId.id`. Standalone
`mir_verify_function` retains its public signature and builds its own module
index. MIR's existing owner invariant is that a module type key and the stored
definition's `symbol` identify the same owner.

The enum slot cache must check membership before reading its scalar value.
Native bootstrap lowering eagerly unboxed an absent `Dict<i64, i64>` lookup:
the tagged Nil value became integer 3, which was mistaken for a populated
cache slot. Both the original `?? -2` expression and an explicitly annotated
`i64?` binding exhibited this defect. Disassembly showed `rt_index_get`,
`rt_unbox_int`, and `rt_box_int` before the nil comparison. A `has` guard
preserves cached slot 0, positive slots, and the cached unresolved value -1
without reading an absent scalar entry.

This repair preserves the verifier's diagnostics and public call surfaces. Its
module setup costs O(type definitions); owner lookup costs O(1). It does not
change generic boxed-key hashing or scalar optional-index lowering elsewhere.
Those remain compiler/runtime defects demonstrated by the frozen producer.

## Regression

`test/fixtures/compiler/native_mir_layout_lookup/main.spl` is a native
executable regression. A zero exit requires successful valid struct access,
rejection of invalid and missing layouts, cached and uncached enum validation,
standalone-function validation, and an empty-module check. Each failure has a
distinct nonzero exit code. Separate boxes at layout insertion and use retain
the original failure trigger.

## Bootstrap route

The frozen Phase-1 producer is
`96b223750119a95a4f0582076285de13888f3ebc77e99ca5a6f4996553a9cd07`.
Bootstrap-only native validation explicitly sets `SIMPLE_NATIVE_BUILD_RUST=1`
and `SIMPLE_NO_STUB_FALLBACK=1`. Ordinary commands continue to use the
self-hosted compiler.

Earlier attempts without the explicit bootstrap route entered the interpreted
native-build coordinator and failed with `cannot iterate over this type: Nil`
before native compilation. That coordinator failure was not localized to the
MIR index and is not claimed fixed by this change. The supported explicit
bootstrap route compiled and linked the focused fixture successfully.

## Qualification limits

Focused Phase-1 interpreter and actual native fixture evidence qualify this
repair. They do not constitute whole Phase-1/2/3 testing, Phase-4 object/link
verification, full bootstrap completion, or item-2 database acceptance.
The shared installed self-hosted runtime has a checksum/receipt mismatch, so
broader runtime/compiler/lib/MCP qualification remains unavailable here.

The release-line verifier owner is absent from the fetched `origin/main`
snapshot `bba9b0989488a37e9b7ab983ae3b2eba640f6229`. This change repairs that
release-line component; applying its lookup delta to main would require adding
the verifier feature first.
