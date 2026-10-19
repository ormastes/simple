# Primitive Char UTF8 storage: current gap and ordered compatibility plan

Status: researched against immutable release `e09fb99f62cf69987d2b7ced7e3cabb643987531`; no compiler/build/test execution. Physical UTF8 Char remains **NOT IMPLEMENTED / NOT QUALIFIED** on this release. The defensive direct-Char C ABI refusal accompanying this document is only a prerequisite.

## Approved meaning and physical contract

The selected [UTF8/SOSIX plan](../../03_plan/utf8_internal_sosix_plan.md) requires ordinary internal UTF8 Char/Text and conversion at SOSIX. Its statement that a character represents one Unicode scalar describes meaning, not permission to retain scalar-integer storage indefinitely. No new grammar, alternate language character type, or redefinition of that requirement is proposed.

Reuse the previously reviewed `char-utf8-inline32-v1` contract: one canonical UTF8 scalar encoded into a four-byte integer carrier, first UTF8 byte in bits 0..7, remaining high bytes zero, width derived from the first byte. NUL is valid carrier zero, not absence. Invalid helper result -1 stays outside valid zero-extended u32 carriers; Option presence is independent. Examples: A=0x41, cent=0xA2C2, euro=0xAC82E2, grinning face=0x80989FF0. High-bit carriers require unsigned extension. Scalar comparison, numeric conversion and code-point hash must decode first; raw little-endian packed integer ordering is wrong (U+00BF vs U+00C0).

This is a fixed-size UTF8 carrier, not a claim that generic `[char]` packs into four bytes per element. Current generic runtime arrays may retain eight-byte value slots. Managed text remains a length-aware UTF8 byte buffer; no need to store text as a character array.

## Exact current-state evidence

| Surface | Current source fact | Remaining gate |
|---|---|---|
| Foundation | `external_text.spl:7` aliases Char to primitive char. ExternalChar validates one scalar and returns `scalar as char` at :258. Strict UTF8/16 codecs and sessions are landed. | Semantic conversion alone proves no primitive physical layout. |
| MIR literal | `_MirLoweringExpr/expr_dispatch.spl:6274` refuses CharLit with E-MIR-EXPR-CharLit. Prior char_cast/storage helper owners are absent. | Port coherent literal/cast lowering, not a helper-only done mark. |
| MIR layout | `mir_types.spl:253` reports Char size2 with I16/U16; `verification_ir.spl:349` labels it unicode-scalar:u32. | Reconcile actual four-byte representation and verification oracle together. |
| Backend | LLVM mapper :147 omits Char from primitive dispatch; shared C mapper originally :19 returns int16_t; Cranelift adapter has mixed unsigned Char handling. | Explicit Char type/size/alignment/load/store/extension across actual backends; unsupported targets refuse. |
| Interpreter/JIT | `jit_interpreter.spl:253` sends Char as Unicode scalar i64, :283 reconstructs from code point after execute. | Typed interpreter carrier adaptation and provider admission before execute; no guessed JIT ABI. |
| Pure runtime text | `core_string.spl:646/665/682` retains managed bytes/length. `rt_string_chars` :781 builds arrays of one-character text handles; :826 is a scalar-codepoint indexing boundary. | Preserve these current consumer contracts until separately migrated; changing them to raw Char words would break text/lexer callers. |
| Existing caches | Pure text indexing has four fixed cursor entries (:316); chars conversion has a 256-entry local ASCII handle table (:794), freed at :817. | These are not external encoding caches or evidence for physical Char; preserve current fixes. |
| Hash | `nogc_sync_mut/src/hash.spl:127` hashes `char.to_u32()` as a code point. | Keep public hash meaning; numeric method must decode carrier before hashing; execute actual map/hash callers. |
| Identity | `20.hir/abi_interface.spl:92` emits bare char identity without a representation tag. Driver incremental owner already carries other runtime/compiler identity. | Change Char ABI/semantics identity in the same activation, reject stale objects/interfaces/cache entries without deleting caches. |

The old frozen packet index is `robust-tdd-20261014/char-utf8-physical-storage-20261018/inline32-composition-status.json`. It is a source design/review reuse map, not proof of current integration. Its old attempt and provider states are historical; no new attempt budget is created here. Existing root campaign accounting remains authoritative.

## Direct C ABI truncation witness and safe prerequisite

A valid U+1F600 scalar is 128512; a 16-bit carrier retains only 0xF600=62976, and signed int16_t would interpret that pattern as -2560 on a two's-complement ABI. U+10FFFF similarly reduces to 0xFFFF. Even a future packed UTF8 value 0x80989FF0 cannot fit int16_t. These are source/range witnesses, not executed C calls. The canonical scalar validator admits these code points and rejects surrogate U+D800.

Actual consumers reach `c_abi_map_type`: C backend `plugins/backend_c/c_type_mapper.spl:69`, C header parameter/return adapters `90.tools/header_gen/c_header.spl:174/185`, and C++ equivalents :129/140. The mapper's direct Char arm now refuses with E-CHAR-FOREIGN-ABI instead of spelling int16_t. Explicit I16/U16/U32 ABI choices remain unchanged. No implicit scalar adapter, uint32_t substitution, primitive layout change, cache-version bump or runtime mutation is included.

This narrow check does not inspect nested pointer/callback/container/nominal signatures that can erase to void*. It is not full foreign-Char safety. Prior recursive foreign gate and exact selected-header-surface packets are needed during coherent storage activation. Opaque handles remain valid; do not reject all pointers or invent imports by name.

## Ordered implementation and qualification

1. **Reuse representation primitives and actual acceptance oracles.** Port reviewed inline32-final helper with strict canonical byte validation, NUL, full scalar range and no allocation. Rebase source tests/fixtures to current APIs. A helper-only pass does not satisfy primitive storage.
2. **Compose MIR semantics and identity atomically.** Literal encoding; integer/text-to-Char checked conversions; Char-to-int/float/text decode; width and invalid handling; default zero; optional presence; equality and scalar ordering; numeric methods/hash. Apply pattern lowering for nested/top-level/or/guard Char literals. Preserve current enum/Result/field-owner fixes. Version typed interfaces, compiler semantics and relevant object/cache identities before accepting any new carrier object.
3. **Compose backends and runtime transport before activation.** MIR Char size/alignment4 and explicit LLVM/Cranelift/native handling; arrays, records, enums, calls/returns, globals, boxing and Option layout. Pure-Simple runtime carrier/tag pathways must be qualified independently of hosted C. Existing text chars/index APIs keep their contract until their real callers migrate. Do not combine old scalar objects with new packed Char code.
4. **Compose interpreter and foreign boundaries.** Typed literal, casts, methods, comparisons and map/hash execution; reject unsupported JIT provider metadata before execute. Add recursive actual foreign declarations/C exports/header-selected methods/types checks, preserving opaque handles. Host conversion uses explicit scalar integer or versioned UTF8 bytes; no raw Char ABI inferred from an i32 register.
5. **Use the admitted existing qualification path, only when root authorizes.** Run real frontend→HIR→MIR/backend API specs and retained native fixtures on a producer containing the coherent implementation. Capture actual producer/runtime/source identity and incompatible-cache rejection. Do not use the old producer's success for scalar Char to prove new representation; no seed fallback, new runner, cache cleanup, or retries are authorized by this plan.
6. **Then migrate remaining ordinary host callers and measure.** Verify file/network/tool SOSIX ingress/egress and actual internal operations, preserving raw bytes and explicit format paths. Current codecs/session routes remain prerequisites rather than completion proof. Measure allocations/RSS/latency/throughput with identical workload/provider controls.

## Actual test prerequisites and gaps

Reuse prior fixtures `native_char_utf8_physical`, `native_char_utf8_absent_order`, `native_char_numeric_methods`, float-cast fixture and `native_utf8_char_storage`; rebind current compiler imports/constructors before execution. Required outcomes include boundary scalars, malformed/padded/noncanonical carriers, zero/high-bit words, every 1–4-byte width, exact emitted constants, scalar-order inversions, NUL vs nil, optional comparisons, signed/unsigned integer and float conversions, text roundtrips, nested/or/guard patterns, actual hash/Dict callers, call/return and nested record/array/enum layout. Verify memory bytes with actual native storage/FFI adapters, not semantic roundtrips alone. Include direct/recursive FFI refusal and admitted explicit scalar/u8 positive controls; assert exact diagnostic plus failing status, never any failure.

The current prerequisite extends `test/01_unit/compiler/backend/c_abi_type_mapping_spec.spl` and adds three actual negative API fixtures under `test/fixtures/compiler/char_c_abi_refusal`: direct shared mapper and both actual header emitters. They remain UNRUN. They do not test physical Char, nested foreign paths or complete compiler admission.

## Encoding-cache decision

No new output encoding cache is needed for correctness or presently justified by measurements. Do not add one. If profiling later demonstrates repeated per-character output conversion dominates, its approved design must key the Unicode scalar/representation version plus encoding, byte order and BOM policy, distinguish stream-start state from content, cap both entries and allocated bytes, and use deterministic eviction/reset with no global cross-session mutable codec. Existing text cursor/ASCII tables are unrelated and stay unchanged. Claim only measured benefit; logical constant state is not total RSS, lifetime or concurrency proof.

## Final state after this prerequisite

Landed source: strict codecs/foundation, immutable selected-encoding config, owning network sessions and ordinary UTF8 routing (separate file/tool lane status remains root-owned). This packet: source-linked physical-storage plan and direct C Char rejection only. Remaining requested primitive UTF8 representation, coherent compiler/runtime ABI, actual native/interpreter/FFI tests and memory/performance acceptance all stay OPEN. A defensive refusal is not feature completion.
