# gzip_decompress returned [] for valid input: `data?` on a plain [u8] (2026-11-28)

Found by `test/01_unit/compiler/common/di_spec.spl` "gzip compression roundtrip"
(failing-tests batch 5).

**Defect.** `gzip_header_parse_at(data: [u8]?, base)` in
`src/lib/nogc_sync_mut/compression/gzip/header.spl` bound its input with
`val input = data?`. Every in-tree caller (`decompress.spl`, and through it
`std.common.compress.gzip.gzip_decompress`) passes a non-optional `[u8]`; the
interpreter rejects that with `? operator requires Result or Option type, got
array`, so `gzip_decompress` failed for every input and the common facade
fell back to `[]`. The sibling helpers in the same file (`gzip_footer_parse`,
`gzip_footer_validate`, `lz77_compress`) already used `match data: case
Some(..) / case None`, which accepts the plain array.

**Fix.** `gzip_header_parse_at` now uses the same `match` binding.
`gzip_footer_parse`'s `case None: return nil` became `return None` (None-not-nil
policy).

**Language/runtime gap (addressed by the seed call-boundary wrap below).** A non-optional value passed to
an `T?` parameter is not wrapped at the call boundary for the `?` operator,
while `match ... case Some(x)` accepts it. The two forms should agree; until they
do, `param?` on an `T?` parameter is unsafe in library code. Separately, the
runner attributed the error to the spec's path with the library's line number
(`di_spec.spl:70:5`; the `?` is at `header.spl:70`), which hid the real site.

**Tests.** Repro + prevention:
`test/01_unit/lib/nogc_sync_mut/compression/gzip_header_plain_array_arg_spec.spl`
(5 examples: plain-array header parse at offset 0 and at a member offset, None
argument, owner + facade decode, facade round trip). It fails 4/5 on the
unfixed code and passes 5/5 after the fix.

Status: verification-pending (interpreter on the Windows seed; native
not re-run).

## Same batch: @lazy_proxy desugar never generated a proxy

`desugar_lazy_proxies` (`src/app/desugar/lazy_proxy_gen.spl`) recorded each
`# @lazy_proxy("svc")` + `trait` pair as `ProxyAnnotation(service_name:,
trait_name:, line_index:)` without `is_valid`, which defaulted to `false`; the
second pass then gated on `find_annotation(...).is_valid` and silently emitted
nothing. Fixed by setting `is_valid: true`. Repro/prevention: the restored
`test/01_unit/compiler/di/di_proxy_spec.spl` (5/10 fail before, 10/10 after).
The missing field compiled under the current "infer missing -> default" rule;
robust mode would have rejected it.

## Follow-up: seed call-boundary `T -> T?` wrap, scalar payloads (2026-11-28)

Decision: wrap at the call boundary, not make `?` lenient, and only where
native wraps. MIR boxes a plain argument for a `T?` parameter or field only
when the payload is scalar (`src/compiler/50.mir/mir_lowering_stmts.spl`
Optional arm, `scalar_payload` -> `ensure_option_handle`; same for fields).
A heap `T?` (array, text, record) is natively the same raw nullable pointer as
`T`, and library code relies on that (`gzip_decompress` iterates a `[u8]?`
struct field directly). A first, universal wrap broke exactly that
(`di_spec` gzip roundtrip: "cannot iterate over Option"), so the seed
(`interpreter_call/core/arg_binding.rs` `wrap_plain_into_optional_param`) now
wraps scalar payloads only (int widths, f32/f64, bool, char). `?` stays strict
on genuine non-Options; `nil` stays nil; `any?` is untouched. Struct
construction goes through the same binder, matching MIR's field rule.
Repro: `test/01_unit/compiler/try_op_optional_param_implicit_some_spec.spl`.

Open (owner decision): `data?` on a heap `[u8]?` parameter that received a
plain array is still rejected by the seed, while native compiles it as a null
check. Options: (i) let `?` accept a raw non-nil heap value (matches native; precedent: the seed matcher
`interpreter_patterns.rs` ~620 already lets `case Some(x)` bind a raw value), or (ii) keep
`?` strict and keep the `match` idiom in the library, guarded by
`scripts/check/check-optional-param-try.shs` (empty baseline). Chosen: (ii) (coordinator, 2026-11-28).

Open item: seed and native still differ on `param?` for array, text and
record `T?` parameters that receive a plain value (native: null check, seed:
"? operator requires Result or Option type"). Library code uses `match` there.
Status: verification-pending.
