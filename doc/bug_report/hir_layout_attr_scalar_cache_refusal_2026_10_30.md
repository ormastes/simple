# LayoutAttr scalar producers prevent HIR cache publication

Status: source fix prepared; runtime validation pending. Live Phase3 source was not changed.

## Observed evidence

Source: `b81f148624f8c39dac0b3f865a8270472dd9fbbd`.
Producer SHA256: `76c04806d8321705424b7ebbf11ddfbe5726771ad4033696d4b308c24e8d33fd`.
Runtime archive SHA256: `5d7399d0c9c6b906b2981028c15185829ab35c960042bffb9d41e358ef8820e8`.
Windows GNU Phase3 attempt2 stderr:
`C:/dev/simple-mono-expected-result-20261029/build/bootstrap/phase3-diagnostic-b81f148-attempt2-20261030/stderr.log`.

First representative refusal, line58944:

```text
[hir-cache-store] refused reason=decode detail=reader kind=malformed detail=nil_in_non_optional_scalar:LayoutAttr.has_explicit_align line=11759/11916 token=N module=src/compiler/00.common/diagnostics/span.spl; entry not stored (further decode refusals are only counted)
```

The next two workers reported the same required-field failure for
`src/app/cli/native_build_mir_selective_admission.spl` and
`src/lib/common/io/types.spl`. Three shard summaries recorded 762 cache hits,
842 misses and 842 store refusals, with zero stores. Their `lowered=0` counter
counts successful new cache publication, not all actual HIR lowering work.
This prevents newly computed HIR from being reused by subsequent compilation.
It does not establish why the earlier attempt1 process exited.

## Cause and repair

`LayoutAttr` uses required `has_explicit_align: bool` and `explicit_align: i64`
fields. `parse_layout_attrs` still constructed the former optional representation:
it omitted the presence field and supplied `Some(value)` or `nil` as the scalar
value. The default, C-repr and packed factories omitted both fields.
The generated codec correctly refused the resulting required-field nil token.

Initialize the pair explicitly in all four owned production producers. The
parser preserves its existing power-of-two validation: 1 and16 are valid;
0 and3 leave the flag false and payload0. The generated decoder and cache
publication checks remain unchanged. No cache version change is needed: valid
wire layout is unchanged, and malformed entries were never published.

## Focused validation for Luna

Run with a hash-admitted full CLI and the repaired source closure:

```text
<admitted-full-cli> test test/01_unit/compiler/hir/layout_attr_scalar_codec_spec.spl --no-session-daemon --mode=interpreter
```

The five cases exercise the real generated LayoutAttr codec from the parser
and all three factories, assert exact scalar values and byte-stable reencoding,
and require rejection of malformed nil presence/value fields. Runtime execution
has not occurred. Compiler cache behavior must subsequently be checked with a
producer rebuilt from this fix; the old frozen producer embeds the old parser
and factories, so merely rerunning its build would not test the repair.
