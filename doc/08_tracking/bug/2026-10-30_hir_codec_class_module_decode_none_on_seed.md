# HIR codec: decoding a module that declares a class returns None on the seed

- Status: OPEN (not root-caused)
- Component: `src/compiler/20.hir/generated/hir_codec.spl` (`hir_module_decode`), Rust seed interpreter
- Found while converting `hir_codec_dict_decode_not_nil_spec` to a behaviour spec (PR #5333 review, finding 4)

## Symptom

On the Rust seed, `hir_module_decode(hir_module_encode(m)).unwrap()` fails with
`called unwrap on None` when `m` is lowered from

```
class Counter:
    value: i64
```

(with or without methods). Modules with only functions round-trip (see
`hir_codec_dict_decode_roundtrip_spec.spl`, 3/3). Not yet checked on a
self-hosted binary, so it may be a seed interpreter gap rather than a codec bug.

## Unblock

Reproduce on a Stage 2 binary; if it also fails, bisect `hc_dec_hir_class`
(hir_codec.spl ~1918). Then add a class-module round-trip case on a native/stage2
lane. `hir_codec_dict_decode_not_nil_spec.spl` stays a source check: on the seed a
`T?` stored into `Dict<K,T>` reads back transparently, so a seed behaviour spec
cannot catch the e606125a541 regression.
