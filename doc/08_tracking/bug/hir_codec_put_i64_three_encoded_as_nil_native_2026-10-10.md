# HIR codec writes integer 3 and bool true as nil under a stage-2 compiler

**Status:** source fix landed on `work/rel-frontend-parallel-20261010`; NOT yet
verified on a rebuilt stage-2 (see "Still to verify").
**Engines:** staged-native (stage 2 and later). The seed interpreter is not
affected, which is why every interpreted codec spec stayed green.
**Host:** Windows, frozen stage 2 `simple-bootstrap 1.0.0-rc.1`
(sha256 `49cbd0052706c055…`), tree `6b540f21546`.

## Symptom

The HIR cache never hits under a stage-2 compiler, so the HIR phase is always
re-lowered serially and every HIR shard's work is thrown away.

- Phase-3 build, 1163 modules: `[hir-cache] hits=0 misses=1163 stores=1133`.
  HIR took 2278 s of a 2818 s front end (parse 333 s).
- 38-module fixture, same command run twice against one cache directory:
  `[hir-cache] hits=0 misses=38 stores=38` both times, 38 entries on disk with
  unchanged names.
- Same fixture through the sharding coordinator with `--threads 4`: the four
  HIR shards reported `lowered=10/8/5/15` (all 38), then the real worker
  reported `[hir-cache] hits=0 misses=38 stores=38`. The parse shards on the
  same run did work: `[frontend-cache] hits=38 misses=0`.
- `SIMPLE_HIR_CODEC_ROUNDTRIP=1` on the fixture entry:
  `HIRROUNDTRIP ok=false stable=false bytes=6119 reason=decode` and
  ``error: hir codec: no `SymbolKind` arm for tag 1448``.

## Root cause

`HirCodecWriter.put_i64` and `put_bool`
(`src/compiler/20.hir/hir_codec_support.spl`) decided whether to write the nil
marker `N` with `v == nil` on a slot statically typed `i64` / `bool`. Under
staged-native codegen that comparison is against nil's immediate:

- it is true for the integer **3**, so every 3 was written as `N` — a count of
  three, symbol id 3, `next_scope_id == 3`, and the literal tag of the fourth
  variant of every enum. The decoder reads `N` as nil, takes a different path
  and desynchronises; the load is rejected.
- it is true for every bool **true**, so each true flag was written as `N` and
  decoded as nil. One line either way, so this half is silent.

Evidence in the stored entries: three entries of 261,898 / 121,701 / 126,515
lines contain **zero** lines equal to `3` and 1238 / 400 / 613 lines equal to
`N`. In the 6119-byte fixture entry the scopes count, the root scope's symbol
count and `next_scope_id` (all 3) are `N`.

Native proof, a standalone probe compiled by the frozen stage 2 with the old
and the new expression side by side:

```
i=3 raw_is_nil=true          # fn raw_is_nil(v: i64) -> bool: v == nil
bool f=false t=true          # fn bool_is_nil(v: bool) -> bool: v == nil
OLD=[0,1,2,N,4,5,N]          # put_i64 over 0..5 and [1,2,3].len()
NEW=[0,1,2,3,4,5,3]
BOOL_OLD=[0,N,N,0,N]         # false,true,true,false,true
BOOL_NEW=[0,1,1,0,1]
```

Payload-less enum values and `text` are not affected (`enum_is_nil` false for
all four variants, `""` is not nil), and the decoder's
`if raw == "N": nil else: …` returns the parsed value correctly.

## Fix

Both writers now discriminate on the rendered text instead of on `v == nil`:
a real nil renders as `nil`, an integer or a bool never does. The interpreted
behaviour is unchanged (nil is still written as `N`).

Pinned by `test/01_unit/compiler/hir/hir_codec_scalar_nil_collision_spec.spl`
(4 examples, interpreted).

## Still to verify

The writer change takes effect only in a stage 2 built from this source. On
that binary, before trusting a warm HIR cache:

1. `SIMPLE_HIR_CODEC_ROUNDTRIP=1` on a small closure must print
   `HIRROUNDTRIP ok=true stable=true` for every module.
2. Running the same build twice against one cache must report `hits == modules`
   on the second run.
3. The objects of a cold build and a warm (all-hits) build must be
   byte-identical. This matters because the cache has never served a hit under
   a native compiler, so any other lossy field would first show up here.

## Related, not fixed here

- `v == nil` on an `i64`- or `bool`-typed operand is wrong under staged-native
  codegen in general; this record only removes it from the two codec writers.
  See `pure_simple_option_i64_ifval_always_some_eqnil_always_false_2026-08-08.md`.
- `bootstrap_main` sends `--entry` builds with `SIMPLE_BOOTSTRAP_STAGE3=1` or
  `SIMPLE_BOOTSTRAP_STAGE4=1` to the in-process focused capsule, which never
  enters the sharding coordinator, so `--threads` cannot affect parse or HIR on
  those lanes.
- HIR lowering cost per module grows with the closure: 0.30 s/module at 38
  modules, 1.96 s/module at 1163.
