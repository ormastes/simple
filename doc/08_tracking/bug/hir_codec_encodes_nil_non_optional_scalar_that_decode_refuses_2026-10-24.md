# HIR codec encodes a nil non-optional scalar that its own decoder refuses

- **Date:** 2026-10-24
- **Status:** OPEN — the asymmetry is established from source; that this module
  hits it is NOT established
- **Files:** `src/compiler/20.hir/hir_codec_support.spl`,
  `src/compiler/20.hir/generated/hir_codec.spl`,
  `src/compiler/80.driver/driver_hir_cache.spl`,
  `src/app/compiler_schema/codec_gen.spl`
- **Context:** explains the `reason=decode` / `RT-E-HIR-BLOB-DECODE` refusal that
  precedes (and is NOT the cause of) the Stage 2 `stage2_module_path_naming`
  SIGSEGV tracked in
  `cranelift_cmov_memory_operand_unconditional_load_2026-10-23.md`

## The asymmetry

For a **non-optional** scalar slot holding nil:

- **The encoder writes a nil sentinel and reports success.**
  `hir_codec_support.spl:373` (bool), `:380` (i64), `:399-401` (text) emit `N`
  (or `\N` for text) and leave `w.ok` **true**.
- **The decoder refuses that exact byte.** The generated decoders reject it as
  `nil_in_non_optional_scalar` — **231 sites**, e.g.
  `generated/hir_codec.spl:166-172`.

So a module carrying a single nil in a non-optional scalar field **encodes
cleanly and can never be decoded**. The round-trip is not symmetric, and the
encode side is the one that is wrong: it produces a blob its own reader is
designed to reject.

Consequence: the cache refuses that module forever — every build pays full
lowering, and the refusal is reported as a cache-health statistic rather than as
the codec defect it is.

## `reason=unstable` vs `reason=decode` — same predicate, different sampling

Both are store-side, in `driver_hir_cache.spl`:

| reason | site | predicate |
|---|---|---|
| `decode bytes=N` | `hir_cache_selfcheck_blob` `:624-631` | `hir_module_decode(blob) == nil` |
| `reencode line=… field=…` | same | decode OK but `hir_module_encode(decoded) != blob` |
| `unstable` | the `elif` at `:467-471` | `hir_module_decode_stable(blob) == nil` |

`hir_module_decode_stable` is confirmed as decode + full re-encode + byte compare
(`hir_codec.spl:555-561`). So `unstable` **collapses both failure kinds into one
word**; the detailed form is printed only when `_hir_cache_selfcheck_due()`
(`:605-612`) fires — mode `all`, or every `HIR_CACHE_SELFCHECK_SAMPLE`-th module
under `SIMPLE_BOOTSTRAP`. The ordinary message therefore hides which half failed.

## Measured: it is the DECODE step

Re-running the Stage 2 repro with `SIMPLE_HIR_CACHE_SELFCHECK=1`:

```
SELFCHECK FAILED … reason=decode bytes=69622
```

A re-encode mismatch would have printed `reason=reencode`. Independently,
`RT-E-HIR-BLOB-DECODE` is emitted only where `hir_module_decode(blob)` is nil
(`rt_criticality_validation.spl:878, 893-895`); the re-encode mismatch has its
own distinct code `RT-E-HIR-BLOB-NONCANONICAL` (`:880-882`). Two independent
lines of evidence, same conclusion.

**Blob size differs by lane:** 69,622 bytes on a plain `native-build` vs 129,346
in the bootstrap (`--entry-closure` / `SIMPLE_BOOTSTRAP`). Inferred that the env
switches change the lowered HIR; **why is not established**.

## Which decode check fails is NOT established — and cannot currently be printed

`hir_module_decode` returns a bare nil on three conditions:
`representation_declarations` non-empty (`hir_codec.spl:544`), `not r.ok`
(`:546`), or a trailing-position mismatch (`:548`). None is distinguished at the
call site.

**The information exists and is thrown away.** The reader already records
`failure_detail` (`flat_pool_codec.spl:203-206`), but nothing prints it, and the
bounded decoder that would surface it is gated off by
`hir_canonical_codec_generated_available_v1()` returning a literal `false`
(`hir_codec.spl:~75`). That is a diagnostic gap, not a missing capability, and
it is why this took a measurement rather than a read.

## `rejected=decode:0` beside a decode refusal is consistent, just badly named

`rejected[]` counts **load** rejections only: `_hir_cache_reject` `:361-366`
increments `misses` plus one class — `absent` at `:256-257` (no entry file),
`decode` at `:276-278` (an existing entry failed to decode). A **store**-side
refusal increments `_hir_cache_refused` instead (`_hir_cache_refuse` `:522-524`)
and never touches `rejected[]`. Summary at `:697`.

So the line

```
refused=1 reason=unstable … rejected=absent:1,header:0,checksum:0,framing:0,decode:0
```

is self-consistent — `absent:1` because there was no entry to load, `decode:0`
because no *loaded* entry failed — but it reads as a contradiction. Worth
renaming one of the two `decode` counters.

## Why the 12 KB source yields a ~70-129 KB blob

`stage2_module_path_naming.spl` is 235 lines: five functions with multi-line
docstrings, deep nested `while`/`if` with long boolean chains, one non-ASCII
literal (`café`, `:235`). **Not measured** — no blob reaches disk, because the
store refuses before writing (`:467-471`), and none of the 411 on-disk entries
is this module.

Inferred from the codec: every `HirExpr` writes kind + `has_type_` + an optional
`HirType` (itself kind + `Span`) + a `Span` as 3 i64 lines
(`generated/hir_codec.spl:2705-2740`, `6943-6964`, `8237-8249`). So per-subexpression
type-and-span overhead dominates, not the docstrings (~2 KB).

## Explicitly not claimed

- That this asymmetry is what fails for `stage2_module_path_naming`. The
  decode-step attribution is measured; **which** check inside decode fails is
  not, so the nil-scalar path is a candidate, not a conclusion.
- That the codec cannot represent something in this module. No known-good
  round-trip exists for it to compare against: no on-disk blob, and no spec
  lowers a real source file through the codec
  (`test/01_unit/compiler/hir/hir_codec_stable_cache_frame_spec.spl` uses
  synthetic fixtures).
- Optional payloads are **not** the asymmetry. A `hc_dec_*` called after
  `next_i64() == 1` can return nil (34 `return nil` sites; 33 calls to
  `hc_restore_enum_nil`, which returns nil on `not r.ok` or `Err` —
  `hir_codec_support.spl:569, 574, 576, 582`), but every such path first sets
  `r.ok = false`, so the nil cannot escape a decode that reports success
  (`hir_codec.spl:546`). That half is sound; only the scalar half is not.

## Suggested order of work

1. Decide which side is authoritative for a nil non-optional scalar. Refusing at
   **encode** (as `w.reject`) makes the blob never exist and reports the real
   defect at its source; the decoder's refusal already exists and is correct.
2. Ungate the bounded decoder's `failure_detail`, or print it from the legacy
   path, so `reason=decode` names its check instead of requiring gdb.
3. Split `reason=unstable` into `decode` / `reencode` at the ordinary call site
   rather than only under the sampling knob.
4. Rename one of the two `decode` counters so a store refusal and a load
   rejection are not reported with the same word.
