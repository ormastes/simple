# Native codegen: `if val x = <cross-module Optional<struct>>` loses the struct type and resolves `.field` by NAME

- **Found:** 2026-09-12, bootstrap lane `work/bootstrap-2026-09-12`
- **Severity:** silent wrong value (no diagnostic, no crash). Blocked Stage 2 admission.
- **Scope:** native codegen only. The interpreter is correct.

## Symptom

`--stop-after-stage2` failed at the Stage-2 sanity smoke with

```
native-capsule-receipt-invalid:scripts.check.cert.redeploy_gate.fixtures.hello_world:
  receipt-content-mismatch:expected-bytes=1572:actual-bytes=1572
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Equal byte counts, unequal content — the verdict localised nothing.

## Root cause (measured, not inferred)

`FileFingerprint` (`src/compiler/80.driver/driver_build/incremental.spl:615`) is
`path, content_hash, modified_time, size` — `size` is field **3** (offset 24).

`driver_aot_native_output.spl` read it as

```
val object_fp = FileFingerprint.from_file(capsule.object_path)
if val fp = object_fp:
    expected = "...\n{fp.size}\n{fp.content_hash}\n"
```

Disassembly of the rejected Stage-2 binary
(`build/bootstrap-2/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
`driver_native_capsule_result_reason_v1` at `0x37eb7c8`):

```
37ebac4:  and x21, x20, #0xfffffffffffffff8   ; untag the unwrapped payload
37ebacc:  ldr x8, [x21]                       ; OFFSET 0  <-- `{fp.size}`
37ebad4:  bl  rt_raw_i64_to_string
...
37ebb04:  ldr x1, [x21, #8]                   ; OFFSET 8  <-- `{fp.content_hash}` (correct)
```

`{fp.size}` reads **offset 0**, i.e. the `path` text POINTER, and renders it as
a decimal. `FileFingerprint.from_file` itself is CORRECT (`0x37ff52c`: it stores
`rt_file_size`'s return into offset 24). The defect is entirely at the read site.

Offset 0 is where the *first* `size` field registered in the build lives (e.g.
`TypeLayout.size`, `src/compiler/30.types/_TypeLayout/layout_core.spl:193`), so
the access was resolved by field NAME against a global index instead of by the
receiver's type. `content_hash` collides with nothing, which is why only the
size was wrong.

Observed values for an **1080-byte** object: `732750049`, `383756385`,
`920329169` — heap addresses, non-deterministic, all 9 digits. Both the writer
(`:2223`) and the verifier (`:888`) used the same shape, so both rendered 9
digits and the byte counts matched while the content did not. That is the whole
of `expected-bytes=1572:actual-bytes=1572`.

## Minimal native reproduction

Two modules; the reader imports the struct plus any other struct whose first
field is named `size`:

```
# fpmod.spl
pub struct FileFingerprint: path: text; content_hash: text; modified_time: i64; size: i64
impl FileFingerprint: static fn from_file(path: text) -> FileFingerprint?: ...

# other.spl
pub struct TypeLayout: size: i64; align: i64; name: text

# main.spl
val opt = FileFingerprint.from_file(p)
if val fp = opt:                     print("RED  {fp.size}")   # 920329169
if not opt.?: return
val fpg: FileFingerprint = opt!;     print("GREEN {fpg.size}") # 1080
```

Measured in ONE binary (aarch64, `--backend llvm --mode dynload`, seed
`src/compiler_rust/target/bootstrap/simple`):

```
tl.size=7
RED  unwrapped.size=920329169
GREEN typed.size=1080
```

Narrowing, same binary:

| shape | result |
| --- | --- |
| `TypeLayout(...)` local, `.size` | 7 — correct |
| `FileFingerprint(...)` constructed locally, `.size` | 1080 — correct |
| `Some(local_struct)` then `if val` | 1080 — correct |
| `val u: FileFingerprint = opt!` (annotated) | 1080 — correct |
| `if val fp = <Optional returned by a cross-module fn>` | **garbage** |

So the trigger is the *cross-module* Optional return: the struct type is lost
across it, and only then does `.field` fall back to a by-name index. Without a
second `size`-bearing struct the by-name index happens to be the right one, so
the bug hides.

## Current state

NOT fixed in the compiler. Worked around at the two blocking sites in
`src/compiler/80.driver/driver_aot_native_output.spl` (`:901`, `:2263`) by
binding with an explicit type annotation — `val fp: FileFingerprint = object_fp!`
— with a comment at each site. Both sites are guarded by a preceding
`if not object_fp.?:` early return, so the `!` cannot fail.

The real fix belongs in the compiler: either preserve the struct type across a
cross-module `Optional<T>` return, or make a type-less field access a hard
semantic error instead of silently indexing by name. This is the same fail-open
family as `unregistered_extern_silent_nil_2026-08-01.md` and the
`compiler_cross_module_private_symbol_collision` warning the build already
prints for functions — but for STRUCT FIELDS, where nothing warns at all.

## Related, found while diagnosing (not fixed)

1. `FileFingerprint.from_file` (`incremental.spl:632-645`) picks the hash
   ALGORITHM by whether the text read succeeds: a sha256 hex on the binary
   branch, a decimal `rt_hash_text` i64 on the text branch. Evidenced here: the
   SAME `.o` hashed sha256 inside the Stage-2 binary and `rt_hash_text` in a
   standalone native probe. For object files it should call
   `rt_file_hash_sha256` unconditionally. Changing it changes receipt content,
   so it was left alone in this lane.
2. `driver_materialize_phase2_native_v1` (`:501-506`) writes the receipt's size
   from `published.content.len()` while every other site uses
   `FileFingerprint.from_file` (`rt_file_size`). A genuine writer/verifier
   asymmetry, but latent: it needs `SIMPLE_PHASE2_COMPATIBILITY_MANIFEST_READ`,
   which `bootstrap_stage_sanity` scrubs, so it is NOT the cause of this
   failure.
3. `rt_file_size` is declared `-> i64` in six modules and `-> usize?` in
   `src/compiler/80.driver/cache/gc/admission.spl:12` and
   `.../gc/fast_gc.spl:14`. Neither module is in the Stage-2 entry closure
   (verified by `nm`), so it is not implicated here, but the two declarations
   are inconsistent.

## Why the `!` at the two patched sites is safe

Both are preceded by `if not object_fp.?:` early returns. The `.?` test does not
need the payload type — the disassembly shows it routed through `rt_is_some`
(`0x37eba30`), and the probe table above shows `val u: FileFingerprint = opt!`
returning the correct 1080 in the same binary that got 920329169 from the
`if val` form. So the guard is sound and the annotated bind is exact.

The annotation is load-bearing **because the seed is the compiler that builds
Stage 2**. Once a self-hosted compiler builds Stage 2 the failure mode may
differ; the workaround should be revisited then, not assumed permanent.

## Blast radius

Every `if val x = <cross-module Optional<struct>>` followed by `x.field` in the
Stage-2 closure is one field-name collision away from a silent misread. The
build already prints `compiler_cross_module_private_symbol_collision` warnings
for FUNCTIONS with clashing signatures; there is no equivalent warning for
STRUCT FIELDS, and no runtime check — the wrong word is simply read.

Recommended compiler fix, in order:
1. preserve the payload type through a cross-module `Optional<T>` return, so the
   field access is resolved by type as it is everywhere else;
2. until (1) lands, make a type-less `.field` access a hard semantic error
   rather than a by-name index — the same rule
   `unregistered_extern_silent_nil_2026-08-01.md` established for externs.

Audited in `driver_aot_native_output.spl` (2026-09-12): the other `if val`
bindings over cross-module optionals (`:996` `source_fp_val`, `:1960` `src_fp`,
`:1514`/`:1518`/`:2303` `session`, `:2392` `obj_bytes`) either pass the struct
whole or read only text-typed members, so none of them renders a numeric field
into an identity string. Only the two receipt sites were exposed.
