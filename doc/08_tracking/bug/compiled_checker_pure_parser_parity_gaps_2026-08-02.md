# Compiled checker pure-parser parity gaps

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Open, P1.  The compiled checker rejects 247 individually reproduced repository
sources that use canonical language surfaces represented in the Rust parser,
while 147 other individual failures are demonstrably invalid source and 17 are
intentional SSpec check-surface rejections.

### Type/signature lane update

Claimed by `codex/fix-signature-parser-20260802` from `34072a509817`.
The refreshed failed-only retry reduced the original route from 62 to 44
non-passing files after the generic declaration fix. The shared flat parser now
preserves canonical `mut T` annotations through `TypeKind.Reference(T, true)`
and accepts canonical empty-array annotations `[]` as `[Any]`.

Focused checker evidence (SHA-256
`563f5d66a8fb9d3cae9ef6c21f505eff144622b9883e8cf24e17caf01fd58d5d`)
proves all 11 routed `mut T` files clear their signature diagnostic and all
eight routed `[]` files clear their type diagnostic. Fourteen complete files
pass; five `[]` files proceed to unrelated later diagnostics. The two nested
multiline method signatures remain open: three bounded parser-owner probes
showed they route through the class-method parser rather than the top-level
function parser. Resume from that owner without repeating the attempted
top-level declaration changes.

### Category C declaration/import/export lane update

Claimed by `codex/parser-category-c-20260803` from `4d2762f589e`. The strict
fresh-checker retry was limited to the 43 cycle3 parser rows in keyword
identifier, keyword receiver, relative import, and structured/keyword export
routes; the checker-entry argv collision was reassigned to memory lane A.

The shared pure-Simple declaration-name helper, export parser, and top-level
plus inline relative-import consumers clear 28 files. Structured/keyword
exports fall from 17 to zero, relative import falls from one to zero, keyword
identifier falls from 21 to eight, and keyword receiver remains four. The
remaining 15 diagnostics are owned by later class, pattern, comprehension, or
primary-expression lanes, including six `static fn nil` methods, two `me fn`
methods, tuple binding, comprehension `_`, three keyword receivers, one
`while val` pattern, and one generic-call surface.

Focused exact, adjacent, and malformed-to-valid recovery coverage passes 8/8
in `test/01_unit/compiler/parser/parser_category_c_spec.spl`. Strict checker
SHA-256 is
`f2a03be721ecd28162a08187e9413356456ec644496b4ada4aa78e9c3df9d593`;
the immutable 43-path manifest digest is
`b1c9a865e8c13196821a32aaa87e9c2d212abd47e5b1cf6a3c78850b9ebd357e`.

### Core type-grammar lane claim

Claimed by `codex/stage4-type-batch-20260803` from `5e7c57e9c89a`.  The
immutable failed-only manifest contains 38 individually reproduced paths:
26 type-or-multiline-signature, nine reference-type, two fixed-array-type, and
one type-test routes.  Before editing, compiled checker SHA-256
`56ccc1509d372162c5f53a54e2fa2262afa03df52b45fe064dc250dab8f43f57`
failed all 38 paths; the manifest SHA-256 is
`e3fe4863a3e87767f1d1da1fd1dcc00dc4145548e2971aa8c17e1af47f932d4e`.

This lane owns only shared type parsing rooted in `parser_parse_type*` and its
direct type-helper splits.  Diagnostics that actually originate in class
members, primary expressions, statements, imports, structured expressions, or
lambda parsing will be rerouted rather than hidden by broad recovery.

The lane is complete.  Shared parser/type-registry/flat-bridge roots now
preserve `&T` and `&mut T`, explicit `-> nil`, legacy `Type[T]` generics, and
`*T`/`*const T`/`*mut T`.  Raw pointers use an explicit appended
`TypeKind.Pointer(Type, bool)` and lower to `HirTypeKind.Ptr`; they are not
misrepresented as references.  Exact, adjacent, bridge-shape, malformed, and
recovery coverage passes 10/10.

Fresh compiled checker SHA-256
`7af6262ecf92cd5f2835ac6594cd7e67d7fb89cac7ca740a83602afddef58d41`
accepts all five changed production files.  On the immutable 38-path manifest,
the original type diagnostic clears from 21 paths and three multiline-lambda
paths were already cleared by the claimed base revision.  Whole-file outcomes
therefore improve from 0 pass / 38 fail to 23 pass / 15 fail; the raw-pointer
loader file progresses to later `unsafe:`/dereference expression diagnostics.

The 15 non-passing files are explicitly rerouted, with no remaining core
type-grammar owner:

- 2 uninitialized fixed-array declarations: the array type parses, then the
  declaration policy requires an initializer (`riscv/startup.spl` variants).
- 1 reference expression/pattern (`src/app/interpreter/parser.spl`).
- 5 multiline declaration signatures (three DAP variants, WM demo, and GPU
  backend adapter).
- 5 structured/named expression literals (syscall specs, three benchmark
  variants, and NAND status test).
- 1 unsafe-block/raw-dereference expression
  (`src/compiler/99.loader/loader/smf_mmap_native.spl`).
- 1 `is` type-test comparison expression
  (`src/app/interpreter/ffi/eval_slice.spl`).

## Reproduction

```bash
python3 scripts/check/compiled-check-tree.py \
  --checker=/absolute/path/to/simple-check \
  --root=src/compiler --root=src/app --root=src/lib \
  --output-dir=build/mini_builds/full-tree-compiled-check-bounded-cycle1 \
  --workers=4 --batch-size=64 --timeout=120

python3 scripts/check/classify-compiled-check-results.py \
  --evidence-dir=build/mini_builds/full-tree-compiled-check-bounded-cycle1
```

Artifact SHA-256:
`27b9593a697d7115b9e16b4471b33f969bd98229e410a866c2ef28d3d95c6874`.
Manifest: 11,433 files, digest
`4522a42023807eabb45c24dc8c7f31b590c7640d717f83d554e954947b413298`.

## Evidence and owners

The highest-volume parser routes are type/multiline signatures (62), class
members (51), metadata blocks (24), unmatched canonical surface (20), keyword
identifiers (18), and structured/keyword exports (17).  Exact per-file routing
is retained in the build evidence and compact group routing in
`doc/03_plan/compiler/bootstrap/compiled_checker_failure_routes_2026-08-02.tsv`.

Likely owners are the pure-Simple parser declaration/type/expression surfaces
under `src/compiler/10.frontend/core/`, with the Rust parser serving as the
canonical parity reference.  Fix categories separately and rerun the immutable
manifest checker; do not modify invalid source merely to hide a parser gap.

## Non-cause

Batch parser-state leakage was investigated and disproved by a two-file minimal
pair.  The aggregate checker correctly reports one failing file of two; passing
members of a nonzero batch are not false positives.
