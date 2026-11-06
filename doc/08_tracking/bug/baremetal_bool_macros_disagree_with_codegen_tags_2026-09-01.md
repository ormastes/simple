# Baremetal C runtime encodes `bool` as 8/0 while codegen encodes it as 11/19
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (2026-11-06; tagged consumers repaired, self-hosted/device acceptance pending)
- Date: 2026-09-01
- Scope: `examples/09_embedded/simple_os/arch/common/baremetal_runtime.h`
- Found while root-causing
  `riscv64_freestanding_bool_in_collection_always_true_2026-09-01.md`.
  **This is a SECOND, INDEPENDENT defect** and is deliberately NOT folded into
  that fix.

## The mismatch

`arch/common/baremetal_runtime.h:39-59` defines:

```c
#define TAG_INT      0x0
#define TAG_SPECIAL  0x3
#define ENCODE_INT(v) ((v) << 3 | TAG_INT)
#define NIL_VALUE     3
#define TRUE_VALUE    ENCODE_INT(1)   /* = 8  */
#define FALSE_VALUE   ENCODE_INT(0)   /* = 0  */
```

The compiler encodes booleans as TAG_SPECIAL values instead:
`true = 11`, `false = 19` (`src/compiler_rust/compiler/src/codegen/llvm/instructions.rs:14-17`,
restated at `codegen/llvm/functions/calls.rs:2628`).

So `TRUE_VALUE` (8) and `FALSE_VALUE` (0) are **not** the values the compiler
produces or consumes for a `bool`. Any C code in the baremetal runtime that
returns `TRUE_VALUE`/`FALSE_VALUE` to compiled Simple code, or compares an
incoming `RuntimeValue` against them, is wrong in at least one direction:

- runtime-produced `false` is `0`, which *accidentally* survives a `!= 0`
  truthiness test, so it can look correct;
- runtime-produced `true` is `8`, which no tag-aware consumer recognises as
  the boolean `true` (`11`);
- compiler-produced `false` is `19`, which never equals `FALSE_VALUE`.

There is also no bool encode/decode macro at all in that header, which is why
each call site improvises.

## Why it is filed separately

The riscv64 row-2 hang is fully explained by, and fixed at, the Cranelift
boxed-closure boundary (`unbox_int` passthrough + `!= 0`). Nothing in that fix
depends on these macros, and no measurement has yet shown a live call site
where the 8/0-vs-11/19 disagreement changes an observed result. Folding a
speculative header change into a fix with a measured cause would make the
verification of both weaker.

## Next step

Enumerate the actual uses of `TRUE_VALUE` / `FALSE_VALUE` in the baremetal
runtime (both `baremetal_stubs.c`, whose definitions win the link, and
`baremetal_runtime_core.inc.c`), decide the single canonical bool encoding, and
make the header agree with codegen — with a per-DEFINITION guard, since a
tree-wide grep cannot tell which definition the linker actually selected.


## Resolution evidence — 2026-11-05

Fixed on `work/libbug-linux-booltag-20261105` (branched from `origin/release/1.0.0`).

**Canonical encoding: the codegen tags won** — `true = 11`, `false = 19`
(`TAG_SPECIAL` payloads), per this doc's "Next step" ("make the header agree
with codegen"). `tagged_bool_const` in
`src/compiler_rust/compiler/src/codegen/llvm/instructions.rs:14-17` is the
source of truth and is pinned by
`scripts/check/check-baremetal-tagged-bool-decode.shs`.

All 7 definitions of `TRUE_VALUE`/`FALSE_VALUE` were aligned:

- `arch/common/baremetal_runtime.h:74-75` — now alias the existing
  `TAGGED_BOOL_TRUE`/`TAGGED_BOOL_FALSE` macros (11/19), with file-scope
  `_Static_assert` guards.
- `arch/{x86_64,x86_32,arm64,arm32,riscv64}/boot/baremetal_stubs.c` and
  `arch/riscv64/boot/baremetal_runtime_core.inc.c` — each self-contained TU
  redefines the pair; each was changed to the literal tagged values (spelled
  out because these TUs do not include the common header) **and** given its
  own `_Static_assert(TRUE_VALUE == 11, ...)` /
  `_Static_assert(FALSE_VALUE == 19, ...)` guard, per this doc's
  per-DEFINITION-guard requirement: any future drift now fails the build at
  the offending definition instead of silently relinking the old encoding.

Verified (aarch64 Linux host, source-level + host cc only):

- RED (pre-fix): extracted constants compiled to `TRUE_VALUE=8 vs 11 MISMATCH`,
  `FALSE_VALUE=0 vs 19 MISMATCH`.
- GREEN (post-fix): `TRUE_VALUE=11 MATCH`, `FALSE_VALUE=19 MATCH`; a
  deliberately-diverged definition fails to compile with
  `static assertion failed: "TRUE_VALUE must match codegen tagged true (11)"`.
- `grep` sweep: no `ENCODE_INT(1)`/`ENCODE_INT(0)`-based bool definitions
  remain under `examples/09_embedded/`.
- `cc -fsyntax-only -ffreestanding` (c11/gnu11 as appropriate) passes for all
  touched TUs and every TU that includes `baremetal_runtime.h`.
- `sh scripts/check/check-baremetal-tagged-bool-decode.shs` →
  `PASS — 4 definition(s) checked, all decode the tagged bool` (exit 0).

Not verified here (no hardware/semihosting on this host): actual baremetal
boot on any target; the change is ABI-visible only at runtime<->codegen bool
boundaries, which is exactly the defect.

## Remaining tagged-bool consumers — 2026-11-06

The producer repair `2593c5da5b4` is present in release/1.0.0. Revalidation at
`bbfe33dd9f1d` found a remaining consumer defect in the real ARM64 and x86_64
`baremetal_stubs.c` definitions:

- `rt_and`, `rt_or`, and `rt_not` decoded tagged `false` (19) as integer 2,
  so it was truthy; e.g. `rt_not(19)` returned false instead of true.
- `rt_to_bool(11)` fell through the nil/int/heap cases and returned false.
- `rt_is_bool` accepted encoded integers 0/8 while rejecting booleans 11/19.

The repair recognizes tagged booleans before preserving the logical helpers'
existing encoded-integer truthiness. The shared helper uses unsigned shifting,
so negative encoded integers stay truthy without adding a signed-shift
assumption. `rt_to_bool` preserves an existing tagged bool. `rt_is_bool` now
recognizes exactly the tagged pair, retaining its existing raw 0/1 result ABI.
No registered compiler caller or Simple declaration of that compatibility
predicate was found; this change does not invent a tagged return contract for
the surrounding `rt_is_*` family or implement other architectures' placeholders.
The seven producer definitions and their static assertions are unchanged.

Native owner regression:

```sh
sh scripts/check/check-baremetal-runtime-bool.shs bbfe33dd9f1d  # baseline: exit 1
sh scripts/check/check-baremetal-runtime-bool.shs       # repaired: exit 0
```

The check compiles the real macros for all seven owners and extracts the real
types and five function bodies from each of the two logical owners. Both old
owners fail on `rt_to_bool(tagged_true)`; the repaired owners pass tagged
true/false, encoded integer zero/one/negative/two, nil and raw zero, including
all 64 ordered pairs for `rt_and`/`rt_or`, negation, conversion, and the raw
predicate. Five constant-only owners remain green. This is native C execution
of the selected definitions, not execution of an ARM64 image or a Simple
compiler fixture. Clang SHA-256:
`20ba1856942744291a6aaaf9f2c94f6d0cd7cac5aa9557fce96471dc7ef25d6f`.

Full touched translation units also pass freestanding syntax checks for
`aarch64-none-elf` and `x86_64-unknown-elf`. ARM64 retains an unrelated existing
negative-shift warning in `baremetal_stubs.c:6720`, its wide-integer range check.

Remaining acceptance: an admitted self-hosted producer executes the tagged-bool
runtime boundary in a baremetal/attested native fixture. Pure-Simple Cranelift
internal `MirConstValue.Bool` is raw 1/0 (`cranelift_codegen_adapter.spl`,
`cl_translate_const`); that internal representation is distinct from the tagged
RuntimeValue boundary tested here. No device, bootstrap, or end-to-end
self-hosted acceptance is claimed by this repair.
