# Baremetal C runtime encodes `bool` as 8/0 while codegen encodes it as 11/19
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN
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

## Scoped C consumer repair — 2026-11-07

The ARM64 and x86_64 primitive logical consumers still interpreted tagged false (19) as integer2, converted tagged true (11) to false, and recognized encoded integers0/8 as booleans. The scoped repair handles11/19 first, retains prior nonboolean integer truthiness, preserves tagged booleans in conversion and keeps the predicate's raw0/1 result ABI. No compiler or runtime representation is changed.

The whole-production-object reproducer landed in #7447 records the original release failing25 of190 assertions per architecture and the candidate repair passing190/190 on both. The seven producer owners and two logical owners also have a focused native regression. Both checks are now CI-wired for owner/header/test changes, including the complete-object QEMU user-mode regression. The current release integration is validated with exact input identities in the landing receipt.

Astra reviewed the production C patch and confirmed that compiler/lib/MCP-specific conditional gates do not automatically apply to these embedded C files. This records completion of the primitive C consumer repair only. It does not claim a device boot, a Simple-generated caller, full owner branch coverage, or broader system qualification; those remain separate acceptance work. No broad bug closure is added here.
