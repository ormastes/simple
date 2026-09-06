# Baremetal C runtime encodes `bool` as 8/0 while codegen encodes it as 11/19

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
