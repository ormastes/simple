# A module-level `val` holding a struct is zero-initialized when passed as a call argument

- **Date:** 2026-09-01
- **Status:** OPEN
- **Binary:** `bin/simple` (Rust seed), interpreter path (`bin/simple run`)
- **Severity:** silent wrong answer — no error, no warning, no crash

## Symptom

A module-level `val` whose value is a struct reads correctly through direct
field access, but binds to a **zero-initialized struct** the moment it is passed
as an argument to a function. Binding it to a local first does not help: the
copy is broken too. An inline constructor, or a struct rebuilt field-by-field
from the same global, is correct.

## Minimal reproduction

`bfmod.spl`:

```
struct BF:
    shift: i64
    width: i64

val A = BF(shift: 3, width: 2)
val B: BF = BF(shift: 3, width: 2)

fn bf_mask(f: BF) -> i64:
    ((1 << f.width) - 1) << f.shift
```

`bfuse.spl`:

```
use bfmod.*
fn main():
    print "A.shift={A.shift} A.width={A.width}"   # 3 2   -- correct
    print "mask(A)={bf_mask(A)}"                   # 0     -- WRONG, expect 24
    print "mask(B)={bf_mask(B)}"                   # 0     -- WRONG, expect 24
    val a = A
    print "mask(local copy)={bf_mask(a)}"          # 0     -- WRONG
    print "mask(inline)={bf_mask(BF(shift: 3, width: 2))}"                 # 24 -- correct
    print "mask(rebuilt)={bf_mask(BF(shift: A.shift, width: A.width))}"    # 24 -- correct
```

Measured output on the seed:

```
A.shift=3 A.width=2
mask(A)=0
mask(B)=0
mask(local copy)=0
mask(inline)=24
mask(rebuilt)=24
```

Notes on scope, measured:
- Reproduces both same-module and cross-module (`use m.*`).
- Not annotation-dependent: `val A = BF(...)` and `val B: BF = BF(...)` both fail.
- A module-level `val` of scalar type (`val N: i64 = 77`) is unaffected.
- A struct returned from a function and passed on is unaffected.

## Impact

The natural, compact way to write a hardware register bitfield table is a list
of module-level struct constants:

```
val CC_EN = BitField(shift: 0, width: 1)
...
bf_get(cc, CC_EN)
```

Under this defect every such lookup silently returns 0 — a register decoder that
reads every field as zero, with nothing failing loudly. This was found while
building the NVMe controller register file
(`examples/09_embedded/simpleos_nvme_fw/fw/nvme_reg_defs.spl`): 45 of that
module's assertions failed, all traced to this single cause.

## Workaround in use

Every bitfield constant is a **nullary function returning the struct**
(`fn bf_cc_en() -> BitField: BitField(shift: 0, width: 1)`), so the value is
constructed at each use rather than read from a module-level `val`. Recorded
inline in the `nvme_reg_defs.spl` module docstring so the shape is not
"normalized" back to the broken form by a later cleanup.

## Related

- `doc/08_tracking/bug/interp_me_method_first_param_times8_conditional_2026-06-29.md`
- `doc/08_tracking/bug/interp_method_call_result_as_arg_corruption_nested_2026-06-30.md`

Both are also argument-binding corruptions in the interpreter; this may share a
root cause with them.
