# NLL borrow check: `&mut` of a local is reported "may still be active at return" at every return (2026-08-24)

- **Status:** OPEN — not fixed
- **Severity:** HIGH — blocks `native-build` of any program whose closure
  contains such a function, including everything importing `std.io_runtime`
- **Area:** `src/compiler/55.borrow/borrow_check/` (pure Simple)
- **Found by:** clearing two earlier blockers in the
  `std.io_runtime` native-build chain (see
  `io_runtime_import_breaks_native_build_len_on_i64_2026-08-24.md` and
  `seed_val_bound_unsafe_block_parsed_as_call_2026-08-24.md`)

## Ten-line reproducer

```
# borrowmod.spl
extern fn rt_process_read_stdout_checked(pid: i64, status: &mut i32) -> text

pub fn read_res(pid: i64) -> i64:
    if pid <= 0: return -1
    var status: i32 = 0
    val chunk = rt_process_read_stdout_checked(pid, &mut status)
    if status == 1: return 1
    if status == 0: return 0
    if status == 2: return 2
    -3
```
```
# bmain.spl
use borrowmod.{read_res}
fn main() -> i64:
    print("r={read_res(-1)}")
    return 0
```

```
native-build bmain.spl
-> error: 22:1: borrow of `local(10)` may still be active at return
        |||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
   (once per return that follows the borrow)
```

The real-world instance is
`src/lib/nogc_sync_mut/io/process_ops.spl:229 process_read_stdout_result`,
which has exactly six returns after its `&mut status` and produces exactly six
errors. It was identified by probing `check_mir_module` to print
`module.name` / `mir_fn.name` alongside each error — the diagnostic itself
names neither, because `primary_span` is a MIR program point rendered as
`43:1`, not a source location.

## Mechanism

`nll.spl:409 check_terminator`, `case Return`, reports EVERY borrow that is
active at the return point:

```
val active = borrowset_active_list(borrow_set.borrows)
for borrow in active:
    self.errors = self.errors.push(NLLError(message: "borrow of `...` may still be active at return", ...))
```

Nothing ever ends a borrow. The structural reasons:

- `mod.spl:199 case Ref(dest, borrow_kind, place)` records the borrowed PLACE
  and **discards `dest`**, the local holding the reference. Without `dest` there
  is no way to ask when the reference dies.
- `check_terminator` receives a `liveness: LivenessResult` argument and never
  uses it.
- `LivenessAnalysis.record_use` / `record_def` (`nll.spl:166,173`) have **no
  callers anywhere in the tree**, so `uses`/`defs` stay empty and the liveness
  fixed-point computes empty sets. The liveness plumbing exists but is not wired.

So a correct NLL fix is not a patch: it needs `Ref` to record `dest`, real
per-local liveness, and a rule that only reports a borrow whose reference can
escape through the return value. That was judged too large and too safety-
sensitive to attempt in the same lane that fixed the two defects above.

## NOT verified

- Whether a shared `&` borrow of a local behaves the same way (only `&mut` was
  exercised).
- Whether the check ever produces a TRUE positive today, i.e. whether anything
  would regress if the `Return` case were simply removed. Not tested; do not
  assume it is dead weight.
- `--no-borrow-check` makes the build proceed past this point. That was used
  ONLY as a diagnostic probe to see what lay beyond; it is not a fix and must
  not be wired into any build lane.
