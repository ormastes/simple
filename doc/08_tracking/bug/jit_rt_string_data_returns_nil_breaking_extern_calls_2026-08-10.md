# jit lane: a nested extern call used as an extern ARGUMENT is marshalled raw, arriving as Nil/Bool/garbage

*(Filed as "`rt_string_data(text)` evaluates to Nil". That title named the
symptom, not the defect — `rt_string_data` is fine in isolation in both lanes.
Kept as the canonical path for inbound links.)*

- **Date:** 2026-08-10
- **Status:** **FIXED** 2026-08-10 in the jit lane. Fenced by
  `scripts/check/check-jit-nested-extern-arg-marshal.shs`.
  Two adjacent gaps found on the way are left OPEN and RED below.
- **Lane:** `jit` only. `interpreter` was always correct. The AOT/`.smf` lane
  cannot reach this path at all (see OPEN 2).
- **Class:** engine divergence / silent extern-call failure.

## Reproduction

The filed reproduction is real, but the diagnosis in it ("suspect the `text`-typed
*argument* marshal") was wrong. `rt_string_data` on its own is correct in both
lanes:

```
$ cat /tmp/q23/b.spl
extern fn rt_string_data(value: text) -> i64
extern fn rt_string_len(value: text) -> i64
fn main():
    val line = "Q23B_PAYLOAD"
    print "ptr_nonzero={rt_string_data(line) != 0} len={rt_string_len(line)}"

interpreter: ptr_nonzero=true len=12
jit:         ptr_nonzero=true len=12
```

The discriminator is **nesting an extern call inside another extern call's
argument list**:

```
extern fn rt_simpleos_log_emit(level: i64, ptr: i64, len: i64) -> bool

val a = rt_simpleos_log_emit(3, rt_string_data(line), rt_string_len(line))  # nested
val p = rt_string_data(line)
val n = rt_string_len(line)
val b = rt_simpleos_log_emit(3, p, n)                                       # hoisted
```

jit lane, on `bin/simple` before the fix:

```
ERROR simple_compiler::interpreter_sffi: 806: rt_interp_call error:
  Runtime("rt_simpleos_log_emit: argument 2 must be an int, got Nil")
```

…for the **nested** form only; the **hoisted** form is clean. A second run of a
differently shaped fixture reported `got Bool(true)` for the same slot, and a
third reported `argument 1` rather than `argument 2` — the decoded value depends
on the bit pattern of whatever raw scalar landed in the slot, so the symptom is
not stable. `Nil` is one of several faces of one defect.

The interpreter lane produces no error for any of these forms.

## Root cause

`src/compiler_rust/compiler/src/codegen/instr/core.rs`, `compile_interp_call`.

The argv-boxing loop (`core.rs:860-887`) decides how to store each argument by
looking up `ctx.vreg_types`:

```rust
match ctx.vreg_types.get(arg).copied() {
    Some(TypeId::BOOL)  => arg_val = call_runtime_1(.., "rt_value_bool",  arg_val),
    Some(TypeId::I64 | TypeId::U64)
                        => arg_val = call_runtime_1(.., "rt_value_int",   arg_val),
    Some(TypeId::F64)   => arg_val = call_runtime_1(.., "rt_value_float", arg_val),
    _ => {}                       // <-- stores the value RAW
}
builder.ins().store(MemFlags::new(), arg_val, argv, (index * 8) as i32);
```

and the dest-handling block 40 lines below states the invariant that breaks it,
in its own comment (`core.rs:900`):

> *"Call dests carry no entry in vreg_types, so the SFFI naming convention is
> the reliable signal here."*

So for `rt_string_data(line)` the dest vreg is unboxed to a plain `i64` via
`rt_value_raw_i64` and inserted into `vreg_values` — **with no `vreg_types`
entry**. When that vreg is then used as an argument, the loop finds nothing,
takes `_ => {}`, and stores the raw integer into argv. `interp_call_handler`
(`interpreter_sffi.rs:679`) runs `runtime_to_value` over the slot, which decodes
the raw scalar as whatever NaN-box pattern its bits match — `Nil`, `Bool(true)`,
or an unrelated integer.

The two halves of one function disagreed about an invariant, and neither side
was wrong on its own terms.

## Why it was invisible

`src/runtime/startup/common/runtime_log_hosted.c` was, verbatim:

```c
bool rt_simpleos_log_emit(int64_t level, int64_t msg_ptr, int64_t msg_len) {
    (void)level; (void)msg_ptr; (void)msg_len;
    return false;
}
```

A hard `return false`, with the arguments explicitly discarded. So the hosted
path **could not distinguish** "the marshal delivered a real string and the hook
is stubbed" from "the marshal handed me garbage". Both return `false`, the
Simple side takes its fallthrough in `logger.spl`, and the log line still
appears. Every existing logging check was satisfied.

## Fix — JIT marshalling code, not `.spl`

This one genuinely lives in the Rust JIT codegen, not the Simple layer, so per
the repo's fix-in-`.spl` rule: **stating that explicitly rather than forcing a
`.spl` workaround.** There is no `.spl` change that could repair it — hoisting
the nested calls into locals in `logger.spl` would paper over this one call site
and leave the defect live for every other caller.

`core.rs` now records the unboxed type on the dest, restoring the invariant the
boxing loop depends on:

```rust
let v = call_runtime_1(ctx, builder, "rt_value_raw_i64", result);
ctx.vreg_types.entry(*d).or_insert(TypeId::I64);
```

and the same for the `rt_value_as_float` arm (`TypeId::F64`). The kept-boxed arm
deliberately records nothing — those values *are* `RuntimeValue`s, so the loop's
raw store is already correct there. `or_insert` is used rather than `insert` so a
real MIR-derived type is never overwritten.

This fixes every nested-extern argument, not just the logging call shape.

## Observability — `runtime_log_hosted.c`

The C stub gains a **default-off, level-gated** probe
(`SIMPLE_LOG_HOSTED_PROBE=1`) that writes what it actually received to fd 2:

```
[HOSTED-LOG-PROBE] emit level=7 len=20 payload=Q23B_MARSHAL_PAYLOAD
```

and `<UNREADABLE>` when the `(ptr,len)` pair is null or implausible. **The return
value is unchanged in both modes**, so the hosted contract and every existing
logging check are untouched. This exists because the bare `return false` is the
reason the defect survived: without it, no check can assert anything stronger
than "an error message did not appear", and error-absence is exactly the kind of
assertion that passes on broken code.

## Board-runnable — SCOPE OF CLAIM

Per `.claude/rules/board-runnable.md`, stating the limit rather than implying
coverage:

- **All evidence here is hosted x86_64 Linux**, `interpreter` and `jit` engines.
- **No board evidence, and no QEMU evidence, was collected.** No claim is made
  about the physical dev board.
- The original filing said this "would silently divert every log line away from
  the device" on a jit baremetal build. **That configuration does not exist in
  this repo's build graph**: `src/compiler/70.backend/baremetal/` contains no
  cranelift path, so a board build is AOT-lowered via LLVM and calls
  `src/runtime/startup/baremetal/runtime_log.c` as a direct C symbol, never
  through `rt_interp_call`. The board-loss framing was speculative and is
  withdrawn.
- The defect is nonetheless real and worth fixing on its own terms: the hosted
  **jit lane is the default developer and spec lane**, and it was silently
  corrupting every nested-extern argument in the process.
- What would be needed for a genuine board claim: an AOT/baremetal build that
  actually links `runtime_log.c` and a serial transcript showing the payload on
  the UART. That is blocked today by OPEN 2 below.

## OPEN 1 — the LLVM lane does not box argv at all

`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2913-2930` builds
the same argv array with `coerce_value_to_type(value, i64)` and a raw
`build_store`, with **no boxing switch whatsoever** — not even the partial one
cranelift has. Whether that is correct depends on an LLVM-lane value
representation this change did not audit. Left OPEN and unmeasured rather than
asserted either way.

## OPEN 2 — `rt_simpleos_log_emit` is unresolvable in the AOT/`.smf` lane (RED)

```
$ bin/simple compile /tmp/q23/aot.spl -o /tmp/q23/aot.smf     # succeeds
$ bin/simple /tmp/q23/aot.smf
ERROR simple_common::smf::reloc: 95: Undefined symbol: rt_simpleos_log_emit
                                     (required by relocation 7)
error: load failed: relocation failed
```

The symbol is not exported to the SMF loader, so the third lane cannot execute
this path at all. Pre-existing, unrelated to this fix, and left RED. It is also
the reason the board-evidence path above is currently blocked: the AOT lane is
the one a board build uses.

## Check

`scripts/check/check-jit-nested-extern-arg-marshal.shs`, both lanes. It asserts
the **payload at the C boundary**, not a line count — a count assertion passes on
the broken code, because the Simple-side fallthrough already prints an
unlabelled line from another layer, which is precisely how this hid.

- **payload positive** — `[HOSTED-LOG-PROBE] emit level=7 len=20
  payload=Q23B_MARSHAL_PAYLOAD` must appear, proving the `(ptr,len)` pair
  survived the marshal and points at the real bytes.
- **discriminator** — a fixture passing a NULL pointer must make the probe print
  `<UNREADABLE>`. Without it, both the payload assertion and the `<UNREADABLE>
  absent` assertion are vacuous. If it does not fire the script exits **2**
  (`ERROR — nothing was checked`), never PASS.
- **negative control** — `<UNREADABLE>` absent from the real probe.
- **signature controls** — `must be an int, got` and `rt_interp_call error`
  absent.
- **lane control** — interpreter must agree with jit on every value.
- **probe-off control** — no probe output without the env var, proving default-off.

Measured on a purpose-built seed (`CARGO_TARGET_DIR=/tmp/q23/target`, private so
the shared `src/compiler_rust/target` could not serve another session's
artifact — see the measurement note below):

```
PASS -- 16 assertion(s) checked across 5 probe(s)                      exit 0
```

Negative evidence, same fixture, pre-fix `bin/simple`:

```
ERROR simple_compiler::interpreter_sffi: 806: rt_interp_call error:
  Runtime("rt_simpleos_log_emit: argument 2 must be an int, got Nil")     [jit]
(no such error)                                                  [interpreter]
```

A full revert-and-rebuild proof (delete the `or_insert` line, rebuild, re-run the
check to a FAIL verdict) was started; the release link did not finish inside the
session window. The before/after above is on the identical fixture and differs
only by this change.

### Measurement note — a stale shared artifact almost produced a false GREEN

The first two rebuild attempts in this session used `-p simple_compiler`; the
crate is `simple-compiler`, so **cargo errored and built nothing** while the
wrapper still exited 0. `src/compiler_rust/target/release/simple` nevertheless
contained a *newer-than-`bin/simple`* binary built by a concurrent session, and
running the fixture against it showed the defect absent — which reads exactly
like "my fix works". It was caught only by comparing the binary's mtime
(08:39:26) against the source edit (08:44:43). Every number above was
re-measured afterwards on a private target dir with a positive capability probe
(`strings | grep -c HOSTED-LOG-PROBE` = 1) confirming the binary really contains
this change.

## Related

- `doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
- `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
- `scripts/check/check-noalloc-log-error-reaches-stderr.shs`
