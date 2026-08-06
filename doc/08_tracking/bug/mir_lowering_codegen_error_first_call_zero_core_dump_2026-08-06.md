# `CompileResult.CodegenError` construction called unresolved `Array.first()`, crashing the compiler (`call 0`) on every fatal MIR-lowering error — source-fixed, binary verification blocked by a separate pre-existing native-build instability

- **Date:** 2026-08-06
- **Severity:** high — every native-build invocation that hits a fatal MIR
  lowering error (which includes the common `Option<Trait>.unwrap().method()`
  shape) crashed the compiler process itself (SIGSEGV) instead of printing a
  diagnostic, on the deployed self-hosted stage3 binary.
- **Status:** source-fixed in three call sites (`driver_aot_pipeline.spl`,
  `driver_pipeline_execution.spl`, `driver_orchestration.spl`); verified
  correct via the interpreted `bin/simple` worker path (clean exit 1,
  correct message, no crash). **NOT yet verified against a freshly rebuilt
  stage3 binary** — blocked by an unrelated, already-broader, pre-existing
  native-build instability described below.

## How this was found

Investigating a reported "native codegen core-dumps when a trait method is
called through `Option<Trait>.unwrap()`" (module-global `Option`-wrapped
trait/class instance, unwrapped per call — the exact shape
`g_fat32_mount_dev: BlockDevice? = nil` uses in
`src/os/kernel/fs/fat32.spl`; see "Update 4" of
`path_based_fs_syscalls_fake_success_2026-08-06.md` for the original
sighting).

## Reproduction

```
trait Writable:
    fn write_it(self, v: i64) -> i64

class Impl:
    field: i64

impl Writable for Impl:
    fn write_it(self, v: i64) -> i64:
        return v + 1

var g_dev: Option<Writable> = None

fn set_dev():
    g_dev = Some(Impl { field: 0 })

fn call_write() -> i64:
    return g_dev.unwrap().write_it(41)

fn main():
    set_dev()
    print(call_write())
```

`bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build repro.spl -o
out`: prints two correctly fail-closed WARNING lines ("unresolved method call
'unwrap'/'write_it' lowered to const-0 placeholder (silent-null risk, Task
#145)"), then four `[ERROR] MIR error: ...` lines, then **the compiler process
itself dies with SIGSEGV** (`timeout: the monitored command dumped core`,
exit 139). Exact same crash reproduces with **no trait, no Option** at all —
just `some_plain_class_instance.totally_nonexistent_method_xyz()` — proving
the crash is generic to any fatal MIR-lowering error, not specific to
`Option<Trait>.unwrap()`.

## Root cause (confirmed via gdb + objdump, not guessed)

MIR lowering itself is **correct and already fails closed**: an unresolved
method call is collected as a fatal error (`_mir_error_is_fatal` in
`driver_pipeline_lowering.spl` matches `"unresolved method call:"` and
`"unsupported MIR expression:"`), and `lower_to_mir()` correctly returns
`false`. `aot_compile()` (`driver_aot_pipeline.spl`) correctly detects this
(`if not mir_ok: ... return CompileResult.CodegenError(msg)`) and never
reaches codegen. **The crash is not in MIR lowering or codegen at all** — it
is in constructing the `CodegenError`'s own message string, three lines
later:

```
val first_err = self.ctx.errors.first()
val msg = if first_err != nil: first_err else: "MIR lowering failed"
return CompileResult.CodegenError(msg)
```

`gdb -batch -ex run -ex bt` on the crashing process shows a call through
address `0x0` (`Program received signal SIGSEGV, 0x0000000000000000 in ?? ()`,
caller at `0x66b6ac`). `objdump -d` at that address:

```
66b69c: mov    (%rbx),%rax
66b69f: and    $0xfffffffffffffff8,%rax   ; untag
66b6a3: mov    0x70(%rax),%rdi
66b6a7: call   0                          ; call rel32, displacement resolves to absolute 0
66b6ac: mov    %rax,%rbx
66b6af: mov    $0x3,%esi
66b6b4: mov    %rax,%rdi
66b6b7: call   ...                        ; nil-check on the result
66b6bc: test   %rax,%rax
66b6bf: jne    ...                        ; not-nil -> true arm
66b6c1: lea    0x86bb8(%rip),%rdi ; mov $0x13,%esi   ; $0x13 = 19 = len("MIR lowering failed")
```

`call 0` immediately followed by a nil-check, immediately followed by the
19-byte literal `"MIR lowering failed"` pins this exactly to the `if
first_err != nil: first_err else: "MIR lowering failed"` line above. The
`0` call target is **baked into stage3's own machine code at self-host build
time** (a `call rel32` with a fixed displacement), not a runtime vtable miss.

**Confirmed by direct discriminator probe** (no rebuild needed, uses the
existing stage3 binary): `val f = xs.first()` on a plain `[text]` array
produces `[mir-lower] WARNING: unresolved method call 'first' lowered to
const-0 placeholder (silent-null risk, Task #145)` — i.e. **builtin
`Array.first()` has no MIR method symbol under native codegen**, the same gap
class already documented for `push`/`map`/`filter`/`fold` (see Bug #149's
comment in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
around line 2587 — `try_instance_method`/`try_trait_method`/`try_ufcs` in
`resolve_strategies.spl` all require a symbol-bearing HIR type, and the
builtin Array type has none). `Array.len()` is unaffected (resolves cleanly,
confirmed via the same probe technique) — only the method-call-shaped
accessors (`first`/`last`, presumably) hit this gap; index reads (`xs[0]`)
aren't method calls at all so are unaffected.

So the actual failure chain is: **the compiler's own error-reporting code
calls an unresolved builtin (`Array.first()`), which lowers to a
placeholder that should be a fail-closed `rt_panic`+const-0 (per the Task
#145 comment at `method_calls_literals.spl:2644-2684`) but in this
particular reachable-from-self-host-build call shape instead produced a bare
null call** — every fatal MIR-lowering error (not just the reported
`Option<Trait>.unwrap()` shape) triggers this same crash.

## Fix

Three call sites replaced `.first()` with a length-guarded index read (the
established safe substitution pattern in this codebase for builtin-Array
methods with native-codegen gaps, mirroring the documented `Dict.get()` ->
`contains_key`+`d[k]` substitution in
`doc/07_guide/language/dict_native_pitfalls.md`):

```
val msg = if self.ctx.errors.len() > 0: self.ctx.errors[0] else: "MIR lowering failed"
```

- `src/compiler/80.driver/driver_aot_pipeline.spl` (`aot_compile()`) — the
  exact site the repro's gdb backtrace pins to; this is the path
  `native-build` takes.
- `src/compiler/80.driver/driver_pipeline_execution.spl`
  (`jit_compile_and_run()`) — same anti-pattern, JIT path, not
  repro-verified against this specific crash but fixed as part of the same
  family sweep.
- `src/compiler/80.driver/driver_orchestration.spl` (the general
  `compile()` orchestration path, which is what `bin/simple native-build`'s
  interpreted worker actually calls through `run_compile_entry`).

`src/compiler/driver/*` is a symlink to `src/compiler/80.driver/*`, so no
duplicate edits were needed there.

**Deliberately not fixed in this change:** the underlying MIR-lowering gap —
`Array.first()`/`.last()` have no native codegen support at all (same status
as the already-tracked `push`/`map`/`filter`/`fold` gaps). Any OTHER caller
of `.first()`/`.last()` on a builtin array under native codegen will still
hit the same const-0-placeholder-then-panic path (which is supposed to be
safe/fail-closed per the Task #145 comment, but as this bug shows, is not
reliably so). Recording this explicitly per the "record instead of silently
normalize" rule: **`Array.first()`/`Array.last()` need a real MIR lowering
case, parallel to the existing `push`/`map`/`filter`/`fold` special-casing in
`method_calls_literals.spl` around line 2569-2585** — out of scope for this
change (bigger surface, more risk, not required to eliminate the reported
core-dump).

## Verification

**Interpreted path (`bin/simple`, exercises the edited `.spl` source
directly, no rebuild required):** both the original `Option<Trait>.unwrap()`
repro and the generic (no-trait, no-Option) repro now produce a clean exit 1
with `error: MIR lowering error: unresolved method call: unwrap` /
`unresolved method call: totally_nonexistent_method_xyz` respectively — no
crash, correct message content (proving `self.ctx.errors[0]` correctly
threads through the real first error, not just avoiding a crash by falling
back to the generic "MIR lowering failed" placeholder).

**Native stage3 binary (`bootstrap/stage3/.../simple`): NOT verified.**
Rebuilding stage3 to pick up this fix was attempted and abandoned after
discovering the deployed stage3 binary currently SIGSEGVs on **every**
`native-build` invocation that reaches the codegen/link success path,
including a trivial `fn main(): print("hello")` — unrelated to this bug
entirely (that repro's `lower_to_mir()` succeeds with zero errors, so the
`.first()` line this bug is about never executes). `strace` shows a
different fault: `SEGV_MAPERR` at address `0x118`, occurring immediately
after two `clone3`-spawned subprocesses that read `uname -m`/`uname -s`
output (target-triple detection, on the codegen/link success path) — this is
close to but not identical to the already-tracked
`native_selfhosted_run_segfault_startup_normalize_2026-07-24.md` (that one
faults at `0x8` in `startup_normalize_program_args`, pre-output, and is
recorded as "run/test source-fixed; redeployment blocked"). This `0x118`
fault is reproducible 3/3 tries and blocks self-compiling a new stage3 at
all right now — filing as a distinct, separate, more severe finding (a
native-build that currently cannot emit ANY binary via this stage3 copy)
rather than silently treating it as the same issue. Not investigated further
here (out of scope for this change); flagged for follow-up before this fix
(or any other native-build fix) can be binary-verified end to end.

## Why the original "core-dumps" description pointed at the wrong layer

The task that surfaced this bug reasonably assumed the crash was in MIR
lowering's handling of `Option<Trait>.unwrap()` specifically (it's untested,
looked deliberately fail-closed with a WARNING+rt_panic, and the crash
followed immediately after). The gdb+objdump evidence above rules that out:
MIR lowering behaves exactly as designed (fails closed, returns a fatal
error), and reproduces identically with no Option and no trait involved at
all. The real defect was three lines later, in how the compiler driver
itself reports that MIR lowering failed.
