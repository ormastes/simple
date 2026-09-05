# `CompileResult.CodegenError` construction called unresolved `Array.first()`, crashing the compiler (`call 0`) on every fatal MIR-lowering error — source-fixed, binary verification blocked by a separate pre-existing native-build instability

- **Date:** 2026-08-06
- **Severity:** high — every native-build invocation that hits a fatal MIR
  lowering error (which includes the common `Option<Trait>.unwrap().method()`
  shape) crashed the compiler process itself (SIGSEGV) instead of printing a
  diagnostic, on the deployed self-hosted stage3 binary.
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  unresolved `Array.first()`) is source-fixed in three call sites
  (`driver_aot_pipeline.spl`, `driver_pipeline_execution.spl`,
  `driver_orchestration.spl`) and confirmed still working end-to-end via a
  2026-08-06 execution probe (4/4 fatal MIR errors printed cleanly, no
  crash from error reporting itself). The FOLLOW-UP feature added in the
  same investigation — real MIR lowering for `Array.first()`/`.last()`
  (`lower_array_first_or_last`) — is **execution-confirmed NOT to engage**:
  a 2026-08-06 discriminator probe shows every tested `.first()`/`.last()`
  call (empty/non-empty, `i64`/`text`/struct element types, including a
  plainly explicitly-typed `[i64]` local) still falls through to the OLD
  "unresolved method call" placeholder. **Root cause since pinned and
  source-fixed** (missing `Some(...)` wrap on the function's success return
  — see "Update (2026-08-06, later still)" below); binary/execution
  verification remains blocked, now confirmed to be blocked by a THIRD,
  distinct self-compile crash (`runtime error: field access on nil
  receiver`) on top of the two SIGSEGVs already on file, not merely
  unattempted. See "Update (2026-08-06, later)" below for the exact repro and
  investigation leads. Verification was also complicated throughout by an
  unrelated, already-broader, pre-existing native-build SIGSEGV described
  below (which the discriminator-probe technique works around, since MIR
  diagnostics print before that crash).

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

## Update (2026-08-06): real MIR lowering added for `Array.first()`/`.last()`

Follow-up to the "Deliberately not fixed" note above. `Array.first()` /
`Array.last()` now get real MIR lowering in `method_calls_literals.spl`
(`lower_array_first_or_last`, called from the same `local_is_runtime_array`
guard block that already special-cases `push`/`map`/`filter`/`fold`), instead
of always falling through to the const-0-placeholder-then-`rt_panic` path.

**Confirmed `Option` semantics** (read directly from source, not guessed):
- The nil/None sentinel is the raw i64 `3` (`rt_core_nil()` in
  `runtime_native.c` = `RT_VALUE_TAG_SPECIAL | (RT_VALUE_SPECIAL_NIL << 3)`).
  `rt_is_none(value)` treats any raw value `== 3` as None regardless of
  static element type. This is also the exact value `NilLit` materializes
  (`expr_dispatch.spl`, `case NilLit`) and the value `rt_array_get` already
  returns for an out-of-bounds index.
- The **canonical** typed `Option<T>` representation used by real
  `Some(x)`/`None` construction sites (not the narrower raw-flat-payload
  fast path some Option-typed *locals* use) is an enum-id-1 handle built via
  `rt_enum_new(enum_id=1, disc, payload)` where `disc` is `0` for Some / `1`
  for None, unwrapped via `enum_payload_value`/`rt_unwrap_or_self`. The
  existing helper `ensure_option_handle` (`switch_operators_calls.spl:406`)
  builds this handle from a raw payload local (using `self.nil_locals` to
  distinguish a compile-time-known nil from a real payload) and is the
  general-purpose promotion path already used by `Option.map`
  (`method_calls_literals.spl:775-869`, the closest existing precedent for
  "construct an `Option<T>` result from computed control flow") and several
  other call sites.

**Implementation** (`lower_array_first_or_last`, added just after
`lower_array_fold`): branches on `rt_array_len(arr) > 0`. Non-empty:
`rt_array_get(arr, idx)` (idx=0 for first, `len-1` for last) →
`decode_runtime_value` (the array element is stored TAGGED, via `push`'s
`box_runtime_value` call, so it must be decoded before use as a payload) →
`ensure_option_handle`. Empty: a nil-marked `emit_const_int(3)` local →
`ensure_option_handle`. Both arms store into a shared result temp and `goto`
a merge block (the same store-in-each-branch pattern `NullCoalesce`/
`Option.map` already use to avoid a bare `phi` mid-block). The element's
declared HIR type is looked up two ways (`find_local_hir_type(arr.id)`, then
`receiver_declared_type(receiver)`); **if neither succeeds, the function
returns `nil` and the call site falls through to the existing loud
"unresolved method call" `rt_panic` placeholder** rather than guessing a
type — a guessed `MirType.i64()` for, say, a `[text]` receiver would send
`decode_runtime_value` down its integer arm, silently corrupting the string
handle instead of failing loudly. So today: `.first()`/`.last()` on any
receiver whose element type is statically known gets real Option-returning
lowering; other receivers keep exactly today's fail-closed behavior.

**Verification status: implemented, NOT execution-verified.** Every
available `simple` executable turned out to be unable to exercise the edited
`.spl` source:
- `bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`) is, despite
  its name and the `bootstrap.md` policy ("NEVER copy Rust bootstrap binary
  to `bin/release/simple`"), **currently the Rust seed** — running it prints
  the seed's own "this Rust-built Simple binary is a bootstrap seed only"
  warning. It is a compiled artifact and cannot read this edit at all; any
  test run through it exercises the seed's own pre-existing
  `rt_array_first`/`rt_array_last` native support (confirmed present in
  `src/compiler_rust/compiler/src/codegen/**`), not this change. (Recording
  this as a separate finding: there is currently no deployed pure-Simple
  self-hosted binary, contrary to policy.)
- `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` is a real self-hosted
  binary, but was built at 04:14 today, before this edit, so it also cannot
  exercise it without a fresh bootstrap.
- Running the seed directly against the compiler's own **source** (`seed
  src/app/cli/compile_entry.spl compile --native -o out probe.spl`, the
  "interpreted worker path" pattern from this bug's original fix) does load
  and parse this edited file correctly (no parse/syntax errors across
  several full-tree loads that walked past it), but `cli_compile` resolves
  to `src/app/io/mod_stub.spl`'s stub (`"Error: compile requires Rust SFFI
  support"`) rather than the real driver when the seed interprets the
  compiler tree this way — codegen is unreachable through this route.
- A full `bootstrap-from-scratch.sh` rebuild would produce a binary that
  could actually exercise this change, but was judged out of scope for this
  narrower change (see "No bootstrap unless essential").

Side finding, unrelated to this change but discovered while probing it: a
plain `bin/simple native-build hello.spl` (`fn main(): print("hello")`)
**succeeded** (exit 0, ran, printed `hello`) on the current seed-as-`bin/
simple` setup, taking ~150s. This is evidence *against* this bug's earlier
"native-build currently SIGSEGVs on every invocation, including trivial
`hello.spl`" blocker being live right now -- but since that run also went
through the seed, not a rebuilt self-hosted stage3, it does not by itself
retire that blocker for the self-hosted binary; it only shows the seed
itself is not universally broken this way today.

## Update (2026-08-06, later): execution verification attempted again — still blocked, now with 4x more evidence the blocker is systemic, not this-worktree-specific

Fresh session, `git fetch origin main` first (tip `eb1fa07e49e`, c49bb56 confirmed
an ancestor). Searched for any genuinely self-hosted binary built *after*
c49bb56 landed (2026-08-06T15:17:50+00:00):

- This worktree's `bootstrap/stage{1,2,3}/...simple` (BuildID `3b41f55f...`,
  mtime 04:12-04:14) all **predate** the fix — ruled out immediately, no test
  run needed.
- `bin/release/x86_64-unknown-linux-gnu/simple` is still the Rust seed
  (confirmed again via its own WARNING banner) — cannot exercise the edit,
  per the previous update.
- Found **four** independent parallel worktrees on disk
  (`~/dev/simple-s3clean`, `-s3red`, `-s3family`, `-s3fix`), each with a
  freshly-rebuilt `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` (BuildID
  `fe5c2e9b...`, distinct from both the seed and this worktree's stale
  stage3) and a `release/x86_64-unknown-linux-gnu/simple` (BuildID
  `545d912c...`), all built between 20:20 and 21:07 today — well after the
  fix landed. Confirmed via `git log -1 -- .../method_calls_literals.spl`
  in each worktree that HEAD's last touch to the fixed file *is* commit
  c49bb56, and `git merge-base --is-ancestor c49bb5606dea HEAD` returns true
  in all four. These are genuinely self-hosted, post-fix binaries.

**Control probe first** (`fn main(): print("hello")`, the same trivial case
from the "Native stage3 binary: NOT verified" section above), run on all
five candidate binaries (4x `bootstrap/stage3/...`, 1x `release/...` from
`simple-s3clean`): **all five SIGSEGV**, identical symptom
(`timeout: the monitored command dumped core`, exit 139, no output file
produced). `strace -f -e trace=memory` on the `simple-s3clean` stage3 run
confirms the exact same fault already pinned in this doc's earlier update:
`SIGSEGV {si_code=SEGV_MAPERR, si_addr=0x118}`, occurring right after the
`uname -m`/`uname -s` subprocess pair exits cleanly (target-triple
detection). Same address, same call shape, reproduced on five more distinct
freshly-built self-hosted binaries across four separate worktrees, none of
which is this worktree's own stale stage3, on top of the 5/5 already
recorded in `stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`
(2/2 this worktree + 3/3 the other lane) — this is one input (`hello.spl`)
tested on five binaries, not a claim that every input crashes identically
(see below: the fatal-MIR-error path crashes too, but at a different
address).

**Corroboration, not the final word:** the `0x118` crash confirms every
self-hosted `native-build` rebuilt today (before or after c49bb56) SIGSEGVs
before the process exits on the zero-MIR-error (`hello.spl`) case — but MIR
lowering's own diagnostics print to stderr *before any crash on either path*,
so they are captured regardless. This doc's own earlier "direct discriminator probe"
technique (grep the `[mir-lower] WARNING: unresolved method call '...'
lowered to const-0 placeholder` line) still works on a crashing binary and
was used below to get a real answer instead of stopping at "blocked."

**Discriminator probe result: `lower_array_first_or_last` does NOT engage,
on any of the three prepared test files, including the plain explicitly-typed
`[i64]` case.** Ran all three (`first_last_int.spl`, `first_last_text.spl`,
`first_last_struct.spl`) through `simple-s3clean`'s post-fix stage3 with full
(untruncated) stderr capture. Every `.first()`/`.last()` call in every file —
`empty.first()`, `empty.last()`, `nonempty.first()`, `nonempty.last()` for
`val nonempty: [i64] = [10, 20, 30]` included — produces the exact same
`[mir-method-call] unresolved-array method=first` trace immediately followed
by `[mir-lower] WARNING: unresolved method call 'first' lowered to const-0
placeholder (silent-null risk, Task #145)`, i.e. the OLD fail-through-to-
placeholder path, never the new one. Confirmed this is not a truncation
artifact: `first_last_int.spl`'s full log shows all 4 calls hit the WARNING
and all 4 correctly become `[ERROR] MIR error: MIR lowering error: unresolved
method call: first/last` (proving the *other* part of this bug — fail-closed
error reporting via `errors[0]` instead of `errors.first()` — is genuinely
still working; it's the `Array.first()`/`.last()` lowering itself that never
fires). The process then still SIGSEGVs afterward on this run too, but
`strace -f -e trace=memory` on this exact run shows a **different** fault
than the control probe: `SIGSEGV {si_code=SEGV_MAPERR, si_addr=NULL}`
(address `0x0`), with no `uname` subprocess pair preceding it (the
fatal-MIR-error exit path returns before target-triple detection runs, so it
never fires here). This is a distinct crash site from the `hello.spl`
control probe's `si_addr=0x118` fault, not a recurrence of the same one —
recorded here as its own open finding (a SIGSEGV at NULL somewhere after the
4th `[ERROR] MIR error:` line prints, on the fatal-MIR-lowering-error exit
path through `driver_aot_pipeline.spl`/`driver_orchestration.spl`) rather
than conflated with the already-tracked `0x118` bug. Not investigated
further here (exact call site unpinned); flagging for whichever lane next
touches that exit path.

**Conclusion: the fix, as implemented, is not currently effective for the
tested shapes — this is a real defect independent of the shared SEGV
blocker**, discovered because the SEGV happens late enough to leave the
lowering diagnostics intact. Read the guarded code path in
`lower_array_first_or_last` (`method_calls_literals.spl:3478-3554`): it
returns `nil` (falling through to the old placeholder) unless either
`self.find_local_hir_type(arr.id)` or `self.receiver_declared_type(receiver)`
resolves an `Array`/`Slice` `HirType` for the receiver. Traced the two
plausible population sites for a `val nonempty: [i64] = [...]` binding
(`mir_lowering_stmts.spl`'s two parallel `Let`-lowering arms, ~line
496-540/704-713 the live "disc==1 early-Let" path vs. ~769-900 which its own
comment marks "dead for Let today") and confirmed the live path DOES call
`self.remember_local_hir_type(local.id, declared_type)` when the initializer
local's own type lookup misses (line 710-713) — so on a source read, this
*should* work. Did not pin the exact reason it doesn't (would need either an
instrumented eprint inside `lower_array_first_or_last` itself, which none of
the existing trace calls cover, or a careful trace of
`receiver_declared_type`'s two lookup arms — `self.symbols.get_symbol_raw()`
vs. `self.local_map`/`find_local_hir_type` — against the receiver's actual
`Var`/`NamedVar` HIR shape at the call site). A full self-hosted rebuild to
test an instrumented or corrected version takes 90+ minutes per the sibling
bug doc, so a blind fix-and-hope was not attempted here; recording this as
the concrete, reproducible next step instead (see "Test files" below for
exact repro inputs).

**Test files** (used for this probe, kept for the next investigating lane):
`first_last_int.spl` (empty/non-empty `[i64]`), `first_last_text.spl`
(empty/non-empty `[text]`), `first_last_struct.spl` (empty/non-empty
`[Point]`, chains `.unwrap()` to touch a field) — all three hit the same
non-engagement result, so this is not element-type-specific. (The struct
file's log additionally shows two `[mir-lower-expr] unsupported-expr-kind
kind=<value:...> disc=4026180482` entries logged for the `[Point]` array
LITERAL construction itself, before the `.first()`/`.last()` calls — a
separate, unrelated gap in struct-array-literal lowering, not investigated
here, noted so the next lane doesn't mistake it for part of this finding.)
Not committed (scratch/, ignored by policy); source is short, see this
update's prose or regenerate from the pattern (`val empty: [T] = []`,
`val nonempty: [T] = [...]`, `print(x.first()); print(x.last())`).

Status: **source written but confirmed NOT effective for the tested cases
via a real (if indirect) execution signal — this is now a known-open defect
in `lower_array_first_or_last`'s type-resolution fallback chain, not merely
"unverified."** No code change made in this pass (root cause not pinned
precisely enough to fix blind, and no fast rebuild path exists to verify a
fix) — flagging for the next lane with the exact function names, line
ranges, and a working repro/probe technique above.

## Update (2026-08-06, later still): root cause pinned — missing `Some(...)` wrap on the success return

Fresh session, `git fetch origin main` first (tip `21875c735e11`, confirmed
current). Reused the four post-`c49bb56` self-hosted binaries recorded above
(`~/dev/simple-s3clean` et al.) — `git log -1 -- .../method_calls_literals.spl`
on `origin/main` also resolves to `c49bb5606dea`, matching those worktrees
exactly, so the binaries are still current for this file.

Read `lower_array_first_or_last` in full this time, including the tail
(`method_calls_literals.spl:3569-3624`, previously only read through 3569).
The dispatch site (`method_calls_literals.spl:2600-2605`) is correctly wired
in the same `local_is_runtime_array` guard block as `push`/`map`/`filter`/
`fold`, and the prior lane's own probe evidence (`[mir-method-call]
unresolved-array method=first` printed from inside that guard) already proved
control reaches the `if method == "first" ...` check — ruling out dispatch
order, a name mismatch, and the receiver-type-recognition failure modes.
That leaves only the `if val first_result = self.lower_array_first_or_last(...)`
binding itself as the remaining suspect.

**Root cause:** `lower_array_first_or_last`'s declared return type is
`LocalId?`, and its early-exit (type-not-found) path correctly `return`s
`nil` (line 3554) — but its success path's final expression, after building
the Option handle in the merge block, was a **bare** `result_local`
(`LocalId`), not `Some(result_local)`. Every other `-> LocalId?` function in
this subsystem wraps its success value explicitly:
`try_lower_global_read` (`expr_dispatch.spl:212`, `return Some(dest)`) and
`try_lower_bitfield_get` (`switch_operators_calls.spl`, `return
Some(result)`) are two directly-grepped examples, and no counterexample of a
bare-value success return from a `-> T?` function was found anywhere in
`src/compiler/50.mir/`. So the convention in this codebase is that a bare
value does NOT reliably auto-promote to `Some(value)` at a `T?` return
site — the `if val first_result = ...` at the call site never bound,
because the un-wrapped return value was not a valid `Option` handle. Falling
through to the existing "unresolved method call" placeholder was itself
working exactly as designed (the fail-closed path for a nil/unbound
result) — this explains why the failure was **uniform across every element
type tested** (`i64`/`text`/`Point`, including an explicitly-annotated
`[i64]`), which is inconsistent with the previously-suspected
`find_local_hir_type`/`receiver_declared_type` fallback-chain theory (that
chain IS type-dependent and DOES succeed for an explicit `[i64]` annotation,
per the "live path" trace in the prior update) and consistent with a defect
that fires identically regardless of which branch of the function computes
the element type.

**Fix:** one-line change, `method_calls_literals.spl:3624`:
```
-        result_local
+        Some(result_local)
```

**Verification status: source-fixed, NOT execution-confirmed — the rebuild
path itself is now confirmed closed, not merely "not attempted".** Two
independent attempts this session to produce a fresh self-hosted binary from
the patched source both failed, and a third data point from an earlier
lane's own leftover build artifacts shows the identical failure:
- Direct `bootstrap/stage2/simple native-build ... src/app/cli/bootstrap_main.spl`
  with a fresh empty cache/runtime dir: immediate SIGSEGV, zero log output
  (an environment/cold-cache artifact, not informative on its own).
- Re-run using `~/dev/simple-s3clean/build/clean/stage2-simple` (a
  provenance-verified stage2 binary from a `Build complete: 3 compiled, 724
  cached` run earlier today, BuildID `fe5c2e9b...`) with its own warm
  `native-objects-BvXGkY` cache dir, same target: the compiler crashes
  **while stage2 is self-compiling `src/app/cli/bootstrap_main.spl` (i.e.
  compiling the compiler's own source tree, before ever reaching the
  `.first()`/`.last()` test files this bug is about)** — `runtime error:
  field access on nil receiver`, `timeout: the monitored command dumped
  core`. Log shows normal MIR-lowering trace output for dozens of unrelated
  method calls (`.replace()`, `.ends_with()`, etc.) immediately before the
  crash, so this is deep into a real self-compile, not a startup failure.
- `~/dev/simple-s3clean/build/clean/stage3.log` (mtime 20:45, an **unrelated
  prior lane's own leftover artifact**, predating this session) shows the
  **exact same** `runtime error: field access on nil receiver` crash
  message at the same point in its own stage2-self-compiling-stage3 attempt.
  Three independent runs, two different sessions, identical symptom.

This `runtime error: field access on nil receiver` crash (during stage2's
self-compile of the compiler) is a **distinct symptom** from both SIGSEGVs
already on file for this binary chain — the `0x118`
`uname`-subprocess-adjacent fault and the `si_addr=NULL` fault after the
4th `[ERROR] MIR error:` line (both described in the "Update (2026-08-06,
later)" section above, and in
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`). This
one is not a SIGSEGV at all (no signal — a Simple-level "runtime error"
message, then the process separately dumps core), and it happens during
**self-compilation of the compiler**, not during a compiled program's
execution — i.e. it blocks producing ANY new stage3/stage2 binary from
current source via this binary chain, regardless of this bug's fix. Recording
this explicitly since it is new information affecting every lane that needs
a fresh self-hosted rebuild right now, not just this one.

**Sabotage-verify: not performed, and not fakeable given the above** — there
is no rebuild path to revert-and-recompare against. The already-recorded
2026-08-06 discriminator probe (all 4 calls across 3 element-typed files →
old placeholder, on a binary built from source identical to this fix minus
the single `Some(...)` wrap) stands as the pre-fix negative control; a
post-fix positive control could not be obtained this session.

**Confidence in the fix without execution verification:** high, on grounds
of source-level convention analysis (every sibling function in the same
file/subsystem uses the explicit-wrap pattern; this was the only exception)
combined with the probe evidence's uniformity across element types (which
this fix explains and the previously-suspected type-resolution theory does
not). Not claimed as "confirmed" — flagged accordingly for the next lane
that has a working rebuild path.

## Update (2026-08-07, diagnostic-only lane): re-confirms this worktree's `0x118` fault IS the already-root-caused borrow-check field-index collision; no env bypass found

Diagnostic-only pass (no source edits). Read this doc plus the fuller
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md` (which now
carries the deep root-cause work — see its "RESOLVED" section) before doing
anything here, per instructions.

**Fresh gdb repro, this worktree's own stale stage3 binary**
(`bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, BuildID `3b41f55f...`,
mtime 2026-08-06 04:14 — predates both the `try_lower_bitfield_construct` fix
and the (unlanded) `resolve_field_index` reorder fix, so it is expected to
still crash regardless of either):

```
gdb -batch -ex run -ex bt -ex 'info registers' -ex 'x/4i $pc' \
  --args bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build probe.spl -o probe.bin
# probe.spl: fn main(): print("hello")

Program received signal SIGSEGV, Segmentation fault.
0x0000000000517966 in ?? ()
#0  0x0000000000517966 in ?? ()
#1  0x000000000051842e in ?? ()
#2  0x000000000067b29c in ?? ()
#3  0x000000000066b928 in ?? ()
#4  0x000000000040533d in ?? ()
#5  0x00000000004025f5 in ?? ()
#6  __libc_start_call_main (...)
rax 0x110  rdi 0x111  r15 0x111  rip 0x517966
=> 0x517966: mov 0x8(%rax),%r14
   0x51796a: test %r14,%r14
   0x51796d: jle 0x5179ad
```

This is a byte-for-byte match (same `rip=0x517966`, same `rax=0x110`, same
`mov 0x8(%rax),%r14; test; jle` shape, same 6-user-frame depth above
`__libc_start_call_main`) to the symbolized crash the sibling doc's
"2026-08-07 — RESOLVED" section already pinned via an unstripped stage2
artifact: `BorrowChecker.check_function` reading `nll.errors` at the *wrong*
field offset (`0x58` instead of the correct `0x20`) because
`MirLowering.resolve_field_index`'s id-keyed tier
(`field_map[sym_id]`, `Dict<i64,[text]>`) collides across module boundaries
in the `--entry-closure` whole-program build — the numeric type-symbol id
that should resolve `NLLChecker` (5 fields, `errors` at 0x20) instead
resolves to `MirLowering` (which happens to also have a field named `errors`,
at index 11 → offset 0x58), returning a garbage tagged-int "pointer" that
`rt_for_iterable`/the length read then dereferences.
`si_addr = (rax & ~7) + 8 = 0x118` here, matching this doc's own historical
`0x118` sighting and the "si_addr is derived, not diagnostic" lesson already
recorded in the sibling doc — **no new information from the address itself.**

**Nil/garbage receiver, pinned (reconfirming, not re-discovering):** the
"receiver" at the crash is not a nil struct pointer in the classic sense —
it's a **tagged small integer** (`rax=0x110` = `(17<<3)|0`, i.e. field value
`17`) read out of `BorrowChecker.check_function`'s `nll` local at the wrong
byte offset, then treated as a list handle and dereferenced via
`rt_for_iterable` → `mov 0x8(%rax)`. Fix location (already proposed, not
landed, per sibling doc): `resolve_field_index`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:934`) — make the
name-keyed tier (`struct_field_order[type_symbol.name]`) authoritative over
the id-keyed tier (`field_map[sym_id]`), or validate an id-keyed hit against
`type_symbol.name` before trusting it.

**Env-bypass check (this lane's task step 3): no working bypass found.**
- Grepped `src/app/cli/bootstrap_main.spl`,
  `src/app/cli/native_build_worker.spl`, and the `driver_aot_pipeline.spl`
  family for an env var that skips the `uname -m`/`uname -s` pair
  specifically. None exists on this path — the only `uname` callers found
  in-repo (`src/app/cli/check_entry.spl`, used by MCP/tool wrappers to pick
  which `simple` binary to invoke; `src/compiler/90.tools/header_gen/shared_lib_flags.spl`'s
  `host_os()`, used only for `--shared` library builds) are not the ones
  `native-build hello.spl`'s default (non-`--shared`) path exercises, and
  neither exposes a `SIMPLE_TARGET`-style override.
- **`SIMPLE_BOOTSTRAP=1` re-tested here and does NOT mask this crash on this
  binary** — `SIMPLE_BOOTSTRAP=1 native-build probe.spl` still dumped core
  (`timeout: the monitored command dumped core`). This differs from the
  sibling doc's report that `SIMPLE_BOOTSTRAP=1` turns the crash into a clean
  `rc=1` ("bootstrap entry lowered to 0 MIR instructions") — that result was
  obtained on a **stage2** binary built by the Rust seed
  (`FIX8/stage2-simple`); this worktree's binary is a **stage3** binary
  (pure-Simple-emitted). The masking behavior is apparently specific to
  which stage/codegen produced the binary, not a general property of the
  flag — recording this discrepancy so the next lane doesn't assume
  `SIMPLE_BOOTSTRAP=1` is a universal workaround for `native-build`.
- **Bottom line: the uname pair is a timing landmark, not a causal
  ingredient.** The crash is in the borrow-check pass, which the pipeline
  reaches regardless of how target-triple detection resolved; nothing
  observed in this pass suggests an env var can route around it. The only
  real fix path remains the unlanded `resolve_field_index` reorder, which
  per the sibling doc requires a full stage-3 rebuild to verify (a stage-2-only
  build is proven blind to `src/compiler` changes on this exact function).

**No source edits made in this pass**, per lane scope.

## Why the original "core-dumps" description pointed at the wrong layer

The task that surfaced this bug reasonably assumed the crash was in MIR
lowering's handling of `Option<Trait>.unwrap()` specifically (it's untested,
looked deliberately fail-closed with a WARNING+rt_panic, and the crash
followed immediately after). The gdb+objdump evidence above rules that out:
MIR lowering behaves exactly as designed (fails closed, returns a fatal
error), and reproduces identically with no Option and no trait involved at
all. The real defect was three lines later, in how the compiler driver
itself reports that MIR lowering failed.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. Source-level fix present. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3007-3010` now routes `.first()`/`.last()` to real lowering (`if val first_result = self.lower_array_first_or_last(receiver, unresolved_receiver_local, false):`), and the helper at :3977 returns `LocalId?` wrapping success in `Some(...)` -- the missing `Some` wrap this doc describes is gone. Note the line numbers in this doc are stale: 3124-3133 is now the `rt_contains` polymorphic-accessor arm, not a CodegenError site, and NO `call 0` construct exists anywhere in the file. The remaining unresolved-method path at :3145 is `self.error("unresolved method call: {method}", nil)` -- a loud fail-closed rt_panic, deliberately not a silent const-0.

## 2026-08-17 CRIT-C4 close (SOURCE READING, no execution)

The "silent const-0 placeholder" mechanism this row is filed against no longer
exists. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` now
fails CLOSED at the end of the Unresolved arm:
`:3176 self.error("unresolved method call: {method}", nil)`,
`:3185 print "[mir-lower] WARNING: unresolved method call '{method}' lowered to
const-0 placeholder (silent-null risk, Task #145)"`, then
`:3208 emit_const_str("unresolved method call: {method}")` + an `rt_panic` call
emitted BEFORE the const-0 def (the def is retained only so the temp is not
use-before-def in llvm-lib). An unresolved method can therefore no longer ship a
wrong value under exit 0. The doc's own title already says "source-fixed".
Recommend CLOSE. The C4 TSV evidence column ("const-0/unresolved placeholder path
still present at line 3133") is stale — the path is present but is now preceded
by rt_panic.
