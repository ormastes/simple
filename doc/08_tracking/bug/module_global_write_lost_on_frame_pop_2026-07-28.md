# Module-level `var` write silently reverted on frame pop (interpreted lane)

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Id:** module_global_write_lost_on_frame_pop_2026-07-28
- **Found:** 2026-07-28, while root-causing `bin/simple lint` reporting
  "all files clean" on files that do not parse (fixed in `f4adc39bf39d`).
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  JIT (cranelift) was already correct.
- **Sibling:** `module_global_write_invisible_to_callee_2026-07-27.md` is the
  *downward* half of the same place-model defect (a write is invisible to a
  callee) and is marked FIXED 2026-07-28 (lane GFIX). This document is the
  *upward* half — the callee's stale snapshot written back over the live value
  on return — and it is **not** fixed by that work.
- **Severity:** HIGH. Silent, and it **inverts safety**: a flag that should read
  "something went wrong" reads "fine". Every affected read is a fail-open gate.
- **Binary used for every measurement below:** `bin/simple` →
  `bin/release/x86_64-unknown-linux-gnu/simple`, which prints
  `WARNING: this Rust-built Simple binary is a bootstrap seed only`. There is no
  deployed pure-Simple binary at the time of writing.

## Summary

A module-level `var` assigned **a constant** inside a callee frame has that
constant **replayed over the live value when an enclosing frame returns**,
silently reverting any write made after it — including writes made much deeper
in the call tree.

The commit message of `f4adc39bf39d` describes this as "not visible to a read
taken after control returns **across a module boundary**". **That
characterization is wrong and this document supersedes it.** Instrumentation
(below) shows the loss at a *single frame pop between two functions in the same
file*, and shows it is *not* a property of the reader at all — it is a property
of an earlier constant-assignment write.

## Reproduction

Repro file (six real syntax errors), written to `/tmp/gvprobe/broken.spl`:

```
fn good() -> i64:
    val x = 1
    x

fn broken( -> i64:
        val y = [1, 2
   y
```

Probe: revert `lint_cli_source()` (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`)
to the two-step form *alongside* the fixed `*_checked` form, so both are
measured in the same run, then `bin/simple lint /tmp/gvprobe/broken.spl`:

```
[gvprobe] two_step=false checked=true self_write=true self_clear=false
```

- `two_step=false` — the defect. `parse_module_silent()` + `parser_has_errors()`
  reports the file parsed cleanly.
- `checked=true` — **control**: the same parse, flag returned by value, correctly
  reports failure. Proves the parse really did fail and the probe executed.
- `self_write=true` / `self_clear=false` — **control**: `parser_set_had_error(v)`
  followed by `parser_has_errors()` *from the lint module* round-trips both
  directions. Proves the accessor pair is not simply broken, and that the reader
  living in another module is not the trigger.

## Where the value is lost

Probes placed inside `src/compiler/10.frontend/core/parser.spl`, gated on the
path so only the repro file is traced. **All reads below go through the accessor
`par_had_error_get()`** — no bare-name reads, so the probes do not perturb the
result:

| Probe | Location | `par_had_error` |
|---|---|---|
| `gvP1` | inside `parser_error()`, right after `par_had_error_set(true)` | `true` |
| `gvP2a` | in `_parse_module_with_diagnostics()`, right after `parse_module_body()` returns | `true` |
| `gvP2b` | same frame, after `parser_diagnostics_suppressed_set(saved)` | `true` |
| `gvP2c` | same frame, **last statement before return** | `true` |
| `gvP3` | in `parse_module_silent()`, **first statement after the call returns** | **`false`** |

The value is lost **at the frame pop itself**, between the last statement of
`_parse_module_with_diagnostics` and the first statement of its immediate caller
`parse_module_silent`. Both functions are in the same file, same module. No
module boundary is crossed at the point of loss.

### Ruled out

- **Import spelling / phantom module prefix.** `parser.spl` imports siblings
  under two different prefixes (`compiler.frontend.core.*` and
  `compiler.core.*`; `src/compiler/core` does not exist on disk). Rewriting all
  32 `use compiler.core.*` to `use compiler.frontend.core.*` **did not change the
  result** — `gvP3` still read `false`. Not a dual-module-instance problem.
- **Cross-module reads in general.** See `self_write`/`self_clear` above.
- **Depth alone.** The write at `gvP1` survives many frame pops (out of
  `parser_error`, back through `parser_decls`/`parser_stmts` frames, into
  `_parse_module_with_diagnostics`) before being lost at one specific pop.

## Root cause (confirmed by injection)

Six extra module-level `var`s of different declaration forms were added to
`parser.spl`, all written by one call from inside `parser_error()`, all read
through accessor functions at `gvP2a` (inside) and `gvP3` (caller):

```
[gvP1]  write  bool=true  i64=2  text=SET  slot=true  sloti=2  arrlen=2
[gvP2a] inner  bool=true  i64=2  text=SET  slot=true  sloti=2  arrlen=2 | flag=true
[gvP3]  caller bool=true  i64=2  text=SET  slot=true  sloti=2  arrlen=2 | flag=false
```

**All six survive the pop that loses `par_had_error`.** The loss is therefore not
a property of the type, nor of the frame pop as such.

The distinguishing property: `parser_init_with_path()` — called near the *top* of
`_parse_module_with_diagnostics`, i.e. an **earlier callee of the frame that
loses the value** — contains `par_had_error = false`. The injected probe vars had
no such reset.

Adding exactly that reset for two of the probe vars inside
`parser_init_with_path` reproduces the loss for them and only them:

```
# added to parser_init_with_path: gvt_scalar_bool = false ; gvt_slot[0] = false
[gvP2a] inner  bool=true  i64=2 text=SET slot=true  sloti=2 arrlen=2 | flag=true
[gvP3]  caller bool=false i64=2 text=SET slot=false sloti=2 arrlen=2 | flag=false
                 ^^^^^                        ^^^^^
```

`gvt_scalar_bool` and `gvt_slot[0]` now revert exactly like `par_had_error`. The
untouched forms (`i64` counter, `text`, `[i64]` slot counter, growable `[i64]`)
still survive.

**Rule:**

> If a callee of frame **F** assigns a module-level `var` a value, that value is
> copied into **F**'s environment. Writes made to that global *after* the callee
> returns — at any depth below F — are made to the live module environment but
> not to F's copy. When **F** returns, F's stale copy is written back over the
> live value.

This is a copy-in/copy-out place model where the write-back is load-bearing.
It is consistent with the previously recorded interpreter finding that "two-hop
loss is a place-model problem and write-back is load-bearing" — this document is
that same defect observed on module globals rather than locals, with the
triggering condition now pinned.

It also explains the observation that converting `par_had_error` to the
single-element slot-array idiom did not help: `par_kind_slot`-style resets
(`X_slot[0] = false`) copy **the whole cell** into F's environment, so the whole
cell is restored. Confirmed above — `gvt_slot` fails identically to
`gvt_scalar_bool`.

## Truth table

Write made deep in a call tree, read after the enclosing frame `F` returns.
"Reset in a callee of F" means some callee of F assigns the same global a value
before the deep write happens.

| Declaration form | Reset in a callee of F? | Survives F's return |
|---|---|---|
| `var x: bool` | no | **yes** |
| `var x: bool` | yes | **NO — silently reverted** |
| `var x: i64` (counter, `x = x + 1`) | no | **yes** |
| `var x: i64` (counter) | yes (`x = 0`) | **NO** (`par_diagnostic_emit_count` read back `0` after six increments) |
| `var x: text` | no | **yes** |
| `var x: text` | yes (`x = ""`) | **NO** |
| `var x: [bool]` single-element slot, `x[0] = v` | no | **yes** |
| `var x: [bool]` single-element slot, `x[0] = v` | yes (`x[0] = false`) | **NO — whole cell restored** |
| `var x: [i64]` growable, `x = x.push(v)` | no | **yes** |
| `var x: [i64]` growable, `x = x.push(v)` | yes (`x = []`) | **NO** |
| return the value from the function | n/a | **yes — reliable** |
| `rt_env_set` / `rt_env_get` process-global mirror | n/a | **yes — reliable** |

Reader location (same module vs. another module) does **not** affect any row.

### Engine differences

`SIMPLE_EXECUTION_MODE` selects the engine. `bin/simple run` defaults to the
**JIT**; the lint/spec lanes execute on the **interpreter**.

| Lane / engine | Result |
|---|---|
| `SIMPLE_EXECUTION_MODE=jit` (default for `bin/simple run`) | **CORRECT** — every form survives |
| `SIMPLE_EXECUTION_MODE=interpreter` | **BROKEN** — reproduces every time |
| `bin/simple lint` (interpreted lane) | **BROKEN** — the original symptom |
| Seed *Rust* parser (`bin/simple run` / `compile` on the repro file) | **CORRECT** — rejects at exit 1; a different code path entirely |
| native codegen | **not measured** — `bin/simple native-build` on the repro file fails first for an unrelated reason (`error[E1002]: function 'source_file_coverage_identity' not found`) |

This is why four earlier standalone probes appeared to pass: they were run under
the default JIT. Always pass `SIMPLE_EXECUTION_MODE=interpreter` when probing
this defect.

## Minimal reproduction (self-contained)

Three files. `a_init()` is a callee of `a_inner()` and resets the `r_*` group;
the `n_*` group is never reset and acts as the in-run control.

`amod.spl`:

```
use bmod.{b_body}

# RESET group: a_init() assigns each a constant
var r_bool: bool = false
var r_i64: i64 = 0
var r_text: text = ""
var r_slot: [bool] = [false]
var r_arr: [i64] = []
# NO-RESET group: never touched by a_init()
var n_bool: bool = false
var n_i64: i64 = 0
var n_text: text = ""
var n_slot: [bool] = [false]
var n_arr: [i64] = []

fn a_init():
    r_bool = false
    r_i64 = 0
    r_text = ""
    r_slot[0] = false
    r_arr = []

fn a_set():
    r_bool = true
    r_i64 = r_i64 + 1
    r_text = "SET"
    r_slot[0] = true
    r_arr = r_arr.push(7)
    n_bool = true
    n_i64 = n_i64 + 1
    n_text = "SET"
    n_slot[0] = true
    n_arr = n_arr.push(7)

fn a_report(tag: text) -> text:
    tag + " | RESET bool=" + r_bool.to_text() + " i64=" + r_i64.to_text() + " text=[" + r_text + "] slot=" + r_slot[0].to_text() + " arr=" + r_arr.len().to_text() + " || NORESET bool=" + n_bool.to_text() + " i64=" + n_i64.to_text() + " text=[" + n_text + "] slot=" + n_slot[0].to_text() + " arr=" + n_arr.len().to_text()

fn a_inner():
    a_init()
    b_body()
    print(a_report("P2 inner "))

fn a_outer():
    a_inner()
    print(a_report("P3 caller"))
```

`bmod.spl`:

```
use amod.{a_set}
fn b_body():
    b_deep()
fn b_deep():
    a_set()
```

`main.spl`:

```
use amod.{a_outer, a_report}
fn main():
    a_outer()
    print(a_report("P4 main  "))
```

Run:

```
for m in jit interpreter; do
  echo "=== $m ==="
  SIMPLE_EXECUTION_MODE=$m bin/simple run main.spl
done
```

Measured output:

```
=== jit ===
P2 inner  | RESET bool=true i64=1 text=[SET] slot=true arr=1 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
P3 caller | RESET bool=true i64=1 text=[SET] slot=true arr=1 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
P4 main   | RESET bool=true i64=1 text=[SET] slot=true arr=1 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
=== interpreter ===
P2 inner  | RESET bool=true i64=1 text=[SET] slot=true arr=1 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
P3 caller | RESET bool=false i64=0 text=[] slot=false arr=0 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
P4 main   | RESET bool=false i64=0 text=[] slot=false arr=0 || NORESET bool=true i64=1 text=[SET] slot=true arr=1
```

`P2` (inside `a_inner`) is correct for both groups — the deep write landed.
At `P3`, one frame pop later, **every form in the RESET group reverts to the
value `a_init()` wrote**, while the NO-RESET group survives untouched. The
NO-RESET group is the in-run control: it proves the probe executed and that the
defect is not "globals don't survive returns".

## Blast radius

`grep -rn --include=*.spl -E '^var [a-zA-Z_]' src/` → **2848** module-level vars
(src/lib 1214, src/os 802, src/compiler 611, src/app 163, src/runtime non-vendor
14). **227** match the high-consequence name filter.

Only a var that is (a) reset to a constant by some callee and (b) written again
deeper and read after the enclosing frame returns is at risk. Ranked candidates,
by consequence:

### Confirmed broken

1. **`src/compiler/10.frontend/core/parser.spl:76` `par_had_error: bool`** —
   measured above. Reset at `parser_init_with_path` (:241), written at
   `parser_error` (:266) / `parser_expect` (:276), lost at
   `_parse_module_with_diagnostics`'s return.
   - `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:40` — **was**
     broken (lint fail-open); fixed in `f4adc39bf39d` by
     `parse_module_silent_checked()`.
2. **`parser.spl:78` `par_diagnostic_emit_count: i64`** — reset at :243, read
   back `0` after six increments. Same mechanism; any diagnostic-count gate
   built on it is dead.

### High risk, same shape, NOT yet probed

3. **`src/compiler/80.driver/driver.spl:680`** reads `par_had_error_get()` to
   fail phase 2 on a parse error — the "silent wrong binary" gate. Its inline
   comment says the accessor form is the mitigation; **the measurements above
   show the accessor is not sufficient**, so this gate is likely still fail-open.
   Not probed directly because `bin/simple native-build` on the repro file dies
   earlier for an unrelated reason. **Highest-value follow-up.**
4. **`src/compiler/70.backend/backend/compile_c_entry.spl:574`**
   `parser_has_errors()` — read in the *same frame* as `parse_module_body()`,
   with no intervening pop, so it matches the surviving `gvP2a` case and is
   probably fine. Note separately that its `parser_get_errors()` is a stub
   returning `[]` (`parser.spl:882`) and `parser_error_count()` returns `0`
   (:885), so the error report it prints is empty regardless.
5. **`parser.spl:77` `par_diagnostics_suppressed: bool`** — reset at :242,
   save/restore across speculative parse at
   `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:513-514`. A stale
   read leaks or swallows diagnostics.
6. **`src/compiler/10.frontend/core/interpreter/eval.spl:178` `eval_had_error`** —
   no accessor at all; bare-read from ~40 sites across `_EvalOps/*`,
   `eval_decls.spl`, `eval_builtins.spl:584-591` (save/restore).
7. **`src/compiler/35.semantics/comptime_checker.spl:22` `checker_error_count`** —
   before/after delta computed at :144-147 around a call tree: exactly the
   failing shape.
8. **`src/compiler/10.frontend/core/type_inference.spl:91` `unify_error_msg`** —
   set deep in `unify` (:106/:112/:117), read via getter at :94.
9. **`src/os/services/nvfs/driver/fs_driver_impl.spl:25` `_verify_on_read: bool`** —
   setter :29, getter :33, gate at :246. A stale `false` silently skips
   filesystem read verification.
10. **`src/lib/nogc_sync_mut/sanitizer/{asan,tsan,lsan,msan}/mod.spl` `g_*_enabled`** —
    each gates 6-8 early returns. A stale `false` silently disables the sanitizer.
11. **`src/os/kernel/boot/zstd_noalloc.spl:70` `g_zstd_error_code: u64`** — 10+
    write sites in the decompress tree; boot-time truncation would read `ZSTD_OK`.
12. **`src/compiler/85.mdsoc/adapters/in/language_server_adapter.spl:9`
    `_ls_error_count`** — LSP diagnostic count.
13. **`src/lib/nogc_sync_mut/coverage.spl:34/37`**, **`mcdc.spl:79/83/84`** —
    `_*_data_loaded` / `_*_last_error` guards.
14. **`src/os/kernel/arch/riscv64/boot_info.spl:34` `g_dtb_valid_cached`** —
    written :72, read :154/:192.
15. **`src/lib/log.spl:527` `_g_panic_mode`**, **`src/lib/nogc_sync_mut/src/aop.spl:285-286`
    `_aop_proceed_err`/`_aop_proceed_had_err`**.

### Already-attempted-and-failed mitigations (do not trust)

Every existing single-element slot-array global in the codebase is an instance
of the idiom that **does not work**: `parser.spl` `par_kind_slot` /
`par_text_slot` / `par_line_slot` / `par_col_slot`, `lexer.spl:56`
`lex_env_save_enabled: [bool]`, `g_msan_initialized: [bool]`,
`ast_decl_mode_slot`, and the `_gpu_compositor_override_*` family in
`src/os/compositor/display_backend.spl:6-10` (whose neighbour
`background_image_provider.spl:181-184` explicitly documents them as the
workaround for "the interpreter bug"). Treat all of these as unprotected.

## Known-good workarounds

1. **Return the value.** The only form that never touched the module environment
   is a return value. This is what `parse_module_silent_checked()`
   (`parser.spl:850`) does and it is the preferred fix.
2. **`rt_env_set` / `rt_env_get` process-global mirror.** Survives because it
   lives outside the environment model. Used by `par_had_error_mirror_*`
   (`parser.spl:178-185`) and, pre-existing, by `par_line`/`par_col`. Cost is one
   `getenv`/`setenv` per write — acceptable only on cold paths.

**Does NOT work:** the single-element slot-array idiom (`var x: [bool] = [false]`,
`x[0] = v`). The whole cell is restored, so it fails identically to the scalar.
This is the intuitive fix and it is wrong — see the truth table.

## Recommended fix

Not landed here (characterization was the deliverable), but the defect is
**localized and the fix is identifiable**, because the sibling lane already
mapped this code.

All of it lives in
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`:

- `captured_env_with_live_globals()` builds a callee env by copying the owner
  module's globals into the frame's `Env` **overlay**.
- `sync_owned_captured_globals()` writes that overlay back into
  `MODULE_GLOBALS_BY_OWNER` / `MODULE_GLOBALS` **on return**.

Lane GFIX (2026-07-28) fixed the *entry* direction by adding
`publish_live_owned_globals()` at the five `exec_function_*` entry points, so a
callee no longer copies a stale value **in**. The *return* direction was not
touched: `sync_owned_captured_globals()` still writes back **every** overlay
entry the frame holds, including entries the frame has not written since a
deeper frame published a newer value. That unconditional write-back is the
clobber measured above.

Two candidate fixes, in increasing order of correctness:

1. **Cheap and targeted:** make the return-side sync conditional. Stamp each
   published global with a monotonic generation counter; on return, write back
   an overlay entry only if the frame's copy is at least as new as the owner
   map's. This is a small change confined to the two functions above and mirrors
   the predicate `publish_live_owned_globals` already uses. It is the change to
   try first.
2. **Correct end state:** option (c) from the sibling doc — shared
   `Rc<RefCell<Value>>` global slots, so there is no per-frame copy to go stale
   and no write-back at all. The sibling doc already names this as the right
   follow-up; this defect is the second piece of evidence that copy-in/copy-out
   cannot be made correct by adding publish points one direction at a time.

Until one lands, interim guidance for authors:

- Do not read a module-level `var` as an out-of-band status channel across a
  function return. **Return the value.**
- If a global must be a status channel, mirror it through `rt_env_set`.
- Do not "fix" such a site by wrapping it in a one-element array.
- Any regression test for this must run under
  `SIMPLE_EXECUTION_MODE=interpreter`; the JIT passes and will hide it.

## 2026-07-28 fix and Retry 10 evidence

Retry 10 rebuilt current Rust authority, passed Stage 2 and Stage 3 sanity and
source attestation, then reproduced the defect in Stage 4 despite
`SIMPLE_NATIVE_ARENA_DECLS=1` being present in `/proc/<pid>/environ`. It
released 1,277 surfaces, emitted 15,483 stale flat-AST diagnostics, and then
lost `ctx.module_surfaces` at the Phase-2 frame return. The run took 64m57s,
peaked at 2,649,080 KiB RSS, and performed zero swaps. Stage 2 SHA-256 was
`3aa6334770a6ac18e3bc145990e6b27e5013da7f77caa5d4d67853e2220d3a77`;
Stage 3 SHA-256 was
`bd09bf6247475863d5ddddc47613de25554ba9b6c7c194b03dbbae8c128eda7b`.

The return-side fix gives each `CowEnv` frame a set of owner globals refreshed
from callees. Refreshed values stay readable but are excluded from that
frame's later owner-global write-back. Owner-qualified updates are forwarded
through intervening foreign-module frames and refreshed when they reach their
owner's caller. Every mutation API (`insert`, `extend`,
`entry`, `get_mut`, `remove`, and `clear`) clears the corresponding provenance,
so a real caller assignment or copy-on-write array mutation still publishes.
This is the minimal per-frame clean/dirty model; it avoids generation storage
while preserving the current synchronous thread-local interpreter semantics.

The focused Rust unit regression proves a newer callee scalar survives, a real
caller overwrite wins, and an array mutation is published. The end-to-end
interpreter regressions reproduce deeper writes across same-owner frames, an
`A -> B -> A` callback, and an ownerless nested wrapper. The serialized
`interpreter_flattened_module_globals` suite passes all 21 tests. A new strict bootstrap is still required to rebuild the authority
and prove zero stale-index diagnostics plus retained streaming surfaces.

## 2026-07-28 Retry 11 evidence

Retry 11 rebuilt the pushed Rust authority at `a7b53d603fc0`, passed Stage 2
sanity, Stage 3 sanity/provenance, and the Stage 2 native capability gate, but
the Stage 4 admission still failed. The first stale statement read appeared
after surface 374 at `idx=6783` with `arena_len=101`. The run released 1,278
surfaces, emitted 10,292 OOB reads and 5,146 missing-tag diagnostics, then
reported `n_modules=0` and `Streaming module surfaces missing after phase 2`.

This disproves the provenance-only repair as a complete Stage 4 fix. The run
took 51m55s, peaked at 2,650,944 KiB RSS, and used zero swap, so the remaining
failure is semantic state ownership/order rather than memory exhaustion. Stage
2 SHA-256 was
`e29146d77f45a71e4c7c36e8ad727ba6a6f2f76487c011c1e74dd4af65bda827`;
Stage 3 SHA-256 was
`ecfa4b16745732c8d25ee66e09d4189ba5322f259552d253f672e321cd4b20ae`.
Do not run Retry 12 until the remaining arena/context ownership path has a
focused failing regression and root fix.

The focused root trace identified imported-global ownership loss: function
capture copied imported aliases as bare `(local_name, Value)` pairs, while
return sync inferred ownership only from the executing module. Consequently,
`ast_reset()` successfully reset its owned statement arena but discarded clears
of declaration pools imported from `decl_nodes.spl`, producing the exact stale
declaration-body/new-statement-arena mismatch.

`CowEnv` now retains each global binding as
`local_name -> (defining_owner, source_name)`. Entry capture records owned and
imported bindings, locals remove inherited bindings when they shadow a name,
and return sync writes dirty aliases to the defining owner. The new two-module
parallel-arena regression reproduces a stale declaration index against a reset
statement arena and now passes. The serialized module-global suite passes all
25 tests. The five core entry paths publish dirty owner-qualified bindings
before capture; forwarded updates refresh matching imported aliases; block and
function-parameter shadows relay rather than discard packets. Retry 12 remains
postponed pending review and the remaining method/
lambda frame-lifecycle work; this focused pass alone is not Stage 4 admission.

## Related

- `f4adc39bf39d` — lint fail-open fix (workaround at one site).
- `scripts/check/check-lint-rejects-unparseable.shs` — regression guard, both
  directions.
- `doc/08_tracking/bug/lint_does_not_detect_syntax_errors_2026-07-28.md` — the
  symptom this defect was found under.
- `.claude/memory` interpreter place-model / "two-hop loss, write-back is
  load-bearing" notes — same defect class.
