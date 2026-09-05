# Prelude builtins (`exit`, `eprint`, `dprint`) are silently rebindable by a transitively imported top-level `fn`

- **Date:** 2026-08-10
- **Status:** PARTIALLY FIXED (2026-08-10, commit `d21332ede1f`) — `exit` is
  fenced in both lanes and every shadow now warns. The general hazard (the other
  50 user-facing prelude names remain shadowable, by an explicit and now-stated
  policy) is still OPEN. The one live instance (`eprint`) is
  fixed in
  `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`;
  the mechanism that allowed it is not.
- **Lanes:** `interpreter`, `jit`, and **`native` (still OPEN — see the Q34
  update at the bottom: `simple native-build` uses the pure-Simple HIR lowering,
  which has its own builtin list and honours neither `PRELUDE_UNSHADOWABLE` nor
  the Rust whitelist, so `exit` is NOT fenced in the lane that ships binaries).**
- **Class:** silent semantic hijack / name resolution.

## Mechanism

`src/compiler_rust/compiler/src/interpreter_call/mod.rs:358-410`, `evaluate_call`:

```rust
// Priority 1: Check extern functions first (before builtins)
let has_local_def = is_extern
    && (functions.contains_key(name.as_str())
        || FUNCTION_OVERLOADS.with(|c| c.borrow().contains_key(name.as_str())));
if is_extern && !has_local_def { /* extern/builtin dispatch */ }

// Priority 2: Try built-ins (before user functions, so builtins can't be shadowed)
```

The `has_local_def` escape hatch was added deliberately, for
`rt_array_len_safe`: a pure-Simple helper whose name coincidentally matched a
runtime export had to win over the coincidental extern registration
(`seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`).

But **prelude builtins are registered in the same `EXTERN_FUNCTIONS` set**
(`interpreter_eval.rs:232` `PRELUDE_EXTERN_FUNCTIONS`, which lists `print`,
`eprint`, `dprint`, `exit`, `panic`, `input`, …). So the hatch applies to them
too, and the reassuring comment on the line below — *"before user functions, so
builtins can't be shadowed"* — is **false** for every prelude name Priority 1
reaches. A single top-level `fn exit` anywhere in a module's transitive import
closure silently rebinds `exit` for the whole program.

## Measured family

Synthetic 2-level transitive import (`main` → `mid` → `lib` defining the name),
`bin/simple`, both lanes:

| builtin | rebindable? | observed |
|---|---|---|
| `exit` | **YES** | user `fn exit` ran; `exit(0)` **did not terminate the process** |
| `dprint` | **YES** | user `fn dprint` ran |
| `eprint` | **YES** | real instance, see the linked bug |
| `print` / `println` | no | parser resolves the statement form ahead of call dispatch |
| `panic` | no | real panic fired; the user `fn panic` never ran |

`print`, `println` and `panic` are protected only by a **syntax accident** —
they have a statement form the parser handles before name resolution. That is
not a policy and it will not protect any prelude name added later.

## Why `exit` is the dangerous one

There are **12** top-level `fn exit` definitions in `src/`
(`src/app/io/cli_ops.spl:342`, `src/app/io/signal_handlers.spl:11`,
`src/lib/nogc_sync_mut/io/signal_handlers.spl:11`,
`src/compiler/70.backend/baremetal/link_wrapper.spl:296`, …). Any program whose
import closure reaches one of those and then calls bare `exit(code)` gets that
function instead of process termination — the program keeps running, and the
exit code is whatever `main` falls through to. That is a false-GREEN generator
for any harness that reads exit status.

## Why it is not fixed here

The obvious fix — move Priority 2 (builtins) ahead of Priority 1's
`has_local_def` fallback, or exclude `PRELUDE_EXTERN_FUNCTIONS` from the hatch —
directly re-opens the `rt_array_len_safe` regression, and it is a
name-resolution semantics change in the seed interpreter affecting every call
site in the compiler. It needs its own change with its own bootstrap
verification, not a drive-by inside a logging fix.

Preferred shape when it is done:

1. Split the two sets. The hatch should key on *coincidental runtime-symbol
   registration* (the `rt_*` manifest bulk-seed that motivated it), **not** on
   `PRELUDE_EXTERN_FUNCTIONS`. A prelude builtin should never be silently
   rebindable.
2. If a module genuinely needs its own `exit`/`eprint`, it should have to say so
   — a shadow of a prelude name should at minimum **warn** at load, naming both
   the builtin and the shadowing definition, the way the seed already warns for
   `compiler_cross_module_private_symbol_collision`.
3. Audit the 12 `fn exit` definitions: most look like they want a distinct name.

## Next step

Land (2) first — the load-time warning is cheap, non-breaking, and turns every
remaining instance of this class from silent into visible, which is what the
`eprint` case needed and did not have for months.

## Related

- `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
- `doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`
- `scripts/check/check-eprint-reaches-stderr-fd.shs`


---

# Update 2026-08-10 — full sweep, `exit` fixed, policy chosen

## What changed (commit `d21332ede1f`)

`exit` is now **unshadowable in both lanes**, and every remaining prelude shadow
**warns once** naming the builtin and the shadowing definition. Guarded by
`scripts/check/check-prelude-builtins-unshadowable.shs`.

**Reproduction (before).** `main.spl` imports only `mid_helper` from `q29mid`,
which imports only `helper` from `q29lib`; `main` never names `exit`, and
`q29lib` defines `pub fn exit`:

```
BEFORE code=42
SHADOW_EXIT_RAN code=3
AFTER_EXIT_STILL_RUNNING      <-- process did not terminate
EXITCODE=0                    <-- and reported success
```

**After:** the shadow does not run, `AFTER_EXIT_STILL_RUNNING` is absent, and
`EXITCODE=3`, with a warning naming the shadowing `fn exit`.

## The hole had TWO independent causes

The predecessor analysis named only the first. Fixing either alone leaves the
defect live, which is why the guard probes both lanes:

1. **Interpreter** — the Priority-1 `has_local_def` escape hatch in
   `interpreter_call/mod.rs`, as originally diagnosed.
2. **JIT / native** — `hir/lower/expr/calls.rs` recognizes builtins by an
   **explicit whitelist**. `exit` was simply absent from it, so it fell through
   to ordinary function resolution. This also explains the JIT column below
   exactly: the names that resisted shadowing in the JIT lane are precisely the
   ones that whitelist mentions.

The bug doc's claim that `print`/`println`/`panic` are protected by a
"parser statement-form accident" is **wrong**. They are protected by that HIR
whitelist, and only in the JIT lane — in the interpreter, called in
**expression position** (`val r = println(1)`), `println` and `panic` are both
shadowable. Only `print` resisted in both lanes.

## Prelude x lane shadowability (measured, all 51 user-facing names)

Probe: 3-module transitive import as above; SHADOWABLE = the user `fn` ran.
JIT `safe` verdicts were positive-controlled (the builtin demonstrably ran:
`abs(1)`=1, `panic` really aborted) so "safe" never means "the program errored".
Runs that emitted `[jit-fallback]` are reported as such, never credited as JIT.

| lane | shadowable | safe |
|---|---|---|
| interpreter | **50 / 51** | `print` only |
| JIT | **43 / 51** | `print`, `print_raw`, `eprint`, `eprint_raw`, `input`, `println`, `eprintln`, `abs`, `panic` |

`dprint` is shadowable in **both** lanes. After this commit `exit` is safe in
both. Native lane not separately measured — it shares the HIR lowering path
with JIT, so the JIT column is the governing signal there; confirming it is
follow-up work.

## Policy chosen: fence process control, warn on the rest

Rejected: making all prelude names unshadowable. **22 of the 51 names already
have 102 top-level definitions in `src/**`** (inventory:
`prelude_shadow_inventory_2026-08-10.txt`) — `exit` 16, `min` 10, `abs` 8,
`sqrt`/`max`/`format_bytes` 7 each, and so on. Silently retargeting all of them
to builtins is a semantic change across the whole tree that cannot be verified
in one commit, and it would change baremetal behaviour (`os/kernel/arch/*/cstart.spl`
maps `exit` to `__spl_exit`, not to host process exit).

Adopted instead:
- **`PRELUDE_UNSHADOWABLE`** (currently `exit`) — always dispatches to the
  builtin. Justified for `exit` specifically because a shadowed `exit` is a
  false-GREEN generator, and because it is behaviour-preserving: all 16 live
  `fn exit` definitions in the host lanes delegate to `rt_exit` already, and the
  baremetal `cstart.spl` variants are never interpreted.
- **Everything else stays legal but is loud** — one warning per name, naming the
  builtin and the shadowing definition's line, silenceable with
  `SIMPLE_NO_PRELUDE_SHADOW_WARNING=1`. This is what the `eprint` incident
  needed and did not have for months.
- The `rt_*` escape hatch that motivated the whole mechanism is untouched:
  `is_user_facing_prelude` excludes `rt_*` / `compiler__*`, so
  `rt_array_len_safe` still wins over its coincidental extern registration.

This is a Rust-layer fix, against the repo's usual fix-in-`.spl` rule, because
the defect is in the seed interpreter's dispatch and in HIR lowering — there is
no `.spl` site to fix.

## Existing shadows: disposition

All 16 `fn exit` definitions delegate to `rt_exit` (or, in baremetal,
`__spl_exit`), so none of them was causing live non-termination — the fenced
builtin now makes that structural rather than incidental. The remaining 86
shadows across 21 other prelude names are **not yet triaged individually**; they
are now visible via the warning rather than silent, which is the point of the
policy. Triage remains open work and is the reason this bug is not closed.

## Verification

- Check: `scripts/check/check-prelude-builtins-unshadowable.shs`
  (`SIMPLE_BIN=<path>`), verdict line last, negative control included.
- Fixed binary (built to a private `CARGO_TARGET_DIR`, not the shared `target/`):
  `PASS — 3 probes checked`.
- **Revert-proof:** the same check against a binary predating the fix
  (`bin/release/x86_64-unknown-linux-gnu/simple`, Aug 9 04:50) reports
  `FAIL — [interpret]` and `FAIL — [jit]`, with the negative control still
  firing — so the PASS is caused by the fix, not by a broken harness.

---

# Update 2026-08-10 (Q34) — native lane measured, triage, fence recommendations

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple`, size 29577536,
mtime **2026-08-09 04:50:31 UTC** (the deployed, fix-free seed). Read/invoke
only. `src/compiler_rust/target/release/simple` was NOT used (broken).

## 1. The native/AOT lane does NOT share the JIT whitelist — measured, not inferred

The previous update inferred *"Native lane not separately measured — it shares
the HIR lowering path with JIT, so the JIT column is the governing signal
there."* **That inference is wrong.** There are two distinct native paths:

| path | HIR lowering | whitelist |
|---|---|---|
| Rust `pipeline/native_project/mod.rs:1251`, `linker/native_binary/result.rs:43` | `crate::hir::lower*` | shares `hir/lower/expr/calls.rs` (JIT's) |
| **`simple native-build` (the lane that ships binaries)** | `src/compiler/20.hir/` (pure-Simple) | **its own, different list** |

Provenance proof that `native-build` uses the pure-Simple lane: its diagnostic
string `HIR lowering error in <name>: <msg>` is emitted by
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:42-44`, not by any
Rust `LowerError` formatter.

The pure-Simple lane's builtin set is `is_interp_builtin_fn` in
`src/compiler/20.hir/hir_lowering/expressions.spl:50-58`:
`print, println, to_string, type_of, clone, file_exists, file_read, file_write,
file_delete, env_get, env_set, int, float, bool, panic, str, text`.
It contains **no `exit`**, no `PRELUDE_UNSHADOWABLE`, and no overlap with the
`abs|min|max|sqrt|floor|ceil|pow|to_int` group the Rust whitelist carries.

## 2. Prelude x native lane — all 51 user-facing names

Method (two probes, compile-stage; the AOT back half cannot be used as an oracle
here — `llc failed (exit 1)` even for `print 0`, and interpolated `print` with a
call is silently dropped in native, so stdout is not a valid oracle):

- **Control** `nat_ctl.spl`: one file calling all 51 names bare, no shadow
  anywhere. A name the lane recognises as a builtin lowers; a name it does not
  hard-errors `unresolved name: <n>`.
- **Positive control / shadow probe** `nat_shadow.spl`: identical calls, but a
  3-module transitive import (`main` -> `natmid` -> `natlib`) where `natlib`
  defines all 51 as `pub fn <n>(a: i64) -> i64`. `main` imports only
  `q34_mid` and never names `natlib`.

Result:

| lane | shadowable (name has NO builtin binding, shadow is the only binding) | builtin-bound |
|---|---|---|
| interpreter (prior) | 50 / 51 | `print` |
| JIT (prior) | 43 / 51 | `print print_raw eprint eprint_raw input println eprintln abs panic` |
| **native (`native-build`)** | **47 / 51** | **`panic`, `print`, `println`, `to_string`** |

The 47 unresolved in the control: `abs arc_box_dec_strong arc_box_dec_weak
arc_box_drop_value arc_box_get_value arc_box_inc_strong arc_box_inc_weak
arc_box_init arc_box_size arc_box_strong_count arc_box_weak_count ceil
default_memory_limit dprint eprint eprintln eprint_raw exit floor format_bytes
input is_memory_limited max memory_limit memory_usage memory_usage_percent min
parse_memory_size pow print_raw rc_box_dec_strong rc_box_dec_weak
rc_box_drop_value rc_box_get_value rc_box_inc_strong rc_box_inc_weak rc_box_init
rc_box_size rc_box_strong_count rc_box_weak_count size_of sizeof sqrt sys_free
sys_malloc sys_realloc to_int`.

Positive control fired cleanly: with the shadow module in the closure,
**0 of 51** are unresolved — every one of those 47 names resolved to the
transitively imported `fn`. So the shadow is demonstrably supplying the binding;
"unresolved" is not a probe artefact.

### The fix does not cover the lane that ships binaries

**`exit` is in the unresolved-47.** `PRELUDE_UNSHADOWABLE` lives in
`interpreter_eval.rs` and is honoured by the Rust interpreter and
`hir/lower/expr/calls.rs`. `simple native-build` consults neither. A transitively
imported `fn exit` therefore still wins dispatch in a natively built binary —
the exact false-GREEN generator the fix was written to close. The bug's claim
that `exit` is *"fenced in both lanes"* is accurate for the two lanes measured
and **false for native**. This is filed as follow-up, not fixed here: the pure-
Simple fence cannot be an unconditional copy of `PRELUDE_UNSHADOWABLE`, because
`src/os/kernel/arch/*/cstart.spl` deliberately maps `exit` to `__spl_exit` and
those modules are compiled by exactly this lane. It needs a target-conditional
fence plus bootstrap verification.

## 3. Triage of the 86 non-`exit` shadows

Classification of the 102-entry inventory minus the 16 `exit` entries.

| class | count | disposition |
|---|---|---|
| LEGITIMATE — target/tier prelude implementation | 39 | keep |
| LEGITIMATE — documented, already-fixed shadow | 5 | keep |
| ACCIDENTAL / semantics-divergent | 42 | 1 fixed here, 41 filed |

**LEGITIMATE — target/tier implementation (39).** `src/compiler_rust/lib/std/src/bare/io/serial.spl`
(`print`, `println`), `.../bare/startup.spl` (`panic`), `.../host/async_gc_immut/io/term.spl`
and `.../host/async_nogc_mut/io/term.spl` (`print println eprint eprintln input`),
`.../core/math.spl` and `.../gpu/kernel/math.spl` (`abs min max sqrt floor ceil pow`
as f32/GPU intrinsics), `src/runtime/simple_core/{core_string,core_process}.spl`
(`print_raw`, `panic` — these ARE the runtime), and the nine
`src/lib/*/allocator.spl` `sys_malloc`/`sys_free`/`sys_realloc`. These are the
`exit`->`__spl_exit` case generalised: a target where the host builtin does not
exist supplies its own.

**LEGITIMATE — already fixed and documented (5).** `eprint` in
`src/app/io/process_ops.spl:464` and `src/lib/nogc_sync_mut/io/process_ops.spl:558`,
and `eprintln` in the three `io/mod_stub.spl`. All five now call
`rt_stderr_write` and carry an explicit "do not reintroduce a `print` fallback"
comment from the `eprint` fix. Keep.

**ACCIDENTAL / semantics-divergent (42) — the wrong-answer set.** These are
independent reimplementations, not target overrides, and several diverge from
the builtin in domain or return type:

- `abs`/`min`/`max` (i64) in the three `src/lib/*/runtime_wrappers.spl` — and
  these are **re-exported by the tier facade**: `src/lib/nogc_sync_mut/__init__.spl:351`
  reads `export clamp, min, max, abs`. Any module importing the tier gets an
  i64-only `min`/`max`/`abs` in place of the builtin. This is the widest-reach
  entry in the inventory.
- `sqrt(n: i64) -> i64` at `src/app/interpreter/perf/benchmark.spl:535` — integer
  sqrt, own docstring says *"(placeholder)"*. Domain divergence.
- `sqrt(z)` at `src/lib/common/complex/exponential.spl:55` — complex domain,
  arity 1, collides with the real builtin.
- `floor`/`ceil` in `core/math.spl` return **`i32`** where the builtin returns a
  float — return-type divergence.
- `parse_memory_size` x2 with **incompatible return types**
  (`Option<i32>` in `tooling/parse_utils.spl` vs `Result<u64, text>` in
  `tooling/sandbox.spl`).
- `format_bytes` x7 — seven independent implementations of one prelude name.
- `to_int(s: text) -> i64` x6 across `process_monitor.spl` / `resource_tracker.spl`.
- `to_string` x2 (`complex/utilities.spl`, `date/format.spl`).
- `input(type, name, value) -> text` at `tooling/html_utils.spl:308` — an HTML
  `<input>` builder that happens to be named `input`; wholly unrelated to the
  prelude's stdin read. Arity 3, so a prelude `input(prompt)` call in its closure
  becomes an arity error rather than a wrong answer — visible, but still wrong.
- `min`/`max(t: PureTensor<f64>) -> f64` in `gc_async_mut/pure/tensor_ops.spl` —
  arity-1 reductions; distinct signature, lower risk, but same name.
- `min(a: i32, b: i32)` (`tooling/generics_migrate.spl`, `verification/models/tensor_error.spl`),
  `min(a: ByteCount, b: ByteCount)` (`host/async_gc_immut/io/buf.spl`) — width narrowing.
- `print(msg)` at `src/lib/nogc_async_mut/mcp/fileio_main.spl:243`, `sqrt` in
  `std/examples/game_engine/fps_demo_unreal.spl`, `abs`/`sqrt` in
  `tooling/dashboard/{alerts,trends}.spl` — local convenience copies.

**Fixed here:** `src/lib/common/color/convert.spl:5` `pub fn abs(value: i64)`.
It was `pub`, exported from `std.common.color.convert` (imported by
`src/app/model3d/main.spl`, `src/app/ui.browser/renderer.spl`,
`src/lib/common/color/manipulate.spl`, `src/os/compositor/host_compositor_core.spl`,
`src/lib/skia/feature/color_management/`), and had **zero callers anywhere,
including its own file** — a public prelude shadow with no users. Deleted.

The remaining 41 are filed, not fixed: retargeting them to builtins is the
tree-wide semantic change the landed policy explicitly rejected, and the
`runtime_wrappers` group in particular is re-exported by tier facades, so it
needs its own change with bootstrap verification.

### Caveat on the interpreter column

Re-probing `min` with a value-discriminating shadow (`fn min(a: i64, b: i64)`
returning a marker `111`, same 3-module transitive shape) gives `min(3, 9) = 3`
— **the builtin won**, contradicting the prior update's "50/51 shadowable in the
interpreter". `sqrt`, `floor` and `to_int` shadows did win (markers 222/333/444
observed). The interpreter column should be re-derived with a
value-discriminating oracle rather than an existence oracle before it is relied
on; existence of a shadow is not evidence that it won.

Separately: `min(1.5, 2.5)`, `abs(0.0 - 2.5)` and `max(1.5, 2.5)` return
`-2251799813685248` / `1125899906842624` from the **builtin** with no shadow
present at all. That is an unrelated f64 defect in the prelude math builtins,
not a shadowing effect — but it means f64 results must never be used as a
shadowing oracle.

## 4. `PRELUDE_UNSHADOWABLE` recommendations

Checked against the 102 existing definitions before recommending.

| name | recommend | existing defs | justification |
|---|---|---|---|
| `exit` | **already fenced — extend to the native lane** | 16 | Fenced in interpreter + Rust HIR only. Unresolved in `native-build` (measured above), so the false-GREEN hole is live in the shipping lane. Extension must be target-conditional: 6 of the 16 are `src/os/kernel/arch/*/cstart.spl` mapping to `__spl_exit`, and those ARE compiled by this lane. |
| `panic` | **ADD** | 2 | Failure path — a shadowed `panic` means an abort silently continues, the same false-GREEN class as `exit`. Cheap: already builtin-bound in JIT *and* in the pure-Simple lane (`is_interp_builtin_fn`), so fencing it changes nothing in two of three lanes. Both existing defs are target implementations, not overrides: `bare/startup.spl:25` `fn panic(msg: text) -> Never` is the baremetal abort and `src/runtime/simple_core/core_process.spl:401` IS the runtime's panic. Neither is reachable from an interpreted host program, so fencing is behaviour-preserving — same argument that justified `exit`. |
| `abort` | n/a | 0 | Not in `PRELUDE_EXTERN_FUNCTIONS`; there is no such prelude name. Nothing to fence. |
| `assert` family | n/a | 0 | Not prelude externs either — assertions are lowered from statement syntax, not from a prelude call, so they are outside this mechanism. Worth a separate check that the statement lowering has no equivalent hole; not in scope here. |
| `eprint` / `eprintln` / `eprint_raw` | **do NOT fence** | 7 | These are exactly the names with legitimate target implementations (bare serial, host term) and with the five already-fixed documented shadows. Fencing would break baremetal diagnostics. Loud-warning is the right treatment and it already works — the `eprint` incident was caught and fixed under it. |
| `abs` / `min` / `max` / `sqrt` / `floor` / `ceil` / `pow` | **do NOT fence yet** | 30 | Highest wrong-answer risk (item 3's concern) but the *worst* fencing candidates: 30 live definitions including f32/GPU-kernel intrinsics in `gpu/kernel/math.spl` that MUST win (there is no host builtin on device), and i64 wrappers re-exported by every tier facade. Fencing silently retargets all 30. The right fix is deleting the accidental 20-odd first, then fencing what remains — in that order, not this one. Also blocked on the f64 builtin defect noted above: fencing `min`/`abs` today would route correct i64 callers into a builtin that returns garbage for floats. |
| `sys_malloc` / `sys_free` / `sys_realloc` | **do NOT fence** | 9 | All nine are the tier allocators. Fencing them would route allocation away from the tier's own allocator — a much worse failure than a shadow. |

Net recommendation: **add `panic`; extend the existing `exit` fence to the
pure-Simple native lane behind a target condition; fence nothing else until the
accidental math shadows are deleted.**

## Evidence

Probe sources: `/tmp/q34/{nat_ctl,nat_shadow,natlib,natmid,mmain,mctl,mlib,mmid}.spl`.
`scripts/check/check-prelude-builtins-unshadowable.shs` and its negative control
were not modified.

---

# Update 2026-08-10 (Q39) — value-discriminating re-measurement; two plan premises falsified

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple`, 29577536 bytes,
mtime **2026-08-09 04:50:31 UTC**. Read/invoke only; nothing relinked.

## 1. Value-discriminating oracle: min/max/abs are NOT shadowable

Probe `/dev/shm/q39/p/s/{q39main,q39mid,q39lib}.spl` — the same 3-module
transitive shape (`main` -> `q39mid` -> `q39lib`), but every shadow returns a
distinct marker constant instead of a real result, so "did the shadow win" is
read off the VALUE, not off resolution success.

Positive control: `mid_helper()` returns `7` via `q39lib.helper`, proving the
shadow module is in the closure and IS supplying bindings.

| name | shadow marker | observed | winner |
|---|---|---|---|
| `min(3,9)` | 111 | **3** | builtin |
| `max(3,9)` | 112 | **9** | builtin |
| `abs(-5)` | 113 | **5** | builtin |
| `sqrt(16)` | 222 | **222** | shadow |
| `floor(9)` | 333 | **333** | shadow |
| `ceil(9)` | 555 | **555** | shadow |
| `pow(2,3)` | 666 | **666** | shadow |
| `to_int("77")` | 444 | **444** | shadow |

Identical results with `SIMPLE_JIT_STRICT=1 SIMPLE_EXECUTION_MODE=jit` (no JIT
provenance marker was emitted, so that row is not credited as a distinct lane).

**Consequence:** the "interpreter 50/51 shadowable" figure is an artefact of an
existence oracle and must not be relied on. `min`/`max`/`abs` are already
builtin-bound — they are lowered by the MIR special case
`lower_min_max_abs` (`mir/lower/lowering_expr_builtin.rs:121`), which the earlier
sweep did not account for. Recommendation 4's premise that fencing `min`/`abs`
would "silently retarget 30 definitions" is therefore wrong for the host lanes:
they are already retargeted. `sqrt`/`floor`/`ceil`/`pow`/`to_int` genuinely are
shadowable.

## 2. The f64 defect: root-caused, one line

`min(1.5, 2.5)` printed directly gives **4609434218613702656**, which is exactly
`0x3FF8000000000000` — the IEEE-754 bit pattern of `1.5`. The builtin computes
the RIGHT answer; the result is merely typed as an integer, so the float payload
is reinterpreted as an int on formatting.

Root cause: `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:507-509`

```rust
"abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
    Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?))
}
```

The result `TypeId` is **hard-coded `I64`** for all seven names regardless of
argument type. `to_int` (line 511) is legitimately I64; these seven are not.
Fix shape: derive the result type from the lowered argument types (F64 if any
argument is F32/F64), leaving I64 as the integer-argument default. This is a
seed-layer change requiring a private-`CARGO_TARGET_DIR` rebuild to verify; it is
NOT applied here, because an unverified seed edit left in the tree is worse than
the filed defect.

Secondary observation, filed with it: `sqrt(16.0)` returned **5954099806560**
on one run and **6163580365312** on the next — non-deterministic, so the float
argument path has an uninitialised read on top of the type mislabel. That is not
explained by the `TypeId::I64` line alone.

Methodology consequence, confirmed: **f64 results must never be used as a
shadowing oracle.**

## 3. The native `exit` fence as specified is not implementable at that site

The recommendation was to fence `exit` in the pure-Simple lane at
`src/compiler/20.hir/hir_lowering/expressions.spl:50-58` (`is_interp_builtin_fn`).
Reading the call graph: `is_interp_builtin_fn` is consulted **only** from
`lower_unresolved_ident` (line 386), which is reached only after
`self.symbols.lookup` has already MISSED (`case ExprKind.Ident` at line 711-764).
It is an unresolved-name fallback, not a dispatch fence. Adding `exit` to that
list would make a bare `exit` resolvable when no shadow exists and would change
nothing when a shadow does exist — i.e. it would not fence anything. The same
applies to adding `panic` there (`panic` is already in the list, which is why the
Q34 control reported it builtin-bound; that is not evidence of a fence).

A real fence must intercept in the `case ExprKind.Ident(name)` arm at line 711,
**before** `self.symbols.lookup`.

The target condition is the second blocker: baremetal-ness in this lane is
decided at LINK time (`70.backend/backend/llvm_native_link.spl`), and no target
signal is plumbed into `HirLowering` at all. So the required
target-conditional fence needs a target flag threaded from the driver into HIR
lowering first. That plumbing is the actual next unit of work; it is filed here
rather than faked with an env-var read.

## 4. Status of Part 1 (the 41 accidental deletions)

Not started in this pass. One input to it is now settled: the widest-reach
family — `min`/`max`/`abs` (i64) in the three `src/lib/*/runtime_wrappers.spl`,
re-exported by `src/lib/nogc_sync_mut/__init__.spl:351` — reroutes to a builtin
that is **measured correct for i64** (`min(3,9)=3`, `max(3,9)=9`, `abs(-5)=5`,
table above), so the value-equivalence precondition for deleting them holds for
integer callers. Deleting them must also remove the names from that `export`
line, or the facade exports an undefined symbol.

## 2026-08-17 re-verification (lane m1_rust_interp) — MITIGATED, no longer silent

Classified by CONTENT (per session CORRECTIONS #1).

`src/compiler_rust/compiler/src/interpreter_call/mod.rs` now has
`warn_prelude_shadow_once` (:373) driven by
`interpreter_eval::is_user_facing_prelude` (:449). The dispatch comment at
:438-479 states the current contract explicitly:

- `exit` is FENCED — the builtin wins and the shadowing is reported as ignored;
- **every other** user-facing prelude name that is shadowed now WARNS ONCE,
  naming the builtin and the shadowing definition's line
  (`"WARNING: \`fn {name}\` at {where_} shadows the prelude builtin ..."`), with
  a `BDD_`-style once-per-name set so a shadowed builtin called in a loop does
  not warn per call.

The comment also corrects a previously FALSE claim in that same file ("so
builtins can't be shadowed") and records the measured scope: 50 of 51
user-facing prelude names were rebindable.

So the SILENT half of this bug — the property that made it a P2
silent-wrong-result — is closed: shadowing is now always diagnosed. The
remaining shadowability of the other 50 names is documented in-source as
**by design**, not as an unnoticed defect.

**Status: downgrade from OPEN(P2) to a design note.** If full fencing is still
wanted, that is a language-design decision, not a bug fix, and should be re-filed
as a feature request naming the 50 affected identifiers.
