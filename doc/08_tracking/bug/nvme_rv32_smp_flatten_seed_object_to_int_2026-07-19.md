# `native-build --emit-object` regression: "cannot convert object to int" (generic, content/target-independent)

**Date:** 2026-07-19
**Area:** compiler/native-build, `--emit-object` code path specifically
**Status:** FIXED 2026-07-19 (lane F3) — see "Root-cause fix (lane F3, 2026-07-19)"
below. Both x86_64 and riscv32 `--emit-object` builds of the minimal 2-fn
repro now succeed (real relocatable `.o` produced); full-link control
unaffected; regression sanity green.

## Summary

While reworking `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`'s
`NVME_RV32_SMP=1` branch to flatten every SMP source into one module (fixing
the original `unresolved name: _rv32_io_command_valid` bug — module-PRIVATE
underscore names crossing files in multi-file `--entry-closure` mode; see
"Flatten fix — RESOLVED" below), the resulting single-module 472-function
file compiled cleanly through `phase2:parse`, `aot:lower_to_mir` (all 472
functions), `aot:borrow_check`, and `aot:process_async`, then failed inside
`aot:optimize_mir` with:

```
error: semantic: type mismatch: cannot convert object to int
```

with no file/line/function attribution.

**Root cause, isolated 2026-07-19 (bisected from a ~13.5min full-file compile
down to ~1min reproductions):** this is **not** a bug in the firmware source,
not pattern-specific, not target-specific, and not `--entry-closure`-specific.
It reproduces from the most trivial possible program:

```simple
fn f(x: i64) -> i64:
    x + 1

fn main() -> i64:
    f(41)
```

via `native-build --backend llvm --entry-closure --target <ANY> --emit-object
-o out.o`. Confirmed on:
- `riscv32-unknown-none` (the firmware target) — fails.
- `x86_64-unknown-linux-gnu` — fails, identically, deterministically (repeated).
- Both `src/compiler_rust/target/bootstrap/simple` (Rust seed, dated
  2026-07-19 04:33) and `bin/simple` (self-hosted, symlink to
  `release/x86_64-unknown-linux-gnu/simple`, dated 2026-07-18 22:58) — both fail.

**The discriminating flag is `--emit-object` itself**, not `--entry-closure`
or target:
- `native-build --backend llvm --entry-closure --target x86_64-unknown-linux-gnu
  -o out` (no `--emit-object`, normal full link) on the identical trivial
  program: **succeeds** (`Linked: .../out (16 KB) via clang`).
- `native-build --backend llvm --target x86_64-unknown-linux-gnu --emit-object
  -o out.o` (no `--entry-closure`) on the identical program: **fails**,
  identical error.
- `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1` env var (as `build.shs` sets it) makes
  no difference either way — the `--emit-object` CLI flag is sufficient to
  trigger it on its own.

So: **any `native-build ... --emit-object` invocation on the current binaries
is broken, regardless of target or source content.** This binary
(`target/bootstrap/simple`, 04:33 today) is newer than the one that built
`build/nvme_fw_rv32.bootstrap_full_probe.elf` in 5.2s on 2026-07-05 per
`doc/08_tracking/bug/nvme_rv32_firmware_build_timeout_2026-07-05.md` — this
looks like a regression introduced between those two builds, likely from
ongoing parallel-session compiler bootstrap activity in this shared repo
(`ps aux` showed concurrent `bootstrap-memory-sync` stage3/stage4
native-build cycles running during this investigation).

## Why this blocks the SMP firmware build specifically

`build.shs` (both the default AND the reworked SMP branch) MUST use
`--emit-object` for the rv32 firmware: the freestanding binary needs a custom
4-hart (SMP) or single-hart (default) `_start` asm stub and a custom linker
script (`src/os/kernel/arch/riscv32/linker.ld`), so it emits an object file
and links it manually with `ld.lld` rather than using native-build's normal
auto-link path (which the control test above shows still works, but doesn't
support the custom `_start`/linker-script requirement).

## Flatten fix — RESOLVED (do not re-derive)

The original diagnosis for this lane (multi-file `--entry-closure` compiling
`entry_smp.spl` + 189 copied `logic*.spl` files, failing with `unresolved
name: _rv32_io_command_valid` because `*_cases.spl` files reference
module-PRIVATE underscore names from `*_core.spl` — legal only within one
module) **is fixed**. `build.shs`'s `NVME_RV32_SMP=1` branch now flattens the
same way the default branch already does: the SAME base concat (all
`logic*.spl` except `logic.spl`/`logic_check.spl`, then `logic.spl` with
`use` lines stripped, then the direct-entry footer) plus entry.spl's filtered
`nvme_fw_rv32_selftest`+helpers (its `_uart_put`/`main`/
`rt_rv32_boot_optional_nvme_fw_selftest` dropped — real duplicates, see
below) plus entry_smp.spl (use-stripped, `i32`→`i64` transformed same as
every other appended file) — one module,
`build/os/generated_smp/nvme_fw_smp_direct_entry.spl`, 3954 lines, 472
functions, zero duplicate top-level `fn`/`val` names, `grep -c
_rv32_io_command_valid` = 17 (matches the default's count). A guard fn
(`smp_check_collisions`) in `build.shs` fails the build loudly on any future
top-level-name collision instead of silently shadowing.

Two real collisions were found + fixed during this work:
1. The wave-3 IPC/pool/nand/fourcore/coro core files
   (`logic_ipc_layout_core.spl` etc.) already match the `logic*.spl` glob in
   the base step — appending them a second time (as an earlier draft of this
   fix attempted, and as the original task instructions assumed) is a hard
   duplicate-definition collision. They must NOT be appended separately.
2. `entry.spl`'s `_uart_put`, `main`, and
   `rt_rv32_boot_optional_nvme_fw_selftest` duplicate definitions already
   present (`entry_smp.spl` defines its own `_uart_put`; the base footer
   already defines `main` and `rt_rv32_boot_optional_nvme_fw_selftest`) — an
   awk paragraph filter drops exactly those three from the appended
   `entry.spl` content, keeping `nvme_fw_rv32_selftest` + its `_emit_*`
   helpers (which entry_smp.spl's hart0 path needs and which are NOT part of
   the default's base flatten — the default omits `entry.spl` entirely and
   calls the raw `nvme_fw_rv32_logic_selftest()` instead, since its own
   `_start` asm prints the PASS banner itself).

## Impact

Both `build/nvme_fw_rv32.elf` (default) and `build/nvme_fw_rv32_smp.elf` (SMP)
are unbuildable while this regression stands, **independent of any firmware
source content** — this is not something further `.spl` firmware changes can
route around. `build/nvme_fw_rv32.elf` is currently absent on disk.

## Flatten validated end-to-end (2026-07-19, via the working full-link path)

A second real bug was found and fixed while validating the flatten through a
path that does NOT hit the `--emit-object` wall: `native-build --backend llvm
--entry-closure --target x86_64-unknown-linux-gnu -o <exe>` (no
`--emit-object`) on the *actual*
`build/os/generated_smp/nvme_fw_smp_direct_entry.spl` first failed at parse
with `Syntax error at 3434:39: reserved keyword 'val' cannot be used as a
parameter name` — `entry_smp.spl` declared `extern fn
rt_rv32_shm_store(idx: i64, val: i64)` and `fn shm_put(idx: i64, val: i64):`,
both using the reserved keyword `val` (see `.claude/rules/language.md`
reserved-keyword list) as a plain parameter name. Fixed in
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry_smp.spl` by renaming the
parameter to `v` in both declarations and their one call site. Notably, the
`--emit-object` path's parser did **not** flag this (it got all the way to
`aot:optimize_mir` before the generic error above) — the two code paths
disagree on this rule, a smaller, secondary discrepancy worth a note in the
"Next check" below.

After the fix, the full-link compile of the real 472-function flattened file
**succeeded**: `Build complete: 1 compiled, 0 cached, 0 failed`, `Linked:
.../nvme_fw_smp_fulllink_validate2_exe (22 KB) via clang`, 15.4s total. The
only diagnostics were harmless `[WARN] Failed to load imported types from
[...]` lines for the pre-existing (default-flatten-inherited) `use
logic_x_cases.*` lines that point at files no longer present standalone —
non-fatal, same as the default flatten already tolerates.

**This closes the loop**: the flatten mechanism and its content are fully
correct and proven through parse/HIR/MIR/borrow-check/optimize/codegen/link.
The *only* remaining blocker to producing the real riscv32 object/ELF is the
generic `--emit-object` regression documented above, which is target- and
content-independent and not fixable by further `.spl` changes.

## Next check

Bisect the seed's `--emit-object` handling directly (smallest repro: the
2-function `f`/`main` program above, ~1 min per iteration) rather than
anything firmware-shaped — `doc/03_plan/agent_tasks/simple_os_rv64_native_build_timeout.md`
already documents the same `cannot convert object to int` message recurring
in `symbol_to_operand()` / bootstrap-flat symbol-table lookup for native AOT
paths; this may be the same code path re-regressing, or the `--emit-object`
branch specifically skipping a step the normal full-link path performs (e.g.
a symbol-table finalization pass that only runs before linking, not before
raw object emission).

## Orchestrator bisection addendum (2026-07-19)

Probed the minimal 2-fn control repro (`--emit-object`, riscv32) against every
available seed+source vintage pairing:

| seed binary (mtime) | src/compiler tree | result |
|---|---|---|
| main repo seed (07-19 04:33) | main tip / cf3b364c548 / b620f0cd023a / a7454f2be8a (Jul 16) | object-to-int |
| simple-seed-llvm-fix (07-18 08:00) | its own tree | object-to-int |
| pure-simple-shared-enum (07-18 11:56) | its own tree | object-to-int |
| pure-simple-tool-remain (07-18 05:41) | its own tree | object-to-int |

Conclusion: `--emit-object` is broken across ALL available vintages back to at
least 2026-07-16 (and probably since shortly after 2026-07-05, when the last
known-good probe ELFs were produced). It went unnoticed because the rv32 boot
spec fails closed on a missing ELF and nothing else exercises the flag.
Reproducing the last-good state requires rebuilding a ~Jul-05 seed from that
era's compiler_rust — compiler-owner territory. Full-link (no `--emit-object`)
WORKS on the identical source (x86_64 validated 15.4s), so the flattened SMP
firmware source itself is compile-clean; only object emission is blocked.

## Root-cause fix (lane F3, 2026-07-19)

F2's bisection correctly localized the *detector* (`Value::as_int()` in
`src/compiler_rust/compiler/src/value_impl.rs:57`, held constant across the
whole seed↔source bisection matrix) but concluded no `.spl`-only fix could
exist. That conclusion was about the bisection method's blind spot, not the
bug itself: pinning the exact `.spl` statement (not just the detector) was
still possible via print-instrumentation bisection through the actual call
chain, and it *is* a pure-`.spl` defect.

**Root cause — exact location:**
`src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl`, in
`ModuleInliner.inline_module` (Phase 2, function-update step, formerly one
line, now the `var updated_func = func` block just before
`optimized_functions[updated_func.symbol] = updated_func`). The original
statement was:

```
val updated_func = MirFunction(..func, locals: new_locals, blocks: optimized_blocks)
```

**On the "strongest lead" (Ret-operand match, `policy.spl:286-297`):**
investigated first per the task brief, and ruled out with direct evidence,
not skipped. `MirOperandKind` (`src/compiler/50.mir/mir_instructions.spl:512`)
has exactly 3 variants (`Copy`/`Move`/`Const`), and the inner match on
`ret_operand.kind` already covers all 3 — it was already exhaustive, no
missing-variant bug to fix there. Instrumentation confirmed it executes
cleanly on the repro: `inline_call:terminator=Ret ...` ->
`inline_call:ret-kind=Copy src=5` -> `inline_call:ret-handled count=4`, all
printed, then execution continues normally through `inline_call`'s return
and back up through `inline_calls_in_block_with_candidates` (`did_inline=true
continuing` -> `loop-done did_inline=true` -> `result-built`) and into
`ModuleInliner.inline_module`'s Phase 2 (`modified=true` -> `new_locals-init`
-> `new_locals-final` -> `pre-MirFunction-construct`) — the crash is several
call frames downstream of the Ret match, with no error signal anywhere in
between.

**Mechanism:** `MirFunction` is a 24-field struct. Pinned via targeted print
instrumentation added at every step of `ModuleInliner.inline_module` →
`inline_calls_in_block_with_candidates` → `FunctionInliner.inline_call` and
run against the minimal 2-fn repro (`f`/`main`) under
`SIMPLE_COMPILER_TRACE=1`: every step up through building `new_locals` and
`optimized_blocks` printed correctly, and the crash traced to exactly this
one constructor call — the bootstrap seed interpreter's evaluation of a
struct-literal with the `..spread` update syntax overriding 2 of
`MirFunction`'s 24 fields (`locals`, `blocks`) mishandles one of the other
(copied-through) fields internally and feeds a non-int `Value::Object` into
an int-context coercion, which is where `Value::as_int()` (the seed-side
detector F2 found) raises "cannot convert object to int". This explains why
F2 saw the bug on every source vintage back to 2026-07-06 paired with the
current seed: `ModuleInliner.inline_module`'s 2-field spread-update on
`MirFunction` predates that whole probed range, so the defect was already
present the entire time — it only started *reproducing on the trivial 2-fn
case* once `--emit-object` started reliably reaching `aot:optimize_mir` with
real function content bridged over (the `f9b43750519` AST-bridge boundary F2
pinned), and it reproduces on any module with >=2 functions.

**Fix 1 (root fix):** rewrite the constructor call as an explicit
struct-copy + field mutation, the same idiom already used a few lines above
in the same function for `caller_with_generated_locals` (a pre-existing,
proven-working pattern in this exact file):

```
var updated_func = func
updated_func.locals = new_locals
updated_func.blocks = optimized_blocks
```

This avoids the buggy multi-field spread-update interpreter path entirely.
Verified independently of the wiring fix (see "Verification b" below): with
`inline_functions` forced to run (temporarily overriding the backend name
passed to `optimize_mir_module_for_backend` to a non-LLVM sentinel and
re-running the exact failing repro command), the pass now completes
("RUNNING" → "DONE" instrumentation) with no object-to-int error, and the
`.o` still emits successfully.

**Fix 2 (wiring fix):** `driver_pipeline.spl`'s `optimize_mir` previously
called the backend-*unaware* `optimize_mir_module` unconditionally (calling
`compiler.mir_opt.mod.optimize_module`, which always includes
`inline_functions` regardless of target). The backend-aware
`optimize_module_for_backend` / `optimizationpipeline_for_backend` +
`mir_pass_backend_skip_reason_fast` machinery (mod.spl) already existed
fully implemented and exported, but had no live caller — designed but dead.
Wired it through: `optimize_mir` now reads `self.ctx.options.backend` and
calls a new `optimize_mir_module_for_backend` (mir_opt_integration.spl),
which calls the pre-existing `optimize_module_for_backend`. For LLVM-target
builds this now correctly skips `inline_functions` (`llc`'s own -O3 inliner
already covers it) as well as `common_subexpr_elim`, `global_value_numbering`,
`auto_vectorize`, `loop_unroll`, `strength_reduction`, `predicate_promote`.
Non-LLVM backend names see no filtering (`mir_backend_is_llvm` gates every
skip reason), so behavior for every other backend is unchanged.

**Fix 2b (bug discovered while wiring):** wiring wasn't a no-op change — it
made a previously-dead, never-exercised code path live for the first time,
and that path had its own latent bug: `mir_pass_applies_to_backend` (mod.spl)
was written as `mir_pass_backend_skip_reason_fast(...).? == false`. Under
the bootstrap seed interpreter, `Option.?` chained directly into a `==`
comparison universally evaluates to `false` — including the `nil` (no skip
reason) case, where it should be `true` — so with the wiring live, *every*
pass was reported "does not apply" and the whole pipeline silently emptied
out (0 passes ran, confirmed via instrumentation: `after passes=0` for every
call). Fixed with an explicit `match` on the `Option`, the same
`.?`-avoidance idiom already established elsewhere in this codebase (see
the pre-existing comment on `extract_func_symbol_id`'s call site in
`_Inline/driver.spl`, same landmine class, different value type — that one
is a `Some(0)`-collapses-falsy case on `i64?`, this one is a
chained-`==`-always-false case on `text?`).

**Fix 3 (secondary, unblocking verification, discovered downstream of Fix
1+2):** with the root+wiring fixes in place, x86_64 `--emit-object` passed
immediately, but riscv32 (bare-metal target) hit a *different*,
pre-existing, previously-masked bug: `llc` failed with `expected metadata
type` / then `expected top-level entity`, both inside
`LlvmIRBuilder.emit_baremetal_attributes()`
(`src/compiler/70.backend/backend/llvm_ir_builder.spl`). Two distinct
defects there, both fixed:
  - `self.emit("!0 = !{!\"no-builtins\"}")` used single (unescaped) braces;
    Simple's string interpolation parses `{...}` as an expression, and
    `!"no-builtins"` parses as a valid unary-not-of-string expression
    (non-empty string is truthy, so `!"no-builtins"` -> `false`), silently
    rewriting the emitted IR to `!0 = !false`. Fixed by doubling the braces
    (`{{`/`}}`, the same escaping convention already used elsewhere in this
    file, e.g. `nounwind {{` in `start_function`).
  - `MirToLlvm.create_baremetal()` called `emit_baremetal_attributes()` at
    builder-construction time, before `translate_module()` later calls
    `emit_module_header()` — so the bare-metal `!N = ...` metadata lines
    landed in the `.ll` file *before* `source_filename`/`target
    datalayout`/`target triple`, which `llc` rejects ("expected top-level
    entity" on the header line). Fixed by having
    `emit_baremetal_attributes()` queue its lines in a new
    `pending_baremetal_attrs` field when called before the header exists,
    and having `emit_module_header()` flush the queue right after emitting
    the header (falls back to immediate emission if the header was already
    emitted, for robustness against future call-order changes). No caller
    changes needed — both existing call sites (`create_baremetal`,
    `emit_module_header`) keep their current call order/signatures.

**Blast radius (conscious, reasonably scoped, flagged for follow-up
attention rather than expanded into this fix):**
- Fix 2 (wiring) changes the shared `CompilerDriver.optimize_mir` method,
  which is also `jit_compile_and_run`'s only optimize-MIR call site
  (`driver_pipeline.spl:169`), not just the AOT/native-build path this bug
  is about. If a JIT run's `ctx.options.backend` is `"llvm"`, JIT-compiled
  code now also skips `inline_functions`/`common_subexpr_elim`/etc. the same
  way AOT does — optimization-level-only, correctness-preserving (an
  un-inlined call is still a correct call), but not itself exercised by this
  session's verification (regression sanity (d) ran via the `bin/simple`
  seed symlink, which does not read this changed `.spl` source).
- Fix 3's `emit_module_header()` ordering change affects every bare-metal
  LLVM target, not just riscv32 (any target using
  `MirToLlvm.create_baremetal`, e.g. other baremetal `arm`/`aarch64`
  triples if/when exercised). Only riscv32 was exercised in this session's
  verification.

**Files touched:**
- `src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl` (root fix)
- `src/compiler/60.mir_opt/mir_opt/mod.spl` (wiring: `.?`-chain fix in
  `mir_pass_applies_to_backend`; `optimize_module_for_backend` and
  `optimizationpipeline_for_backend` / `mir_pass_backend_skip_reason_fast`
  were already present and required no changes)
- `src/compiler/60.mir_opt/mir_opt_integration.spl` (wiring: new
  `optimize_mir_module_for_backend`)
- `src/compiler/80.driver/driver_pipeline.spl` (wiring: `optimize_mir` now
  threads `self.ctx.options.backend` through)
- `src/compiler/70.backend/backend/llvm_ir_builder.spl` (secondary fix:
  bare-metal attribute brace-escaping + emission ordering)

**Verification (2026-07-19, lane F3):**
- (a) `native-build --backend llvm --entry-closure --emit-object` on the
  minimal 2-fn repro: **PASS** for both `--target x86_64-unknown-linux-gnu`
  (`file` confirms `ELF 64-bit LSB relocatable, x86-64`) and `--target
  riscv32-unknown-none` (`file` confirms `ELF 32-bit LSB relocatable, UCB
  RISC-V, RVC, soft-float ABI`).
- (b) Root fix proven independent of the wiring fix: with `optimize_mir`'s
  backend name temporarily forced to a non-LLVM sentinel (so
  `inline_functions` is NOT skipped and actually runs), the exact same
  repro command still succeeds — instrumentation confirmed
  `InlineFunctions RUNNING` → `InlineFunctions DONE` with no object-to-int
  error, then the override was reverted.
  Note: `native-build`'s `--backend` CLI flag only accepts `llvm` or
  `cranelift`; neither is a usable "force a non-LLVM ctx.options.backend"
  lever from the CLI (`cranelift` did not route through the standard
  AOT/`optimize_mir` path observably, and `--backend c` is CLI-rejected
  outright) — hence the smallest reliable proof was a temporary one-line
  override of `optimize_mir`'s `backend_name` local, verified, then
  reverted; this is recorded here for anyone re-deriving/re-checking it.
- (c) Full-link control (no `--emit-object`, x86_64): **PASS** — `Build
  complete: 1 compiled, 0 cached, 0 failed`, 16 KB binary, and running it
  returns rc=42 (`f(41)` = 41+1), confirming functional correctness, not
  just successful compilation.
- (d) Regression sanity: `timeout 300 bin/simple run
  examples/09_embedded/simpleos_nvme_fw/fw_rv32/ipc_fourcore_check.spl` ->
  rc=0, `IPC FOURCORE CHECK PASS`. `timeout 300 bin/simple run
  examples/09_embedded/simpleos_nvme_fw/fw_rv32/coro_check.spl` -> rc=0,
  `CORO CHECK PASS`. (Both ran via the current `bin/simple` seed symlink and
  do not themselves exercise the touched self-hosted-compiler source paths,
  but confirm no regression in adjacent tooling.)
- Not independently re-verified at full scale in this session: compiling
  the real 472-function flattened firmware
  (`build/os/generated_smp/nvme_fw_smp_direct_entry.spl`) end-to-end with
  `--emit-object` — attempted, hit the session's verification budget at
  400s (this file's own earlier full-link timing note put it at ~13.5 min
  for a full compile pre-fix; not re-run to completion here). The isolated
  minimal-repro root cause is the same defect regardless of module size
  (any module with >=2 functions triggers `ModuleInliner.inline_module`'s
  Phase 2), so this is expected to also now succeed, but that expectation
  is not itself evidence — flag for a follow-up confirmation run with a
  longer budget before closing out the firmware build end-to-end.

**Filed secondary defect (not fixed, out of scope for this fix — flagged
per F1's note):** `driver_pipeline.spl`'s `get_optimization_config()`
hardcodes `optimizationconfig_speed()`, ignoring `ctx.options.opt_level`
entirely. Every build (debug or release, any `-O` level) always runs the
Speed-level MIR optimization pipeline. Independent of the fixes above; not
expanded into this change's scope.

---

## 2026-07-20 addendum: layers 2 and 3 of the onion (post-fix)

The inline_functions fix above unmasked two further defects on the same
emit-object path, both now fixed on the clean-cache 2-fn repro
(`SIMPLE_NATIVE_BUILD_CLEAN=1`, riscv32 ELF relocatable, rc=0):

**Layer 2 — Option-wrapped llc bytes → misleading "unknown static method
object on class CodegenOutput".** After llc already produced a valid .o,
`compile_ir_to_object`'s `rt_file_read_bytes` result (Some-wrapped under the
seed interpreter) flowed unwrapped into `CodegenOutput.object`'s `[u8]` param;
`constructor_overload_score` rejects `Some(_)` vs Array and the dispatcher
misreports it as a missing method. Fixed in
`llvm_backend_tools.spl` (`val byte_arr: [u8] = bytes ?? []` after the nil
guard). Seed-side diagnostic/scoring defect filed separately:
`seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20.md`.

**Layer 3 — O(M²) IR-text accumulation = the 50-minute "silent phase".**
`LlvmIRBuilder.emit()` accumulated the module IR as
`self.instructions = self.instructions.push(line)` — a value-type array the
seed interpreter clones per push (`interpreter_method/collections.rs:67-72`),
O(M²) over M IR lines. Invisible on a 2-fn repro; a 479-fn flattened module
spent >50 min after `aot:format:done` producing zero output (llc never
reached — no `/tmp/simple_llvm_<pid>.ll` existed) until the 3600s wrapper
timeout. Fixed by switching the accumulator to the amortized-O(1)
`rt_string_builder_*` runtime builder (same externs as
`src/lib/common/string_builder.spl`, bug rt_string_concat_quadratic_2026-06-12;
handle consumed exactly once by `llvm_ir_builder_build`). Known smaller
sibling left unfixed (k << M): `string_global_text` quadratic concat in
`mir_to_llvm_helpers.spl:41-44` / `asm_constraints_helpers.spl:329-333` plus a
dead `string_globals.push` accumulator — flagged for follow-up.

Verification method note: a shared main WC repeatedly gave false greens via
native-build **cache replays** and false reds via other sessions' in-flight
edits; all layer-2/3 evidence above was produced in a pristine detached
worktree at origin tip with `SIMPLE_NATIVE_BUILD_CLEAN=1`.
