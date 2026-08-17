# Self-hosted `bootstrap/stage3/.../simple` SIGSEGVs on essentially EVERY `native-build` — `bin/simple` is silently the Rust seed, not a working self-hosted replacement

- **Date:** 2026-08-06
- **Severity:** high — the self-hosted stage3 compiler cannot currently emit
  ANY native binary via `native-build`, including a trivial
  `fn main(): print("hello")`. Independently reproduced (own gdb backtrace +
  register dump), on top of the sighting already recorded in
  `mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`'s
  "Verification" section (that doc's `0x118` mention is the same crash; this
  doc gives the standalone confirmation, root-cause correlation, and — most
  importantly — the scope/regression determination that doc explicitly left
  open).
- **Status:** **root cause pinned to the exact source line with symbolized
  frames** (see "Source-line-accurate root cause" below), a scoped fix
  landed, and regression-checked via the existing bitfield spec suite. Full
  native-rebuild end-to-end verification (rebuild stage2 → stage3 with the
  fix and re-run `native-build hello.spl` on the *native* codegen path) was
  still running in the background when this doc was updated — self-hosting
  the entire compiler from a cold cache took well over 90 minutes and had
  not finished; see "Verification status" for exactly what is/isn't
  confirmed yet.

## Source-line-accurate root cause

Building on the original reproduction below, I got symbols by exploiting an
existing **unstripped, `with debug_info`** copy of `stage2`
(`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` — stage2 is built
by the Rust seed's `rt_native_build`, which does not strip by default; only
the *stage3* build, done by the pure-Simple self-hosted driver, drops debug
info unless `-g`/`--debug` is passed). Stage2 reproduces the **identical**
outward symptom (SIGSEGV, exit 139) on the same trivial `hello.spl` repro,
confirming both binaries hit the same *class* of bug even though the exact
disassembly differs between the two (see "Is this the same site as stage3's
`0x517966`?" below — left explicitly open).

```
$ RT=build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority
$ STAGE2=build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
$ SIMPLE_RUNTIME_PATH="$RT" SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
    gdb -batch -ex run -ex "info registers" -ex "x/3i \$pc" -ex bt \
    --args "$STAGE2" native-build --runtime-path "$RT" -o hello_out hello.spl
...
Program received signal SIGSEGV, Segmentation fault.
0x0000000000529b8d in compiler__hir__hir_types__SymbolTable.lookup ()
rax 0x3   rbx 0x6bc08b1   r15 0x0   rip 0x529b8d <SymbolTable.lookup+77>
=> mov 0x18(%r15),%rdi     ; faulting instruction (r15 = NULL)
   mov %rbx,%rsi
   call rt_dict_contains
#0 compiler__hir__hir_types__SymbolTable.lookup ()
#1 compiler__mir___MirLoweringExpr__switch_operators_calls__MirLowering.try_lower_bitfield_construct ()
#2 compiler__mir___MirLoweringExpr__switch_operators_calls__MirLowering.lower_call ()
#3 compiler__mir___MirLoweringExpr__expr_dispatch__MirLowering.lower_expr ()
#4 compiler__mir__mir_lowering_stmts__MirLowering.lower_stmt_impl ()
#5 compiler__mir__mir_lowering_stmts__MirLowering.lower_stmt ()
#6 compiler__mir___MirLowering__function_lowering__MirLowering.lower_block_expected ()
#7 compiler__mir___MirLowering__function_lowering__MirLowering.lower_function_with_gpu_metadata ()
#8 compiler__mir___MirLowering__bootstrap_globals__bootstrap_lower_flat_hir_module_to_mir ()
#9 compiler__mir___MirLowering__bootstrap_globals__bootstrap_lower_flat_hir_modules_to_mir_for_target ()
#10 compiler.driver.driver_bootstrap.bootstrap_lower_to_mir_context ()
#11 compiler__driver__driver_aot_pipeline__CompilerDriver.aot_compile ()
#12 app.cli.bootstrap_main.run_native_build_bootstrap ()
#13 main ()
```

**Disassembly of `SymbolTable.lookup` (`src/compiler/20.hir/hir_types.spl:368-387`)**
shows exactly what it's doing:

```
mov 0x10(%r14),%r15    ; r15 = self.current_scope
mov $0x80009,%ebp
mov %r15,%r12          ; r12 = &current_scope (masked)
call rt_pool_safepoint  ; loop top
mov 0x8(%r14),%rdi      ; rdi = self.scopes
mov (%r12),%rsi         ; rsi = scope_id.id
shl $0x3,%rsi           ; tag as Any-typed key
call rt_index_get        ; self.scopes[scope_id.id]  <-- returns NULL
mov %rax,%r15
and $0xfffffffffffffff8,%r15
=> mov 0x18(%r15),%rdi  ; FAULT: scope.symbols field read on r15=NULL
```

This is `SymbolTable.lookup()`'s scope-chain walk:

```python
fn lookup(name: text) -> SymbolId?:
    var scope_id = self.current_scope
    loop:
        val scope = self.scopes[scope_id.id]      # <- rt_index_get returns NULL
        if rt_dict_contains(scope.symbols, name):  # <- FAULT: scope is NULL
            ...
```

reached from `try_lower_bitfield_construct` (`switch_operators_calls.spl:958-986`):

```python
case HirExprKind.NamedVar(_, callee_name):
    val resolved_symbol = self.symbols.lookup(callee_name)   # <- crashes here
    if resolved_symbol != nil:
        return self.try_lower_bitfield_construct_for_symbol(resolved_symbol, args)
    return nil
```

`try_lower_bitfield_construct` runs on **every** call with exactly 1
argument (`if args.len() != 1: return nil`) before falling through to the
generic `lower_call` path — so `print("hello")` (1 arg) always hits this
check, and the `NamedVar` branch always does a fresh scope-chain
name-lookup, discarding the `symbol` the HIR node already carries (`_` in
the pattern).

**Why `self.scopes[scope_id.id]` comes back NULL:** the `self.symbols` on
`MirLowering` here is not a general-purpose fully-built HIR symbol table —
it's constructed by the **bootstrap flat pipeline**'s
`bootstrap_flat_symbol_table()` (`src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:302-307`):

```python
fn bootstrap_flat_symbol_table(module_index: i64) -> SymbolTable:
    var table = SymbolTable.new()
    val flat_symbols = bootstrap_hir_module_symbols_at(module_index)
    for symbol in flat_symbols:
        table.symbols[symbol.id.id] = symbol   # only the FLAT id->symbol map
    table
```

`SymbolTable.new()` *does* insert a root `Scope` at id 0
(`hir_types.spl:228-234`, `table.scopes[0] = Scope(...)`), so the scope
chain is not structurally empty — but `bootstrap_flat_symbol_table` never
calls `push_scope()`/`define()` to populate any scope's own `symbols` dict,
and the `self.scopes[scope_id.id]` bracket read on this
`Dict<i64, Scope>` (a struct-valued dict) comes back NULL under native
codegen instead of returning the id-0 `Scope` that `.new()` put there or
cleanly reporting "not found" — the same native-codegen struct-valued-Dict
unreliability this repo's own code already had one battle-scar comment
about one line below (`hir_types.spl:374-376`, added for a *different*
symptom on the *same* function: `Dict.get` falsely reporting nil for a
present tagged integer). This crash is the sibling failure mode of that same
family: instead of a false negative on a *present* key, a struct-valued
bracket read on this table returns a null pointer instead of the value or a
clean miss.

The `lower_call` sibling code path (`switch_operators_calls.spl:3905-3932`)
already documents and uses the safe alternative for the exact same
situation — resolve via the symbol **already embedded on the HIR node**,
never via a second scope-chain lookup:

```python
case HirExprKind.Var(symbol):
    direct_symbol = symbol
    val sym = self.symbols.get_symbol_raw(symbol.id)   # flat id-map read, no scope walk
    ...
case HirExprKind.NamedVar(symbol, name):
    # `name` already carries a --entry-closure cross-module imported
    # function's qualified name ... NOT looked up here via self.symbols
    # a second time ...
    direct_symbol = symbol
```

`try_lower_bitfield_construct` was the one caller in this file that didn't
follow that already-established pattern.

## Fix landed

1. **`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`**
   (`try_lower_bitfield_construct`): the `NamedVar` branch now captures and
   uses the symbol already resolved onto the HIR node
   (`case HirExprKind.NamedVar(symbol, _): return
   self.try_lower_bitfield_construct_for_symbol(symbol, args)`), matching
   the `Var` branch immediately below it and the documented pattern in
   `lower_call`. `try_lower_bitfield_construct_for_symbol` already guards
   `sym_id < 0` and `not self.bitfield_map.has(sym_id)` by returning `nil`,
   so an unresolved/-1 symbol safely falls through to generic call
   lowering exactly as before — no `self.symbols.lookup()` call remains in
   this function.
2. **`src/compiler/20.hir/hir_types.spl`** (`SymbolTable.lookup` and
   `lookup_or_invalid`, defense-in-depth for the whole family): both now
   guard the scope-chain read with `if not
   rt_dict_contains(self.scopes, scope_id.id): break` before the bracket
   read, so any other caller landing on this same "scope id not actually
   present in `scopes`" situation (e.g. `lookup_or_invalid`, called from
   `switch_operators_calls.spl:3049`, and any future caller) ends the scope
   chain cleanly (same behavior as walking off the top with no parent)
   instead of dereferencing a NULL `Scope` pointer. `push_scope`/`pop_scope`
   (`hir_types.spl:500,518`) and `define` (`hir_types.spl:270`) have the
   same unguarded pattern but are not reached from the bootstrap-flat path
   (that path never calls `push_scope`) — left as-is; only the two paths
   proven reachable from a real crash were touched, per "don't guess a fix
   for foundational code you can't verify."

## Verification status

- **Regression check via the interpreted/seed pipeline (passing):** the
  compiler's own MIR-lowering source (including the two edited files) is
  executed by whatever runtime is running `bin/simple` — currently the Rust
  seed (see "Scope determination" below) — when it acts as a compiler. Ran
  the full bitfield spec family through it with the fix applied:
  `test/01_unit/compiler/native/bitfield_codegen_spec.spl`,
  `test/01_unit/compiler/mir/bitfield_mir_spec.spl`,
  `test/01_unit/compiler/bitfield_sugar_spec.spl`,
  `test/01_unit/compiler/packed_struct_bitfield_spec.spl`,
  `test/03_system/feature/usage/bitfield_spec.spl`,
  `test/03_system/feature/usage/bitfield_runtime_compat_spec.spl` — **all 6
  files pass, 0 failures.** This is the cheapest available discriminator
  that the direct-symbol change doesn't break bitfield-construct
  recognition, but it does **not** exercise the native codegen path that
  actually crashes.
- **Native end-to-end verification (started, not completed in this
  session):** rebuilding stage2 from the fixed pure-Simple source via the
  Rust seed (`SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple
  native-build --source src/compiler --source src/lib --source src/app
  --entry src/app/cli/bootstrap_main.spl -o <fixed-stage2>`) was still
  running after **over 90 minutes** of continuous 100%-CPU work in its
  `native_build_worker.spl` child (confirmed via `/proc/<pid>` — genuinely
  computing, not hung: `futex_wait_queue` on the idle supervisor thread,
  100% CPU on the actual worker thread) when this doc was last updated. A
  second background build (an **unfixed** stage3, rebuilt with `-g` from
  the existing unstripped stage2, purely to get a symbolized comparison
  against the original stripped-stage3 crash address) was similarly still
  running. Neither had produced an output binary yet. **This means: the
  fix is not yet empirically confirmed to eliminate the crash on the
  actual native-codegen path that stage3 uses** — only the mechanism
  (pinned via debug-symbol stage2 + disassembly) and the non-regression on
  the interpreted path are confirmed. Follow-up: once either background
  build finishes, run `<fixed-stage2-or-stage3> native-build hello.spl -o
  hello_out && ./hello_out` and confirm exit 0 / prints `hello`; if it
  still crashes, gdb it the same way (now with symbols) to see whether a
  second site is hit.

## Is this the same site as stage3's `0x517966`? Left open.

The stripped-stage3 crash this doc originally described (`rax=0x110`,
`mov 0x8(%rax),%r14` then `test/jle`, 6 user frames above
`__libc_start_call_main`) and the stage2 crash pinned above (`r15=0x0`,
`mov 0x18(%r15),%rdi` then `call rt_dict_contains`, 13 user frames) **do
not obviously match**: different faulting instruction shape, different bad
pointer value class (a small scalar vs. a true NULL), and a call-depth
difference (6 vs. 13) that isn't explained by codegen-layout differences
alone — frame count reflects how deep into the pipeline execution got
before crashing, not just addressing. `objdump -d` on the actual stripped
`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` around `0x517966` shows
a null-check-then-length-read shape (`test rax; je +skip; mov 0x8(%rax)`)
with no `rt_pool_safepoint`/`rt_index_get`/`rt_dict_contains` call triple
nearby, unlike `SymbolTable.lookup`'s disassembly — consistent with the
original doc's own read of it as a length-field-then-array-loop shape, not
a dict lookup. **Working conclusion: these are plausibly two distinct
crash sites in the same general native-codegen-list/dict-corruption
family** (per this repo's memory notes on that family), not proven to be
the identical bug. The `-g` unfixed-stage3 rebuild (in progress, see
above) is the intended discriminator — once it finishes, gdb it on the
identical `hello.spl` repro and compare frames/site directly against this
doc's stage2 backtrace.

## AC-6 (SimpleOS native build) scope check

`scripts/os/simpleos-native-build.shs` does **not** invoke
`bootstrap/stage3/.../simple` (or any `build/bootstrap/stage*` binary)
directly. It selects a compiler via
`scripts/lib/simple-compiler-select.shs`, whose own header comments
document that it is a **positive-capability probe** specifically built to
avoid this exact failure class: it explicitly excludes "the staged
bootstrap compilers" from blind selection because they "answer 'unknown
X'... a PASS" on capability probes and would otherwise be selected "having
proved nothing about it, and that binary then SIGSEGVs on the real work"
(comment dated before this investigation, i.e. this is a known, already
-designed-around risk, not a new one). AC-6's build path is **not**
directly exposed to this bug's silent-failure risk.

---

*(Original reproduction, disassembly-only investigation, and scope
determination sections below are preserved from the initial filing; the
new investigation above supersedes their root-cause section with a
source-line-pinned mechanism and a landed fix.)*

## Reproduction (own run, independent of the other lane)

```
$ git fetch origin main   # tip 42706d525a77d7af30c70b43435b330cd83732c0
$ cat /tmp/.../hello.spl
fn main():
    print("hello")

$ ulimit -c unlimited
$ timeout 30 bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build hello.spl -o hello_out
timeout: the monitored command dumped core
$ echo $?
139
```

Reproduced **2/2** tries here (identical fault both times), on top of the
other lane's **3/3** — 5/5 combined across two independent sessions.

## Scope determination — THE important finding for other lanes (unchanged)

`bin/simple` currently resolves to the Rust bootstrap SEED, not a
self-hosted binary (`readlink -f bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple`, prints the seed's
`WARNING:` banner). The seed does **not** crash on this bug — it uses a
different (Rust) implementation of native-build entirely, unrelated to the
pure-Simple `SymbolTable`/MIR-lowering code pinned above. See
`doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md` for the
broader finding that `bin/simple` is not the self-hosted binary
CLAUDE.md/`.claude/rules/bootstrap.md` says it should be.

## Recommended follow-up

1. Finish the in-progress native rebuild (fixed stage2 → fixed stage3) and
   confirm `native-build hello.spl` now runs to completion and the output
   binary executes and prints `hello` with exit 0. Sabotage-verify by
   reverting the fix and confirming the crash returns.
2. Resolve "Is this the same site as stage3's `0x517966`?" once the `-g`
   unfixed-stage3 rebuild finishes — if it's a distinct site, file it
   separately with its own pinned mechanism.
3. Fix `bin/simple`'s symlink/build pipeline so it points at a real
   self-hosted binary again, not the Rust seed (tracked separately in
   `deployed_bin_simple_still_seed_2026-08-05.md`).
4. Separately: the seed's ~2-minute `native-build` time for a trivial
   script, and the >90-minute full self-hosted compiler rebuild time
   observed in this investigation, are worth their own performance bug
   filing.

---

## 2026-08-06 follow-up — the `hir_types.spl` "defense-in-depth" guard broke Stage 3; removed

The end-to-end native verification this doc left open has now been run. Result:
the `switch_operators_calls.spl` half of `1ea6599e8fb` is a **real fix and is
kept**. The `hir_types.spl` half — the `rt_dict_contains(self.scopes,
scope_id.id)` guard added to `lookup()`/`lookup_or_invalid()` as
"defense-in-depth" — was **not** load-bearing for this bug and **broke the
Stage 3 self-host outright**. It has been removed.

### What actually killed Stage 3

Stage 3 died with **SIGSEGV (exit 139) and a 0-byte log**. The zero output is
why it read as a mystery: it is not a compiler diagnostic and not an OOM (tree
RSS peaked ~3.2 GB; earlyoom fired at no point during the run). A gdb backtrace
against the unstripped stage2 shows **unbounded mutual recursion → stack
overflow**, repeating this 6-frame cycle to stack exhaustion:

```
lower_type
  -> lower_named_kind
    -> try_register_bootstrap_global_symbol
      -> register_imported_symbol
        -> register_imported_type_methods
          -> declared_surface_callable_type
            -> lower_type ...
```

The faulting frame is `rt_env_get` / `std::env::var` → `copy_nonoverlapping`,
which is **incidental** — it is merely the call that happened to touch the
guard page. Chasing it as an env/getenv bug is a dead end.

### Why the guard caused it

That cycle's ONLY re-entrancy breakers are two memo checks, and **both** are
`self.symbols.lookup(...)`:

- `try_register_bootstrap_global_symbol`: `if self.symbols.lookup(name).?: return true`
- `register_imported_symbol`: `val already_bound = self.symbols.lookup(local_name).?`

The commit message's premise was wrong. It asserted `self.scopes` is `{}` with
`current_scope` pointing at a scope id the dict does not hold. In fact
`SymbolTable.new()` **does** insert the id-0 root scope (`table.scopes[0] =
Scope(...)`) and `declare()` writes symbols into it. So scope 0 is present —
but `rt_dict_contains` **under-reports membership** on this struct-valued
`Dict<i64, Scope>` (the documented native struct-valued-Dict pitfall,
`doc/07_guide/language/dict_native_pitfalls.md`). The guard therefore hit
`break` on the first iteration every time, making `lookup()` a **constant nil**,
which silently disabled both breakers at once → infinite recursion.

Corollary: do **not** replace this with another `rt_dict_contains` on
`self.scopes` — any form of that predicate there is the same hazard. In-source
`DO NOT re-add` comments now mark both sites.

### RED / GREEN evidence

Both legs use the identical harness (seed → Stage 2 → Stage 3, faithful to
`bootstrap-from-scratch.sh`'s recorded command transcripts), differing only in
the presence of the guard.

| | Stage 2 | Stage 3 | last progress | stage3 binary |
|---|---|---|---|---|
| **RED** (guard present, tree `9393117a5fe`) | exit 0, `727 compiled, 0 cached, 0 failed`, 155.0s | **exit 139 / SIGSEGV**, 0-byte log | `tasks_done=2/6`, parse complete | **none** |
| **GREEN** (guard removed) | exit 0, `727 compiled, 0 cached, 0 failed`, 153.8s | **survives the crash point**, RSS climbs 3.1 → 4.6 GB doing real HIR lowering | past `tasks_done=2/6` | — |

RED was reproduced 3×: the original T3 run, a manual replay of its exact
recorded command (110 s to SIGSEGV), and a full seed→Stage2→Stage3 rebuild.
RED's Stage 3 died ~22 s after `tasks_done=2/6`; GREEN was still alive and
allocating minutes past that point, above RED's peak RSS.

The guard-present leg is itself the sabotage check: same harness, same inputs,
guard restored, exact same symptom (exit 139, 0-byte log, no binary).

### The SIGSEGV fix is preserved

Bug-doc `hello.spl` repro under gdb, run against **both** stage2 binaries:

- guard present: no signal, `error: bootstrap entry lowered to 0 MIR instructions`
- guard removed: no signal, **identical** message

Neither segfaults, so `switch_operators_calls.spl` alone is sufficient to stop
the original `try_lower_bitfield_construct` → `SymbolTable.lookup` fault (it
removes the `lookup()` call from that path entirely). Removing the guard does
not reintroduce it. The residual `0 MIR instructions` on the single-file
`hello.spl` path is unchanged by this fix and is a separate, pre-existing
limitation.

### Still open

Stage 3 is **not** yet a completed self-host — this change removes the
stack-overflow wall that stopped it immediately after parse. It is expected to
run on into HIR/MIR lowering and may still hit the previously documented
MIR-lowering blocker. "Progressed past the recursion crash" is the claim here,
not "Stage 3 succeeds".

Also still open, and now more clearly scoped: `rt_dict_contains` returning
false for a key that is present in a struct-valued `Dict<i64, Scope>`. That is
the underlying native-codegen defect; this change routes around it rather than
fixing it.

### Proof that GREEN is not just recursing more slowly

GREEN's Stage 3 climbs to >11 GB RSS while `progress.events` stays at
`tasks_done=2/6`, which on its own is ambiguous: it could mean the same cycle
still runs unbounded but now allocates per iteration (heap-dominated instead of
stack-dominated) rather than being fixed. The discriminator is the **stack**
segment, not RSS:

```
VmRSS:  11277948 kB
VmData: 11249832 kB
VmStk:       132 kB     <-- normal; a recursion this deep would be enormous
Threads:       1
```

`VmStk` is 132 kB — an ordinary stack. Essentially all memory is heap
(`VmData`). RED died *by exhausting the stack*; GREEN's stack never grows. The
runaway recursion is gone, not merely slowed. (`gdb -p` could not confirm this
directly: `/proc/sys/kernel/yama/ptrace_scope` is `1`, so attaching to an
already-running process is refused. `VmStk` answers the same question without
ptrace.)

Separately, and NOT fixed by this change: Stage 3's memory appetite past this
point is large and still growing at 11 GB. An earlier Stage 3 run was killed by
earlyoom at 81 GB VmRSS. Whether Stage 3 now completes, or instead runs into
that memory wall or the MIR-lowering blocker, is unresolved here and needs its
own run to settle.

## Update (2026-08-06, later): corroborated on 5 independently-rebuilt binaries — not this-worktree-specific

While attempting execution verification for
`mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md` (a
different feature, `Array.first()`/`.last()`), found four parallel worktrees
on disk (`~/dev/simple-s3clean`, `-s3red`, `-s3family`, `-s3fix`), each with
its own freshly self-hosted-rebuilt `bootstrap/stage3/.../simple` (built
20:20-21:07 today, all confirmed via `git merge-base --is-ancestor` to
include commits well past this bug's original repro) plus one
`release/x86_64-unknown-linux-gnu/simple`. Ran the same trivial
`fn main(): print("hello")` control case against all five: **all five
SIGSEGV**, `strace -f -e trace=memory` on one of them confirms the identical
`SEGV_MAPERR si_addr=0x118` fault immediately after the `uname -m`/`uname -s`
target-triple-detection subprocess pair, matching this doc's own reproduction
exactly. This rules out "stale/misconfigured single stage3 copy in one
worktree" as an explanation — the fault is present in every self-hosted
`native-build` rebuilt anywhere on this machine today, independent of
worktree or exact source revision (as long as it's after whatever introduced
this regression). No new investigation into the root cause was done in this
pass (out of scope for that task); recorded here purely as corroborating
reproduction evidence (five more runs, all matching this doc's own `0x118`
signature, on top of the 5/5 already on file) and to save the next
investigating lane from re-discovering "is this worktree-specific?".

**Related but distinct fault, NOT the same crash:** the same investigation
also ran `native-build` on inputs that hit a *fatal MIR-lowering error*
(4 collected errors, `mir_ok=false`) rather than a clean success — that path
returns before the `uname` target-triple-detection subprocess pair this
doc's `0x118` fault depends on, and `strace` shows a **different** fault
there: `SIGSEGV {si_code=SEGV_MAPERR, si_addr=NULL}`. Recorded as its own
open finding, not folded into this doc's `0x118` mechanism — see
`mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`'s
2026-08-06 "later" update for the exact repro and stderr capture.

## 2026-08-07 — symbolized backtrace; the "enum misclassification" diagnosis is FALSIFIED; this family is STILL OPEN

A lane was handed a "30-second reproduction": an 8-line program
(`enum Shape: Circle(i64)/Square(i64)` + `val s = Shape.Circle(7)`) that
SIGSEGVs the compiler at `rc=139`, with the diagnosis *"`Shape.Circle(7)` is
misclassified as an unresolved method call, lowered to a const-0 placeholder,
and then dereferenced."* That diagnosis does not survive a negative control.

**Harness under test.** `stage2-admitted/simple` (128 MB, self-hosted) from
`build/bootstrap-t3-redeploy-retry-20260806-cycle3/stage3/x86_64-unknown-linux-gnu/`,
replaying only the stage-3 `native-build` against a tiny entry, env mirrored
from `stage3-command.transcript`.

**Negative control (the finding).** Seven inputs, one binary:

| probe | program | rc |
|-------|---------|----|
| ER | `enum Shape` + `Shape.Circle(7)` | 139 |
| PB | `Option.Some(7)` | 139 |
| PC | `Shape.Circle(7)` + `match` | 139 |
| PD | bare `Some(7)` | 139 |
| PE | `Shape.Circle(7)` inside an uncalled fn | 139 |
| PG | `struct P: x: i64` + `P(x: 3)` | 139 |
| **PF** | **`fn main(): print "hi"`** | **139** |
| PA | `val s: Shape = .Circle(7)` | 1 (parse error — never reaches the backend) |

**`fn main(): print "hi"` SIGSEGVs.** The only non-139 run is the one that
fails at parse time and never reaches lowering. There is no green baseline on
this harness, so no crash observed on it can be attributed to any language
construct in the input. The enum program is not special.

**Symbolized backtrace (gdb, hello-world `print "hi"`).** This run carried
**no** `ulimit -v`, unlike the probe table above, and SIGSEGV'd on the same
`pF` program — so the memory cap used for the probes is exonerated as a
confound:

```
Program received signal SIGSEGV
#0  compiler__hir__hir_types__SymbolTable.lookup ()
#1  compiler__mir___MirLoweringExpr__switch_operators_calls__MirLowering.try_lower_bitfield_construct ()
#2  compiler__mir___MirLoweringExpr__switch_operators_calls__MirLowering.lower_call ()
#3  compiler__mir___MirLoweringExpr__expr_dispatch__MirLowering.lower_expr ()
#4  ... lower_stmt_impl / lower_stmt / lower_block_expected
#7  ... lower_function_with_gpu_metadata
#8  ... bootstrap_lower_flat_hir_module_to_mir
#10 compiler.driver.driver_bootstrap.bootstrap_lower_to_mir_context ()
#11 compiler__driver__driver_aot_pipeline__CompilerDriver.aot_compile ()
#12 app.cli.bootstrap_main.run_native_build_bootstrap ()
```

Not LLVM codegen, not the link path, not enum lowering: `SymbolTable.lookup`
walking a scope chain from `try_lower_bitfield_construct`.

**The binary is stale — but that does NOT close this family.**

- `stage2-admitted/simple` mtime: **2026-08-06 06:33:43 UTC**
- `1ea6599e8fb` *"fix(compiler): stop try_lower_bitfield_construct SIGSEGV,
  guard SymbolTable scope-chain reads"*: **2026-08-06 13:52:27 UTC**
- follow-up `030ff43e330` (15:27) removed the over-broad `rt_dict_contains`
  guard that had stack-overflowed Stage 3, keeping the correct
  `next_scope_id` range check.

The binary predates its own fix by 7h19m. That explains why *this*
backtrace lands in `try_lower_bitfield_construct` specifically — that call
site was repaired after this binary was built. **It does not explain
hello-world crashing at all.** This same doc records five stage3 binaries
rebuilt 20:20-21:07 on 2026-08-06 — i.e. *after* both `1ea6599e8fb` (13:52)
and `030ff43e330` (15:27) — all SIGSEGVing on `fn main(): print("hello")`
with `si_addr=0x118`. So `1ea6599e8fb` narrowed or moved the fault; it did
not close it. This addendum does not close it either. (The commit message of
the change that first added this section said "the fix is already on main";
that phrasing is superseded by this paragraph.)

`0x118` is consistent with a field read at offset 0x118 off a null `Scope`,
i.e. plausibly the same `SymbolTable` mechanism at a *different*
`lookup()` call site still reachable from `lower_call`. Flagged as the next
lane's entry point — **not proven**; the post-fix binaries on disk are
stripped, so a symbolized backtrace for them still needs an unstripped
rebuild.

The fix's code comment at
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:971-985`
describes this exact fault: on the bootstrap flat symbol table
(`bootstrap_flat_symbol_table`, `bootstrap_globals.spl`) `self.scopes` is `{}`
with `current_scope` at id 0, so `self.scopes[0]` reads past an empty dict and
returns a null `Scope` under native codegen — the next field read
(`scope.symbols`) SIGSEGVs. The fix is to use the symbol already resolved onto
the HIR node instead of re-resolving by name via `self.symbols.lookup()`.

**The enum fallthrough is a SEPARATE, still-open question — an earlier
draft of this section wrongly folded it into the crash above.** `lookup()`
walks `self.scopes`; `get_symbol_raw(id)` reads `self.symbols`. These are
different dicts, and reading the constructor body settles it:
`bootstrap_flat_symbol_table` (`bootstrap_globals.spl:302-307`) calls
`SymbolTable.new()` — which **does** create the id-0 root scope
(`hir_types.spl:229`, `table.scopes[0] = Scope(...)`; a grep for `scopes:`
shows only `scopes: {}` at :218 and misleads) — and then populates
`table.symbols[symbol.id.id]`. It leaves `scopes[0].symbols` and
`exact_symbols` empty. So on that table `get_symbol_raw(id)` **works**, and
`lookup(name)` returns nil rather than crashing. Consequences:

1. The `switch_operators_calls.spl:978-983` comment's premise ("`self.scopes`
   is `{}`") does not hold at origin/main. The guard is still right for other
   reasons, but the stated mechanism should be re-derived.
2. `recv_enum_name == ""` is therefore **not** explained by an unpopulated
   `symbols` dict. The remaining candidate is that `receiver.kind` matches
   neither `Var` nor `NamedVar` at that point. Unverified.

Hypothesis, with its disconfirming constraint, for whoever picks this up: the
`enum_variant_index` reclassification at
`50.mir/_MirLoweringExpr/method_calls_literals.spl:1046-1069` derives
`recv_enum_name` from `self.symbols.get_symbol_raw(rsym.id)`. On the same
unpopulated flat symbol table that returns nil, so `recv_enum_name` stays `""`
and the block would fall through to the unresolved-method path. This is
consistent with the traces (`[mir-method-call] enum-owner` printed, no return).
Corroborating: `Option.Some(7)` fell through identically even though
`"Option"` is registered unconditionally (`module_lowering.spl:895`,
`bootstrap_globals.spl:544/655`), so the index is not the problem. **What is
the problem was not established.** Confirm or kill it by dumping
`rt_enum_discriminant(receiver.kind)` at `method_calls_literals.spl:1046` —
which requires a rebuild, see the CTL control below.

**Two numbers cited as evidence are not garbage.** `disc=1851930204` and
`local=103079215111` (`0x1800000007`) are byte-identical across every probe,
including `Circle` and `Some`. Being byte-identical across unrelated inputs is
exactly as much as was proved: they are stable, hence not per-site
corruption. (`disc` is consistent with the name-hash discriminants the code
deliberately computes via `rt_enum_discriminant`, cf. the `[hir-field-type]`
traces; `0x1800000007` reads more like a packed LocalId than a sentinel —
neither reading is verified.) Do not root-cause from them.

**This harness cannot validate a compiler source fix.** Control: an `XYZZY`
marker was added to the const-0 warning string at
`method_calls_literals.spl:2673` in the compiled worktree; the run printed the
**original** string (0 hits). The probe entry imports nothing from
`src/compiler/**`, so the worktree's compiler sources are never read — the
prebuilt binary is authoritative. Any "prove the fix on the 30-second repro"
plan is unreachable by construction; validating a `50.mir` change requires a
full stage-2/3 rebuild.

**On the const-0 placeholder path.** No change is warranted. `origin/main`
already calls `self.error("unresolved method call: {method}", nil)`
(`method_calls_literals.spl:2664`) *and* emits `rt_panic` before the const-0
temp, and the comment there explains the const-0 def is retained deliberately:
removing it yields a use-before-def local (NULL `llvm::Value*` → ICmp SIGSEGV
in llvm-lib). The residual defect is not the warning — it is that
`driver_bootstrap.bootstrap_lower_to_mir_context` returns
`next_ctx.errors.len() == 0` and never copies `MirLowering.errors` into `ctx`
(unlike the default lane's `_driver_collect_mir_errors`), so the collected
error is dropped. That is the precise place to fix, and it is the same
already-documented Task #145 gap.

**Bearing on the rc=1 vs unbounded-RSS harness divergence:** none. Different
input (tiny entry vs full `bootstrap_main.spl`), so these runs do not
adjudicate it. One data point worth recording: a full-entry run on this same
cycle3 stage2 gave **rc=143 with no `error:` lines** — the external-kill/OOM
signature, consistent with (not proof of) the unbounded-RSS branch.

**Standing lesson.** A reproduction is only evidence if a control passes.
Before attributing a compiler crash to a construct in the input, compile
`fn main(): print "hi"` with the same binary and the same env. And check the
binary's mtime against the fix log before spending an hour on the source.

---

## 2026-08-07 — RESOLVED: the post-fix crash is NOT `SymbolTable.lookup`. Symbolized backtrace obtained; `0x517966` question CLOSED.

The open questions this doc carried — "why do post-`1ea6599e8fb` binaries still
SIGSEGV?" and "is this the same site as stage3's `0x517966`?" — are both
answered. **No new build was launched**; the answer came from an existing
*unstripped* post-fix binary that earlier lanes had left on disk.

### The unstripped post-fix artifact

`/home/ormastes/dev/simple-s3bisect/build/cyc/FIX8/stage2-simple`
(2026-08-06 20:06, 128 MB, `.symtab` + `.debug_info` present, 149,123 symbols).
Built by the Rust seed from **post-fix** source — verified in the lane worktree:
`switch_operators_calls.spl:973` carries `case HirExprKind.NamedVar(symbol, _)`
(the kept half of `1ea6599e8fb`) and `hir_types.spl:373,416` carry the
"DO NOT re-add ... `rt_dict_contains(self.scopes, ...)` guard" comments (the
reverted half). Sibling tags `FIX5/FIX6/FIX7/SAB5` are equally unstripped.

Stage-2 binaries are unstripped because the **seed** builds them and does not
strip; only the pure-Simple stage-3 driver drops debug info. **Any lane needing
symbols should reach for a stage-2 artifact before paying for a rebuild.**

### Hello-world reproduction (negative control, as required)

```
$ printf 'fn main():\n    print("hello")\n' > hello.spl
$ SIMPLE_RUNTIME_PATH=$RT SIMPLE_NO_STUB_FALLBACK=1 \
    <FIX8>/stage2-simple native-build --runtime-path $RT -o o2 hello.spl
Segmentation fault (core dumped)   rc=139        # BASELINE tag: identical
```

**Harness trap worth recording:** with `SIMPLE_BOOTSTRAP=1` added, the same
command instead exits **rc=1** with `error: bootstrap entry lowered to 0 MIR
instructions (ret-0 stub module)` — the crash is *masked*, not absent. A lane
that probes hello-world with `SIMPLE_BOOTSTRAP=1` set will conclude "no SIGSEGV"
and be wrong.

### Symbolized backtrace (verbatim)

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000005ae466 in compiler__borrow__borrow_check__mod__BorrowChecker.check_function ()

$1 = (void *) 0x98                 # si_addr
rax  0x90   rbx  0x6c193b1   r14  0x6c194f1   r15  0x91   rip  0x5ae466
=> 0x5ae466 <BorrowChecker.check_function+102>:  mov    0x8(%rax),%r14
   0x5ae46a <BorrowChecker.check_function+106>:  test   %r14,%r14
   0x5ae46d <BorrowChecker.check_function+109>:  jle    0x5ae4ad
   0x5ae46f <BorrowChecker.check_function+111>:  and    $0xfffffffffffffff8,%rbx

#0  0x00000000005ae466 in compiler__borrow__borrow_check__mod__BorrowChecker.check_function ()
#1  0x00000000005aef2e in compiler.borrow.borrow_check.mod.check_mir_module ()
#2  0x0000000000711c5c in compiler__driver__driver_pipeline_passes__CompilerDriver.borrow_check ()
#3  0x00000000007023b4 in compiler__driver__driver_aot_pipeline__CompilerDriver.aot_compile ()
#4  0x000000000049af6d in app.cli.bootstrap_main.run_native_build_bootstrap ()
#5  0x0000000000498217 in main ()
```

### `si_addr=0x118` / null-`Scope` hypothesis: REFUTED

- The crash is **not** in `SymbolTable.lookup`, and **not** in MIR lowering at
  all. It is in the **borrow checker**, a *later* pipeline pass
  (`aot_compile → borrow_check`), which is why the `1ea6599e8fb` MIR-lowering
  fix changed nothing.
- The faulting pointer is **not NULL**. `r15 = 0x91 = (18 << 3) | 1` — a
  **tagged small integer 18** read out of bounds. `si_addr` is simply
  `(value & ~7) + 8`, so it varies per run/build: `0x98` here, `0x118` in the
  stripped-stage3 report (`rax=0x110`). **Do not root-cause from the si_addr
  value**; it is derived, not diagnostic. There is no `Scope` involved.
- **This closes "Is this the same site as stage3's `0x517966`?" — YES.** The
  stripped-stage3 report's `rax=0x110`, `mov 0x8(%rax),%r14` + `test`/`jle`
  shape and its **6 user frames** match this backtrace instruction-for-
  instruction and frame-for-frame. The earlier "plausibly two distinct crash
  sites" working conclusion is superseded: it is one site.

### Root cause: cross-module field-index collision on `NLLChecker.errors`

Proven from disassembly of both sides of the module boundary in the same binary.

**Producer** — `NLLChecker.create` (`nll.spl`, defining module) allocates a
**0x28-byte (5-field)** object and stores `errors` at **0x20**:

```
5afe0f:  mov $0x28,%edi ; call rt_alloc
5afe19:  mov %rbx,(%rax)        # cfg                0x00
5afe1c:  mov %r14,0x8(%rax)     # borrow_graph       0x08
5afe20:  mov %r13,0x10(%rax)    # liveness           0x10
5afe24:  mov %r15,0x18(%rax)    # lifetime_inference 0x18
5afe28:  mov %r12,0x20(%rax)    # errors  <-- 0x20
```

`NLLChecker.check`, in the **same** module, agrees — it reads and writes
`self.errors` at `0x20(%rbp)` (`5aff55` / `5affc4`).

**Consumer** — `BorrowChecker.check_function` (`mod.spl`) reads the *same field*
at **0x58**, i.e. 88 bytes into a 40-byte object:

```
5ae44c:  and $~7,%r15
5ae450:  mov 0x58(%r15),%rdi    # nll.errors   <-- WRONG: slot 11, not slot 4
5ae458:  call rt_for_iterable   # returns the OOB garbage 0x91 unchanged
5ae466:  mov 0x8(%rax),%r14     # FAULT: list length read on a tagged int
```

**Slot 11 is not arbitrary.** A scan of every `class`/`struct` in
`src/{compiler,lib,app}` finds **exactly one** type with a field named `errors`
at index 11: **`MirLowering`** (`src/compiler/50.mir/mir_lowering_types.spl:41`).

The mechanism is documented by the offending function's own comment.
`MirLowering.resolve_field_index`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:934`) resolves a field
through a three-tier chain, and the **middle** tier is keyed by a numeric symbol
id:

```python
# tier 1 (SAFE, name-keyed):   struct_value_syms -> struct_field_order[value_name]
# tier 2 (UNSAFE, id-keyed):
val sym_id = self.symbol_id_value(found_type_sym)
if self.field_map.has(sym_id):
    val fields = self.field_map[sym_id]          # Dict<i64, [text]>
    ...                                          # returns idx of field_name
# tier 3 (SAFE, name-keyed):   struct_field_order[type_symbol.name]
0  # fallback
```

`field_map` is declared `Dict<i64, [text]>  # type symbol ID -> ordered field
names` (`mir_lowering_types.spl:42`), whereas `struct_field_order` is
`Dict<text, [text]>` (`:54`) — name-keyed. The function's own leading comment
already states the hazard:

> *"Numeric SymbolIds are local to each module and can collide in an
> entry-closure build. A lowered local's name-keyed provenance is therefore
> authoritative when available."*

An `--entry-closure` whole-program build shares **one** `MirLowering` (one
`field_map`) across all modules, so `NLLChecker`'s module-local type symbol id
in `55.borrow/borrow_check/mod.spl` **collides** with the id under which
`MirLowering`'s field list was registered. Tier 1 does not apply (the base is a
`var` from an imported static constructor, not a tracked struct value), so tier
2 wins with the *wrong class's* field list and returns `errors`'s index in
**`MirLowering`** — 11 — instead of 4. Tier 3, which is name-keyed and would
have been correct, is never reached.

Why only this one site: `BasicBlock.statements` (0x8), `BorrowGraph.errors`
(0x18) and `LifetimeInference.errors` (0x10) all read **correctly** across the
same module boundaries in this binary — a collision needs an id clash, so it is
sparse and data-dependent, which is exactly why it produced **no diagnostic at
all** (`FIX8/stage2.log` has zero `nll`/`borrow_check` warnings).

### Two stacked failures — note for whoever fixes this

1. `nll.check()` returned falsey for hello-world, which has no borrow errors.
   It returns `self.errors.is_empty()`, read at the *correct* 0x20 inside
   `nll.spl`; the falsey test is the `mov $0x80009,%ecx; bt` mask (values
   {0,3,19}). Worth confirming this isn't a second defect.
2. The consumer then read `errors` at the wrong 0x58 and faulted.

Fixing only (2) makes hello-world take the `Errors([])` branch — better, but not
obviously a green.

### Proposed fix (NOT landed — deliberately)

In `resolve_field_index`, make the name-keyed tier authoritative over the
id-keyed one: either move the tier-3 `struct_field_order[type_symbol.name]`
lookup **above** the `field_map[sym_id]` lookup, or validate a `field_map` hit
by confirming `type_symbol.name` matches the class that registered it. This is
what the function's own comment already prescribes.

**It is not landed because it cannot be verified right now, and this doc already
records what happens when an unverified fix to foundational compiler code is
landed** (the `hir_types.spl` "defense-in-depth" guard, which broke Stage 3
outright). Verification needs a stage-2 rebuild (~143 s, but ~32 GB RSS —
earlyoom SIGTERMed two such builds at 00:59 today at 32.7 GB and 32.0 GB). At
the time of writing, 67 GB were available with two foreign `native-build`
processes live, so the agreed gate (no other `native-build`, >=85 GB available)
was **not met**. **Sabotage-verification was therefore not performed and no
green is claimed.**

RED is already banked and is cheap to re-run: `FIX8/stage2-simple` on
hello-world is rc=139, reproducible on demand.

### Verification recipe for the next lane (~3 minutes of compute)

1. Apply the `resolve_field_index` reorder to a private worktree.
2. Rebuild **stage 2 only** with the seed — `/home/ormastes/dev/simple-s3bisect/build/cyc/build_stage2.sh <TAG>`
   is the exact recipe (seed `native-build --entry-closure --threads 16
   --entry src/app/cli/bootstrap_main.spl`); FIX8 took **143 s** (84 s compile +
   59 s link). A full stage 3 is **not** required to discriminate.
3. `objdump -d --start-address=0x... <new>/stage2-simple` on
   `BorrowChecker.check_function` and confirm the `nll.errors` read is `0x20`,
   not `0x58`.
4. Run hello-world: expect rc=0. Sabotage by reverting and re-confirming
   rc=139 + `si_addr = (garbage & ~7) + 8` in `check_function`.

**Standing lessons.**
- A stripped stage-3 is not a dead end: an unstripped **stage-2** built by the
  seed from the same source reproduces the identical site with full symbols.
  Check for one before budgeting an hour-long rebuild.
- `si_addr` here is `(tagged_value & ~7) + 8`. Two runs disagreeing on it
  (`0x98` vs `0x118`) is *not* evidence of two bugs.
- `SIMPLE_BOOTSTRAP=1` masks this SIGSEGV as a clean rc=1 diagnostic.

---

## 2026-08-07 — NEGATIVE RESULT: the `resolve_field_index` reorder is NOT verifiable at stage 2, and the "~3-minute stage-2-only recipe" cannot validate ANY `src/compiler` fix

The previous section proposed a one-line reorder in
`MirLowering.resolve_field_index`, deliberately did not land it, and left a
"~3 minutes of compute" stage-2-only verification recipe for the next lane. That
recipe has now been executed. **It cannot work, for a structural reason, and the
reorder is therefore still unverified and still NOT landed.**

### What was run

A hardlink copy of `simple-s3bisect` (the tree `FIX8` was built from) at
`/home/ormastes/dev/simple-fieldidx-lane`. Before editing, `resolve_field_index`
was confirmed **byte-identical** between that tree and `origin/main`, making
`FIX8` a true A/B control with the reorder as the only source delta. The reorder
applied was exactly the proposed one: the name-keyed tier
(`struct_field_order[type_symbol.name]`, `Dict<text, [text]>`) moved **above**
the id-keyed tier (`field_map[sym_id]`, `Dict<i64, [text]>`).

Three stage-2 builds via `build_stage2.sh` (copied, with `R`/`O` repointed;
`SEED` and `--runtime-path` unchanged). All `STAGE2_EXIT=0`.

### Result — the A/B, and the negative controls that explain it

| build | `nll.errors` read in `BorrowChecker.check_function` | hello-world |
|-------|-----------------------------------------------------|-------------|
| `FIX8/stage2-simple` (control, pre-reorder) | `5ae450: 49 8b 7f 58  mov 0x58(%r15),%rdi` | **rc=139** |
| `FIELDIDX1/stage2-simple` (post-reorder)    | `5ae4d0: 49 8b 7f 58  mov 0x58(%r15),%rdi` | **rc=139** |

Both hello-world runs were **without** `SIMPLE_BOOTSTRAP=1`, so the SIGSEGV is
unmasked (that env var turns this crash into a misleading clean `rc=1`).

The edit *was* compiled in — this is not a stale-binary artifact. The symbol
moved `0x5ae400` → `0x5ae480` (+0x80) and the build reported 727 compiled /
0 cached / 0 failed.

### Why: `stage2-simple` is emitted by the RUST SEED, so no `src/compiler` change can alter its machine code

This is the finding that matters, and it invalidates the recipe.

`build_stage2.sh` sets **`SIMPLE_NATIVE_BUILD_RUST=1`** and drives
`$RT/simple`. That binary is the **Rust seed** — 415 `rustc`/`cargo`/
`rust_begin_unwind` markers, and `nm` finds **no `resolve_field_index` symbol in
it at all**. Two positive/negative controls confirm the pure-Simple field
resolver never executes on this path:

- **PROBE1** — an instrumented build carrying three `[fieldprobe]` `print`
  statements inside `resolve_field_index`, gated on `SIMPLE_MIR_FIELD_TRACE=1`.
  Positive control: `strings` finds those 3 strings in
  `PROBE1/stage2-simple` and **0** in `FIELDIDX1/stage2-simple`, proving the
  edited file was read and compiled. Running that binary on hello-world with
  `SIMPLE_MIR_FIELD_TRACE=1` printed **0** `[fieldprobe]` lines (and still
  `rc=139`).
- **PROBE2** — the same build with `SIMPLE_MIR_FIELD_TRACE=1` set *during the
  build itself*, to catch the resolver while the compiler's own
  `borrow_check/mod.spl:77 val errors = nll.errors` is being lowered. The build
  log contains **0** `[fieldprobe]` lines.

So the `mov 0x58(%r15),%rdi` baked into every `stage2-simple` was emitted by the
**seed's** codegen. `stage2` is built by the seed; a change to
`src/compiler/50.mir/**` cannot move a single byte of it. Step 3 of the previous
section's recipe ("objdump the new `stage2-simple` and confirm the read is
`0x20`") is therefore unable to respond to the fix under test, in either
direction — and the RED/GREEN criterion it defines (hello-world `rc=0` on a
seed-built stage 2) is **unattainable by any `src/compiler` change**.

**Correction to commit `61197205501`.** That commit read `0x58` out of the
stripped stage 3, found the window byte-for-byte identical to the seed-built
stage 2, and concluded this "proves the 0x58 field index comes from pure-Simple
codegen". The identity does not license that inference: the stage-2 side of the
comparison is seed-emitted. What the identity actually shows is that *both*
codegens land on the same wrong index.

### The pure-Simple compiler does independently reproduce it

Confirmed here, so the `src/compiler` lead is not dead:
`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` — emitted by stage 2's
pure-Simple codegen — carries `517950: 49 8b 7f 58  mov 0x58(%r15),%rdi`
immediately before the faulting `517966: mov 0x8(%rax),%r14`.

That means the reorder still *might* be right. It simply cannot be tested below
a full **stage-3** build (~1 h, ~40 GB RSS), which the machine gate did not
permit during this lane. **Nothing is claimed green and no code was landed.**

### Verification budget — measured, and much cheaper than assumed for stage 2

Sampled `/proc/<pid>/status` `VmRSS` every second for a whole run:

- **stage-2-only build: peak 908 MB, 167.7 s** (107.3 s compile + 60.4 s link).
  Not 12 GB, not 32 GB. It runs safely alongside two 18–33 GB foreign builds.
- The "no other `native-build` AND >= 85 GB available" gate was written for a
  **full Stage-3** build (~1 h, ~40 GB — the workload earlyoom SIGTERMed twice
  at 00:59 on 2026-08-07). Applying it to a sub-1 GB job idles a lane for an
  hour for nothing. Gate on headroom relative to the measured peak
  (available >= 2x peak + 10 GB, floor 25 GB) and reserve the
  zero-concurrent-builds condition for the 40 GB class of job.

### What the next lane should do

1. **Do not re-run the stage-2-only recipe on a `src/compiler` change.** It is
   structurally blind. Either build stage 3, or find a path where the
   pure-Simple compiler is the one emitting the code under test.
2. If a stage-3 build is affordable, the fix to test is already written and A/B
   -ready (name-keyed tier above id-keyed tier in `resolve_field_index`); the
   `[fieldprobe]` instrumentation used here is the way to see which tier fires
   and why, and its `strings` presence/absence is a working positive control.
3. Note that `struct_field_order` **is** populated for classes on the bootstrap
   flat path (`50.mir/_MirLowering/bootstrap_globals.spl:589-591`,
   `sfo[class_def.name] = field_names`), and `NLLChecker`, `MirLowering`,
   `BorrowChecker` and `LifetimeInference` each have exactly one `class`
   declaration in `src/{compiler,lib,app}` — so if the name tier still misses,
   the reason is `self.symbols.get_symbol_raw(found_type_sym.id)` returning nil
   on the flat table, not an ambiguous name. `HirTypeKind.Named(symbol, args)`
   carries **no** name (`20.hir/hir_types.spl:783`), so there is no way to reach
   the name tier without a working symbol lookup — which is the next thing to
   verify.
4. The backend is **not** a second suspect: `translate_get_field`
   (`70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:190`) emits
   `getelementptr ... i32 {field}` straight from the MIR index, and the native
   isel does `val offset = field * 8`
   (`70.backend/backend/native/isel_x86_64.spl:391`). There is no name- or
   id-keyed layout table in `70.backend`. The index is decided solely in MIR.

### Standing lessons

- **Check which compiler emitted the bytes you are reading before attributing
  them.** A stage-2 binary is seed-emitted; only stage 3 and later are
  pure-Simple-emitted. A verification recipe that objdumps the wrong stage
  returns a confident, reproducible, meaningless answer.
- A clean A/B that shows *no change* is a result about the harness at least as
  often as about the fix. The +0x80 symbol shift proved the source was read,
  which is what made "the recipe is blind" the only surviving explanation.
- Put positive-control markers in **string literals**, not comments — a comment
  marker does not reach `.rodata` and silently fails the control (that happened
  here on the first attempt).

### PROBE3 — the seed-attribution above, converted from inference to direct evidence

The claim "no `src/compiler` change can move a byte of `stage2-simple`" initially
rested on an inference, and commit `61197205501` records a statement that cuts
the other way ("the seed's native-build runs
`src/app/cli/native_build_worker.spl`"). PROBE3 settles it. Every alternative
explanation for PROBE2's zero trace lines was closed:

- **Trace made unconditional.** The `field_name == "errors"` guard was removed;
  `resolve_field_index` now prints `[fieldprobe-entry] QUUXMARKER field={...}` on
  **every** entry, for every field of every type.
- **Positive control passes.** `strings PROBE3/stage2-simple | grep -c QUUXMARKER`
  = **1**. The edited file was read and compiled.
- **The env var reached the build process.** `tr '\0' '\n' < /proc/<pid>/environ
  | grep -c SIMPLE_MIR_FIELD_TRACE` = **1**, sampled live during the run — so
  `env -i` did not strip it.
- **stdout is captured.** `stage2.log` contains the build's own 4 output lines,
  so prints would have landed there.
- **There is no `.spl` worker to lose output to.** `pgrep -af native_build_worker`
  = **0** during the run; the build process has exactly one child thread
  (`simple-main`). The seed binary also contains **no** `native_build_worker`,
  `field_map` or `struct_field_order` string at all.

Result: **0** `[fieldprobe-entry]` lines across a 727-file compile.

The pure-Simple `MirLowering.resolve_field_index` is therefore not executed at
any point while the seed builds stage 2. The `0x58` in `stage2-simple` is
seed-emitted, the stage-2-only recipe is blind to `src/compiler` changes, and
`61197205501`'s worker statement does not hold for this build path
(`SIMPLE_NATIVE_BUILD_RUST=1`).

## Update (2026-08-07): field-index-collision fix IMPLEMENTED (module-qualified struct_field_order tier + conflict diagnostic)

The agreed durable fix for the borrow-checker field-index collision
(`resolve_field_index` reading `NLLChecker.errors` via `MirLowering`'s
layout) has landed:

- **`resolve_field_index` now consults a MODULE-QUALIFIED name tier FIRST**
  (`src/compiler/50.mir/_MirLowering/function_lowering.spl`): before the
  id-keyed `field_map` tier (whose per-module numeric SymbolIds collide in
  an entry-closure build) it resolves the base type's symbol and looks up
  `composite_layout_key`'s `'<defining_module>::<Name>'` key in
  `struct_field_order`. Those qualified keys were ALREADY being registered
  alongside the bare names (prescan + `lower_module`, both via
  `register_composite_field_metadata`) — but no lookup ever used them. A
  qualified hit is unambiguous and now wins over both the collided
  `field_map` tier and the bare-name tier (~1,522 duplicated class/struct
  names across `src/{compiler,lib,app}`).
- **Conflicting bare-name re-registration is no longer silent**
  (`src/compiler/50.mir/_MirLowering/module_lowering.spl`,
  `register_composite_field_metadata`): re-registering a bare name with a
  DIFFERENT field list prints a one-shot
  `[mir-lower] WARNING: struct/class name '<N>' re-registered with a
  DIFFERENT field list ...` naming both field lists and which side was
  kept. Identical re-registration stays silent; qualified keys are exempt.
  Warn-once bookkeeping: new `struct_field_order_conflict_warned` field
  (`src/compiler/50.mir/mir_lowering_types.spl`).

Interpreter-level verification (compiler `.spl` sources run LIVE under
`bin/simple test`):
`test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl` —
`SPEC FILE VERDICT: declared>=4 executed=4 passed=4 failed=0 dropped=0`.
The decisive case registers mod_a's `Config` (`errors` at index 2), poisons
`field_map` at mod_a's SymbolId with a colliding other-module layout
(`errors` at index 0), and asserts `resolve_field_index` returns 2.
Sabotage check: disabling the qualified tier flips exactly that case to
FAIL (passed=3 failed=1), so the spec discriminates the fix.

**Honest status:** the full ~40GB/~1h stage-3 rebuild + hello-world SIGSEGV
retest is PENDING — not run in this pass (box under heavy build contention,
load avg ~75; and the stage-2-only recipe is seed-emitted and structurally
blind to `src/compiler` edits, so only a full stage-3 run can observe this
change natively). Next stage-3 lane should retest hello-world and expect
the `[mir-lower] WARNING` lines to enumerate the real cross-module
collision family.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: FIX PRESENT IN SOURCE; runtime claim UNVERIFIED (needs stage3).**

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1088` has
`return self.try_lower_bitfield_construct_for_symbol(symbol, args)` in the
NamedVar branch, with the `:1080-1087` comment naming this bug id; no
`self.symbols.lookup()` remains in `try_lower_bitfield_construct` at `:1059`.
The SIGSEGV claim itself still requires a full stage-3 self-hosted run, which
per the governing fact was not available in this lane.
