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
