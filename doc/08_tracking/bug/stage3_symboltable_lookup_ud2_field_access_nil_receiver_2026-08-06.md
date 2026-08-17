# Stage-3 native-build crash: `SymbolTable.lookup` traps "field access on nil receiver" (ud2), distinct from the offset-0x118 / NULL-deref SIGSEGVs

Status: FIX LANDED (interpreter-verified only, native-build unverifiable in
this checkout — see 2026-08-07 update). The original "codegen drops the
guard" root-cause theory below is WRONG (disproven by binary provenance, see
2026-08-06 update).
Date: 2026-08-06
Owner: unassigned

## Distinct from

`doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`
(offset-0x118 SIGSEGV and a NULL-deref SIGSEGV). This bug is a **SIGILL on `ud2`**
with message `runtime error: field access on nil receiver`, not a SIGSEGV. Do not
merge into that doc — another session owns it and is mid-edit
(local copy 352 lines vs `origin/main` 481 lines as of this writing).

## Repro

Deterministic — reproduced 3 times independently:

1. Cold-cache direct `stage2 native-build` of the compiler's own `src/compiler` tree.
2. Warm-cache build via `~/dev/simple-s3clean/build/clean/stage2-simple`,
   cache dir `native-objects-BvXGkY`.
3. A leftover artifact from an unrelated prior lane,
   `~/dev/simple-s3clean/build/clean/stage3.log` (~20:45 same day), shows the
   identical trailing signature (last MIR-lowering events before the trap: a
   `method-dispatch` for `.ends_with(...)`, then one for `.replace(...)`, then
   four more `int:*` literal-lowering events, then the trap — byte-for-byte
   identical tail across runs).

A companion `stage3-gdb.log` (already captured by gdb by an earlier lane, same
directory) has a full backtrace:

```
Program received signal SIGILL, Illegal instruction.
0x00000000005c37ed in compiler__hir__hir_types__SymbolTable_dot_lookup ()
#0  SymbolTable_dot_lookup
#1  switch_operators_calls::MirLowering.lower_enum_construct_named
#2  expr_dispatch::MirLowering.lower_expr_impl
#3  expr_dispatch::MirLowering.lower_expr
#4  mir_lowering_stmts::MirLowering.lower_stmt_impl / lower_stmt
#5  function_lowering::MirLowering.lower_block_expected / lower_block
#6  function_lowering::MirLowering.lower_function_with_gpu_metadata / lower_function
#7  bootstrap_globals::bootstrap_lower_flat_hir_module_to_mir(_for_target)
#8  driver_bootstrap.bootstrap_lower_to_mir_context
#9  driver_aot_pipeline::CompilerDriver.aot_compile
#10 driver_orchestration::CompilerDriver.compile
#11 driver.compiler_driver_run_compile → app.cli.bootstrap_main.run_native_build_bootstrap → spl_main → main
```

Command to reproduce fresh (slow — self-compiling the whole `src/compiler` tree):
```
cd ~/dev/simple-s3clean/build/clean
gdb --batch -ex run -ex bt -ex "disassemble compiler__hir__hir_types__SymbolTable_dot_lookup" \
  --args ./stage2-simple native-build <stage3 build invocation as used by the lane>
```

## Root cause

`SymbolTable.lookup` (`src/compiler/20.hir/hir_types.spl:368-399`):

```
fn lookup(name: text) -> SymbolId?:
    var scope_id = self.current_scope
    loop:
        if not rt_dict_contains(self.scopes, scope_id.id):
            break
        val scope = self.scopes[scope_id.id]        # line 385
        if rt_dict_contains(scope.symbols, name):
            val found: i64 = scope.symbols[name]
            return SymbolId(id: found)
        match scope.parent:
            case Some(parent): scope_id = parent
            case nil: break
    nil
```

The comment at lines 372-382 says this exact guard (`rt_dict_contains` before the
bracket read) was **already added** to fix
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06` (a prior SIGSEGV
on `scope.symbols` when `scope` was a null `Scope` pointer). The crash reproduced
here happens at the *same call site*, meaning the guard is not actually
protecting the read in the compiled binary.

Disassembly of `compiler__hir__hir_types__SymbolTable_dot_lookup` from
`stage2-simple` (`gdb -batch -ex "disassemble ..."`) shows, in instruction order:

- `+75..+211`: three back-to-back null-pointer guards (each: mask low 3 tag
  bits, `test`, `jne` past a `ud2` trap) on `self`, then on `self+0x8`
  (presumably `self.scopes`), then on the value pulled from the stack slot that
  cached `self.scopes` earlier at `+85..+93` (`mov 0x10(%rdx),%rax` /
  `mov %rax,(%rsp)`).
- `+211..+225`: `mov (%rsi),%rsi; shl $3,%rsi; call rt_index_get` — this is the
  compiled form of `self.scopes[scope_id.id]` (line 385).
- `+227..+262`: `and`-mask + `test` + `jne` on the **result** of that
  `rt_index_get` call, and if it is nil/zero, **falls through to the
  `eprintln("field access on nil receiver") + ud2` trap** — this is the crash
  site (`rip = 0x5c37ed`, the `ud2` at `+262`).

Critically: **there is no call to `rt_dict_contains` anywhere in the
0x0..+262 instruction range.** The only `rt_dict_contains` call in the function
is later, at `+271` (`call *%r11 <rt_dict_contains>`), which is the *second*
guard in the source (`if rt_dict_contains(scope.symbols, name)` at line 389),
operating on the dereferenced `scope` — i.e. it runs only *after* the crash
site, so it cannot be what's missing.

This means the codegen for `if not rt_dict_contains(self.scopes, scope_id.id):
break` immediately followed by `val scope = self.scopes[scope_id.id]` did not
compile into "call rt_dict_contains, branch on its boolean result, only then
call rt_index_get." Instead the visible machine code goes straight to
`rt_index_get` and treats a nil result as a **fatal trap**, not as the
intended "loop `break`" control-flow the source asks for. In other words: the
source-level `rt_dict_contains(...)` guard added for the earlier bug is not
reflected in the generated code for this call site — the MIR/codegen layer
appears to have collapsed the `contains-check → bracket-read` idiom into a
bare bracket-read whose failure mode is "nil receiver trap" rather than "loop
break", silently reintroducing the exact class of bug the guard was meant to
close.

This matches the already-documented native-codegen Dict pitfalls
(`doc/07_guide/language/dict_native_pitfalls.md`, and repo memory:
"Never call `.get()`/rely on bracket-read parity with `contains_key`") but is a
new, more specific instance: even the *recommended* `contains_key(k)` +
`d[k]` two-step idiom does not reliably gate the bracket read once inlined
into a hot loop across function-call boundaries in native codegen — the guard
call is either optimized away or its result isn't threaded into the
subsequent read's control flow.

## What's NOT yet known

- Whether `scope_id.id` genuinely is a missing key at this point (i.e. this is
  legitimately supposed to `break` per the loop's own logic and the codegen
  bug is purely "guard doesn't gate the read"), or whether `self.scopes` is a
  stale/copied struct field whose backing dict differs between the
  `rt_dict_contains`-intended-call and the `rt_index_get` call. Disassembly is
  consistent with the former (no `rt_dict_contains` call exists in the crash
  path at all) but this wasn't confirmed with a source-level MIR dump.
- Which specific compiler source construct in `src/compiler` triggers this scope
  lookup during self-compilation — the `stage3.log` / `stage3-gdb.log` debug
  traces are pure MIR-lowering event logs with no filename/module markers, and
  the crash is deterministic on *some* enum-construct expression reached via
  `bootstrap_lower_flat_hir_module_to_mir`, not on user-visible source text.
  `bootstrap_flat_symbol_table` (referenced in the source comment at
  hir_types.spl:374) only populates the flat `symbols` map and never calls
  `push_scope()`, which is exactly the precondition the existing comment
  already anticipated as scope-id/scopes-dict mismatch-prone.

## Suggested next step (not done — needs a full stage2→stage3 rebuild per
iteration, which is slow)

Add a temporary `eprintln` immediately before line 385 printing `scope_id.id`
and `rt_dict_contains(self.scopes, scope_id.id)`'s boolean result explicitly
computed in a local `val`, to see whether the *source-level* boolean the
codegen should be branching on is true or false at the crash. If it evaluates
false in the interpreter/JIT (not just miscompiled native), the bug is in
`bootstrap_flat_symbol_table` producing a `current_scope` that's absent from
`scopes` for a legitimate `SymbolId` seen during enum-construct lowering — a
pure MIR-lowering issue, not a Dict-codegen issue. If it evaluates true and
still crashes only under native codegen, the bug is squarely the
contains-check-not-gating-the-read codegen issue described above.

## Files referenced

- `src/compiler/20.hir/hir_types.spl:368-399` (`SymbolTable.lookup`)
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (`lower_enum_construct_named`, caller)
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` (`bootstrap_lower_flat_hir_module_to_mir`, `bootstrap_flat_symbol_table`)
- `~/dev/simple-s3clean/build/clean/stage3.log`, `stage3-gdb.log` (crash evidence, not in repo — local build artifacts)

## Update (2026-08-06, later): root-cause premise disproven — binary provenance mismatch, guard already tried and reverted upstream

Followed the task's cheapest-diagnostic instruction (write a minimal
standalone reproducer, native-build it in isolation) before doing a slow full
self-compile. The reproducer (`struct`+`Dict`+guard-then-bracket-read in a
loop, `lookup(t, name)` called twice, once with a deliberately-unregistered
scope id) behaved **correctly under the interpreter** — the guard fired,
printed a message, and broke the loop as intended (`bin/simple run` output:
`guard fired: break (scope_id=1 not in scopes)` / `not found (expected via
guard break)`).

`native-build` on that same reproducer, and even on an **existing, known-good
repo fixture** (`test/fixtures/compiler/stage4_struct_enum_array_probe.spl`,
already covered by `scripts/check/check-cranelift-aot-aggregates.shs`) and on
a **trivial `struct Point` hello-world**, all failed identically with
`unresolved name: <every identifier in the file>` from the self-hosted
worker. This is a harness-broken-in-this-checkout finding, not a defect in
the reproducer: `bin/simple` in this worktree currently prints the Rust-seed
warning banner (`WARNING: this Rust-built Simple binary is a bootstrap seed
only`) even though `.claude/rules/bootstrap.md`/CLAUDE.md says the deployed
tool should be the pure-Simple self-hosted binary — the deployed binary here
is not what it claims to be, and/or `src/compiler/**` is mid-edit by
concurrent sessions in this shared repo (`git status` at session start showed
it heavily modified). Native-build could not be used to test the isolated
guard-codegen hypothesis in this checkout. **Do not repeat this attempt in
this worktree without first re-verifying `bin/simple`'s provenance
(`readlink -f`, and does it still print the seed banner).**

Escalated instead of continuing to guess at flags. That surfaced the real
answer via a much simpler check the original repro never did: **verify the
binary that was actually disassembled was built from the source this doc
quotes.** It was not.

`stage3-gdb.log`/`stage3.log` (the evidence this doc's "Root cause" section
above is built on) came from `~/dev/simple-s3clean/build/clean/stage2-simple`
— **a separate git clone**, not this repo
(`/home/ormastes/dev/pub/simple`), created 2026-08-06 20:20 and rebuilt
2026-08-06 20:41:55. Checking that clone's actual
`src/compiler/20.hir/hir_types.spl` at the time of the build:

```
$ grep -n "rt_dict_contains(self.scopes" ~/dev/simple-s3clean/src/compiler/20.hir/hir_types.spl
(no output — the guard is NOT present)

$ sed -n '373,391p' ~/dev/simple-s3clean/src/compiler/20.hir/hir_types.spl
            # DO NOT re-add an `if not rt_dict_contains(self.scopes,
            # scope_id.id): break` guard here. It was added as
            # "defense-in-depth" by 1ea6599e8fb and it broke the Stage 3
            # self-host outright: ... rt_dict_contains under-reports
            # membership on this struct-valued `Dict<i64, Scope>` ...
            # The guard therefore ended the chain immediately and made
            # lookup() a constant nil ...
            val scope = self.scopes[scope_id.id]
```

`~/dev/simple-s3clean` has its own git history (`.git` present, distinct
worktree) with two relevant commits:

- `1ea6599e8fb` "fix(compiler): stop try_lower_bitfield_construct SIGSEGV,
  guard SymbolTable scope-chain reads" (2026-08-06 13:52:27) — added
  **exactly** the `rt_dict_contains(self.scopes, scope_id.id)` guard this
  doc's original "Root cause" section quotes as source, to fix
  `stage3_native_build_segv_generic_codegen_link_path_2026-08-06`.
- `030ff43e330` "fix(compiler): remove SymbolTable scope guard that
  stack-overflowed Stage 3" (2026-08-06 15:27:11) — **reverted it**, with a
  detailed writeup: the guard made `lookup()` return constant `nil` because
  `rt_dict_contains` under-reports membership on this struct-valued
  `Dict<i64, Scope>` (the documented native Dict pitfall class, see
  `doc/07_guide/language/dict_native_pitfalls.md`), which silently disabled
  the *only* re-entrancy breakers in a mutual-recursion cycle
  (`lower_type -> lower_named_kind -> try_register_bootstrap_global_symbol ->
  register_imported_symbol -> ... -> lower_type`), causing unbounded
  recursion and a stack-overflow SIGSEGV. In-source "DO NOT re-add" comments
  were left specifically to stop exactly what happened next.

Both commits are on `origin/main` (`git merge-base --is-ancestor 030ff43e330
origin/main` → true) as of this session. **This repo's local checkout
(`/home/ormastes/dev/pub/simple`) has an uncommitted working-copy edit that
re-adds the exact reverted guard**, with a *different* justification comment
(citing the SIGSEGV bug doc, not knowing about the revert). `git log --all -S
"rt_dict_contains(self.scopes"` in this repo confirms the guard is not the
committed state anywhere on this repo's line of history either — it exists
only as an uncommitted WC diff here, `git diff origin/main --
src/compiler/20.hir/hir_types.spl` showed the **entire** diff was this one
guard hunk (59 lines, both `lookup` and `lookup_or_invalid`), byte-for-byte
the inverse of `030ff43e330`.

**Conclusion: the "codegen dropped the guard" theory (hypothesis 2 from the
task framing) is disproven.** The disassembly in the original "Root cause"
section is *exactly consistent with its actual source* — there is no
`rt_dict_contains` call before the crash site because the binary that was
disassembled was built from a checkout where that call genuinely is not in
the source. The doc's mistake was assuming the disassembled `stage2-simple`
was built from this repo's WC (with the guard) when it was actually built
from an unrelated sibling clone (without the guard, deliberately, for a
documented reason).

**Action taken:** reverted this repo's WC to match `origin/main` exactly for
`src/compiler/20.hir/hir_types.spl` (`git show origin/main:... >
src/compiler/20.hir/hir_types.spl`; diff against `origin/main` is now empty).
Re-adding the `rt_dict_contains`-based guard is not a safe fix — it was
already tried, and already causes a documented, worse failure (unbounded
recursion / stack overflow) via the same struct-valued-Dict membership-check
defect this session's task description also flagged as worth checking against
`dict_native_pitfalls.md`.

**This means the underlying bug is real and still genuinely OPEN on
`origin/main` as of this session** — hypothesis 1 (scope-tracking bug),
refined: `current_scope` can legitimately reference a scope id `bootstrap_flat_symbol_table`
never pushed into `scopes` (per `030ff43e330`'s own commit message,
`new()`/`declare()` DO populate an id-0 root scope correctly, so this is
likely a narrower/rarer case than "always nil", consistent with the ud2 crash
being much less frequently hit than the guard-caused stack overflow was).
Without a safe way to test scope-id membership on this struct-valued dict
under native codegen (`rt_dict_contains`/`.contains_key()` both go through
the same runtime call and are the only documented membership check;
`.keys()` + linear scan was not attempted or verified here), no fix is landed
in this session. The two known-bad options are: (a) no guard → nil-scope ud2
crash (this doc), (b) `rt_dict_contains` guard → false membership-check
failure → stack-overflow crash (`030ff43e330`). Next lane needs either (i) a
verified-correct membership check for `Dict<i64, Scope>` under native codegen
(test in isolation once native-build is usable in a clean worktree — this one
currently is not, see above), or (ii) a fix at the source: make
`bootstrap_flat_symbol_table`/its callers never set `current_scope` to an id
absent from `scopes` in the first place, which sidesteps the need for a
runtime guard entirely.

Not done in this session (blocked by the native-build harness issue in this
checkout): confirming whether `scope_id.id` is genuinely absent from
`self.scopes` at the ud2 crash site (the task's suggested `eprintln`
diagnostic), and testing a `.keys()`-based membership check in isolation.

## Update (2026-08-07): third guard strategy landed — Dict-free scope-id range check, plus a narrowed root-cause candidate

### Root-cause narrowing (read-only, no live testing needed)

Grepped every `push_scope`/`pop_scope` call site in `src/compiler/`
(`self.symbols.push_scope`/`.pop_scope`, plus a few unrelated
`env.push_scope`/`narrowing.push_scope` families that are different types).
**All** `SymbolTable.push_scope`/`pop_scope` calls live under
`src/compiler/20.hir/hir_lowering/**` (HIR lowering: `statements.spl`,
`_Items/declaration_lowering.spl`, `expressions.spl`,
`_Items/trait_impl_lowering.spl`). **Zero** hits anywhere under
`src/compiler/50.mir/**`, which is the phase in the crash backtrace
(`bootstrap_lower_flat_hir_module_to_mir` -> `lower_enum_construct_named` ->
`self.symbols.lookup`).

The `SymbolTable` used by `lower_enum_construct_named` (`self.symbols` inside
`MirLowering`) is built fresh per module by `bootstrap_flat_symbol_table`
(`src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:302-307`):

```
fn bootstrap_flat_symbol_table(module_index: i64) -> SymbolTable:
    var table = SymbolTable.new()
    val flat_symbols = bootstrap_hir_module_symbols_at(module_index)
    for symbol in flat_symbols:
        table.symbols[symbol.id.id] = symbol
    table
```

This populates the flat id->symbol `Dict<i64, HirSymbol>` directly, bypassing
`define()` entirely, and never calls `push_scope()`. So structurally, for
this specific `SymbolTable` instance, `current_scope` should be
`ScopeId(id: 0)` for its entire lifetime and `self.scopes` should hold
exactly `{0: <root Scope>}` (`next_scope_id == 1`) — there should be no way
for `scope_id.id` to ever be out of range in this code path. That the crash
happens anyway during this exact call chain means one of:

- `self.current_scope` (a struct-typed field, `ScopeId`, on a `class`
  instance) reads back corrupted/stale under native codegen — consistent
  with this repo's broader catalog of native-codegen struct-field/value
  corruption (`.claude/memory` "Engine divergence" section: JIT/native
  miscompiles chained methods, module globals, spilled locals, etc.), or
- some other MIR-lowering path aliases/replaces `self.symbols` with a
  different `SymbolTable` instance that legitimately did call `push_scope`
  elsewhere (not found by this grep, so not confirmed), or
- `scope_id.id` is not actually corrupted but the disassembly's `ud2` branch
  is reached via a completely different code path than assumed (unconfirmed
  without a working native-build harness in this checkout — see prior
  update).

None of these were confirmed live (native-build is still broken in this
checkout, see below). But the finding is useful independent of which one is
true: **whatever the true cause, a Dict-free, exact scope-id validity check
closes the crash without reintroducing either previously-tried failure
mode**, described next.

### The fix: `next_scope_id` range check instead of `rt_dict_contains`

`self.scopes` is append-only: `push_scope` (`hir_types.spl:525-539`) is the
**only** writer, and it always does `self.scopes[raw_id] = Scope(...)`
*before* `self.next_scope_id = raw_id + 1`. Nothing anywhere in
`hir_types.spl` (or, per the grep above, anywhere else) ever removes a key
from `self.scopes`. Therefore, for the entire lifetime of any `SymbolTable`:

```
scope_id.id in self.scopes  <=>  0 <= scope_id.id < self.next_scope_id
```

is an **exact** identity, not an approximation. The right-hand side is a
plain scalar `i64` comparison against a scalar `i64` class field
(`next_scope_id`) — it never touches `self.scopes` (the buggy struct-valued
`Dict<i64, Scope>`) or calls `rt_dict_contains`/`.contains_key()` at all, so
it cannot exhibit the documented false-negative membership bug that made
guard attempt #2 (`1ea6599e8fb`) disable the HIR bootstrap-global
recursion breakers and stack-overflow Stage 3 (`030ff43e330`'s finding). It
also can't reproduce failure mode #1 (no guard, ud2 trap on a genuinely
out-of-range id), since the bracket read is now unreachable whenever
`scope_id.id` is out of range.

Landed in both `SymbolTable.lookup()` and `SymbolTable.lookup_or_invalid()`
(`src/compiler/20.hir/hir_types.spl`, right before each function's
`val scope = self.scopes[scope_id.id]` bracket read):

```
if scope_id.id < 0 or scope_id.id >= self.next_scope_id:
    break
val scope = self.scopes[scope_id.id]
```

Both existing "DO NOT re-add `rt_dict_contains(...)`" comments are kept
verbatim (that specific guard is still known-bad) with an added note
pointing at this range-check replacement.

### Verification performed (interpreter only — native-build unusable in this checkout)

`bin/simple` in this worktree is still the Rust-seed binary
(`readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
prints the seed warning banner), same finding as the prior update. Per
`.claude/rules/testing.md`, `bin/simple test` hard-defaults to the tree-walk
interpreter regardless, so it exercises the new source-level logic (not
native codegen, and not proof the *original* ud2 crash — which is
native-only — is gone) but does verify the guard doesn't break existing
scope-chain resolution behavior.

New spec:
`test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl` — 5
examples: (1) `lookup()` finds a name defined in the valid root scope; (2)
`lookup()` walks a pushed child scope up to the root and `pop_scope()`
correctly hides the child-only name again afterward (guards against a
"break too eagerly" regression); (3) `lookup()` does not crash and returns
`nil` when `current_scope` is force-set (`symbols.current_scope =
ScopeId(id: 999)`, simulating the corrupted/never-pushed scope id from the
filed bug) past `next_scope_id`; (4) `lookup_or_invalid()` returns
`SymbolId(id: -1)` (`is_valid() == false`) under the same condition; (5) a
negative `scope_id.id` also breaks cleanly. Run via
`bin/simple test test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl`:
`Results: 5 total, 5 passed, 0 failed`.

**What's still NOT verified**: whether this actually eliminates the
*original* native-codegen ud2 crash from the 2026-08-06 backtrace (that
requires a working stage2/stage3 native-build in a clean checkout, which
this worktree does not have — see the "binary provenance mismatch" update
above). Also not confirmed: which of the three root-cause candidates listed
above is the real one. The range-check fix is correct and safe regardless of
which candidate is true (it's a strict superset guard: it fires only when
the existing bracket read would otherwise be unsafe), so it does not need
that answer to be safely landed — but a future lane with a working
native-build harness should still (a) confirm the ud2 crash is gone on a
full stage3 self-compile, and (b) if time permits, add a one-shot
`eprintln` at the new guard's `break` branch to see whether it is ever
actually hit during a real self-compile (if it's never hit, the true crash
cause was probably candidate 3 above — a different code path — and this fix,
while still correct, would not be why the crash stopped).

## Update (2026-08-17): the landed guard covered 2 of 5 bracket reads — the other 3 are now guarded too

Re-classified by CONTENT. The 2026-08-07 `next_scope_id` range check IS present
in current source: `src/compiler/20.hir/hir_types.spl:432` (`lookup`) and `:461`
(`lookup_or_invalid`), with both "DO NOT re-add `rt_dict_contains`" comments
intact. The invariant it relies on is sound: `new()` and `reset_module()` both
insert scope 0, and nothing ever removes a key from `self.scopes`.

**But the fix was incomplete, and the gap is the same defect, not a new one.**
At committed HEAD, `git show HEAD:src/compiler/20.hir/hir_types.spl | grep -n 'self.scopes\['`
lists **five** reads keyed by a scope id:

```
292:            val scope = self.scopes[self.current_scope.id]   # declare(), type-symbol path
321:        var scope = self.scopes[self.current_scope.id]       # declare(), all symbols
325:        self.scopes[self.current_scope.id] = scope           # declare(), write-back
434:            val scope = self.scopes[scope_id.id]             # lookup()          GUARDED
463:            val scope = self.scopes[scope_id.id]             # lookup_or_invalid GUARDED
587:        val scope = self.scopes[self.current_scope.id]       # pop_scope()
```

`declare` and `pop_scope` were left bare. They are reachable with precisely the
corrupted `current_scope` this doc's own root-cause candidate #1 postulates
("`self.current_scope` reads back corrupted/stale under native codegen"), and a
missing struct-valued-Dict bracket read yields a nil receiver whose first field
access is the same fatal `ud2`. Guarding `lookup` alone does not close the class.

### Changed (this session)

- `declare()` — same Dict-free range check, recovering to the always-present
  root scope 0 rather than breaking, so the symbol is still registered and
  still findable (a guard that merely swallowed the write would be worse than
  the crash).
- `pop_scope()` — same check; there is no parent to walk to from a bogus id, so
  it resets to root and returns.
- `push_scope()` — **reordered** to insert `self.scopes[raw_id]` BEFORE
  advancing `next_scope_id = raw_id + 1`. It previously advanced first, which
  made the guards' own comments literally false ("always inserting ... before
  advancing") and left a window in which `next_scope_id` admitted a key
  `self.scopes` did not yet hold — i.e. every range guard in the file silently
  degraded to the unguarded, trapping behaviour inside that window.

No `rt_dict_contains`-based guard was reintroduced anywhere.

### Verification

Interpreter only, and that limitation is unchanged from the 2026-08-07 update:
`bin/simple` here is the Rust seed (banner + mtime 2026-08-16 22:59), and
`bootstrap/stage3/simple` is a 3.4 MB `simple-bootstrap` stub that SIGSEGVs
(rc 139, core dumped) even on `fn main(): print("hi")` — the control fails, so
it cannot witness a native-codegen defect. **The native `ud2` is still not
proven fixed, and nothing here should be read as claiming it is.**

Detection spec added:
`test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl` —
asserts the invariant across entry points (`declare` non-type path, `declare`
type/first-write-wins path, `pop_scope` corrupted, `pop_scope` valid-pop
non-regression, the `push_scope` insert-before-advance ordering, and the
one-past-the-end id), so re-guarding a single function cannot make it pass.
