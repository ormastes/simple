# Stage 3 at `origin/main` clears HIR entirely and dies at `phase4:monomorphize` (arm64-darwin, 2026-08-24)

## What was run

Sanctioned lane only, in an isolated clean `git worktree --detach` at
`origin/main` `ee98a2c3222` — never the shared working tree.

```
# Stage 2 (the sole receipt-free lane)
bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<wt>/build/bootstrap
  -> "Stage 2 admitted; stopping before Stage 3 as requested."
     stage2 sha256 1db26649ff88eeb99dd89caef716f5491625c1fde3c286021b3bf86fda8ab752
     stage2-provenance.receipt + stage2-sanity.receipt written

# Stage 3 admission
bootstrap-from-scratch.sh planner-admission-v2 --target=//bootstrap:stage3 \
    --reason=seed-missing --parent-compiler=<stage2> --bootstrap-output=<wt>/build/bootstrap
  -> bootstrap-admission: produced .../planner-admission-v2.env

# Stage 3
bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/bootstrap \
    --bootstrap-receipt=.../planner-admission-v2.env
```

Two invocation facts worth recording, both cost a cycle:

* the receipt to pass is the **29-field `planner-admission-v2.env`**, not the
  one-line `authorization.receipt` — the latter is rejected as
  `planner-admission-v2-unbound` / `malformed-or-untrusted-planner-admission-v2`;
* `--resume-stage3-from-admitted` requires a **repo-relative** output path
  (`build/bootstrap`). An absolute path yields
  `ERROR — nothing was checked (OUTPUT_DIR must be a repo-relative path without .. components: ...)`.

The isolated worktree was the right call: Stage 3's git-state gate recorded
`git-state-before.env` == `git-state-after.env`
(`head=ee98a2c3222…`, `dirty_fingerprint=225b134c…` on both sides), so the gate
that silently fail-closes on a moving tree was satisfied. Both cache-scope
ownership gates passed:
`PASS — 1 marker checked, .../stage2-native-cache owned by lane 'stage2'` and
the same for `stage3`.

## Result: SIGSEGV at `phase4:monomorphize`, no artifact

```
[BOOTSTRAP-PHASE] +517800ms phase3:hir_typecheck:done
[build] hir unknown/unknown step 3/6 +517800ms dt=0ms complete
[BOOTSTRAP-PHASE] +517800ms phase4:monomorphize:start
[build] monomorphize 0/unknown step 3/6 +517800ms dt=0ms start
[build] monomorphize 0/unknown step 3/6 +517800ms dt=0ms specialize
.../scripts/check/lib/bootstrap-stage3/command-snapshot.shs: line 182:
  69697 Segmentation fault: 11   env -i "HOME=..." "PATH=..." ... exec "$@"
```

No `stage3/aarch64-apple-darwin/simple`, no `provenance.env`, no `full/`.
**Stage 4, Stage 5 and any deployment are therefore unreachable.** Nothing was
deployed.

## The frontend is now CLEAN — this is forward progress over RUN 9

Measured in the same log:

| | RUN 9 (`stage3_hir_imports_memory_explosion_...`, at `cde14a`-era) | this run (`origin/main`) |
|---|---|---|
| outcome | rc=1 on HIR semantic errors | SIGSEGV at monomorphize |
| `HIR lowering error` lines | present, blocking | **0** |
| `hir_finalize` | — | **947/947** |
| `post_hir_validate` | — | **692/692** |
| `unresolved type` | 761 over 295 modules, then ~2050 over ~590 | **427 over 692 modules** |
| furthest phase | `phase3:hir_typecheck` | `phase3:hir_typecheck:done`, then `phase4` |

The remaining 427 `unresolved type` lines are non-fatal and are dominated by
generic builtins — `Option` 151, `Result` 103, `Dict` 98, `fn` 8, `HirType` 5,
`T` 2, `Span` 2, `HirSymbol` 2. The `driver_riscv_gen2_product`
field-visibility set and the large `MethodResolution` population that blocked
RUN 9 are **absent**. So the HIR-side commits in the 96-commit range
(`430d5ac431d`, `4217e91e327`, `0560611bd6b`, `4558514d53f`) did move the
chain: the blocker is now a different, later one.

## Crash attribution — CORROBORATED, NOT first-party

**No backtrace was obtained for this run**, and no claim is made that it is
byte-identical to the known signature. Two honest limits:

1. **No crash report was written.** The compiler runs inside
   `command-snapshot.shs`'s `env -i` sandbox; no `.ips` appeared in
   `~/Library/Logs/DiagnosticReports` after the 17:54 fault.
2. **An lldb replay of the same argv was NOT faithful and is discarded.**
   Re-running the exact `native-build` argv from
   `stage3-command.transcript` outside that sandbox (notably without
   `SIMPLE_BINARY` and with a different `HOME`/`TMPDIR`/`PATH`) **exited 1 on
   HIR lowering errors instead of crashing** — `unresolved name` in
   `types/_TypeLayout/arch_and_verify.spl` and `ambiguous explicit callable
   dependency` in `hir_lowering/expressions.spl`. The real run had **0** such
   errors, which proves the replay diverged before it could reach monomorphize.
   It is recorded here as a negative result, not as evidence about the crash.

What corroborates the attribution, clearly labelled as someone else's run: the
most recent `simple` crash report on this host, `2026-08-24 13:08`, from an
earlier lane, is

```
exception: EXC_BAD_ACCESS / SIGSEGV, KERN_INVALID_ADDRESS at 0xf198715900000000
  simple 0x1fb56c compiler__mono__monomorphize__type_subst__substitute_stmt + 1520
```

Same phase, same binary family, and `0xf19871590000_0000` is a 32-bit value
sitting in the HIGH half of a 64-bit slot — the mirror image of the Stage-2
`hc_enc_hir_module` truncation recorded in
`stage2_hir_codec_segv_is_i32_truncated_heap_ref_2026-08-24.md`, where a 64-bit
heap pointer loses its high half. Both are width defects on a tagged word. That
is a **hypothesis with a stated mechanism**, not a measurement of this run.

## Reproduction cost

Stage 2 from cold: ~27 min wall (seed ~4 min + `750 compiled, 0 cached`,
1035 s compile + 17 s link). Stage 3 to the fault: ~518 s. Both on a 10-core
M-series with `--jobs` defaulting to 5. `build/` in the worktree is 3.8 GB.

## Not verified

* Any Stage 4 / Stage 5 / MCP behaviour. No stage-3 artifact exists, so none of
  it was reachable and none of it was attempted.
* Whether fixing the Stage-2 `hc_enc_hir_module` truncation would clear this.
* The `--no-mcp` fallback was **never** used, because Stage 5 was never reached.

## RESOLVED 2026-08-24 — an Option HANDLE was stored in `HirStmtKind.Let.type_`

The crash attribution recorded above is now **first-party and proven**, and it
is **not** the i32-truncation family the previous section hypothesised.

### First-party backtrace

The `env -i` sandbox was reproduced faithfully (the transcript's five host-env
vars plus all 23 `explicit-env` records, notably `SIMPLE_BINARY`) and the
compiler was launched under `lldb --batch`. The replay tracked the real run —
0 `HIR lowering error` lines, same phase order — and faulted identically:

```
EXC_BAD_ACCESS (code=1, address=0xf198715900000000)
 #0 substitute_stmt + 1520          (ldr x9, [x8];  x25 = 0xf198715900000001)
 #1 substitute_block + 1416
 #2 canonicalize_template + 4796
 #3 MonomorphizationPass.collect_generics + 428
 #4 MonomorphizationPass.process_modules + 452
 #5 run_monomorphization_with_diagnostics + 32
 #6 CompilerDriver.monomorphize_impl + 1288
 #7 CompilerDriver.compile + 3216
 #8 run_native_build_bootstrap + 1324
```

### The faulting word, read out of the core

Walking the live objects in the saved core (`process save-core`):

```
x23 = 0xaccbc8041 -> HirStmtKind enum @0xaccbc8040
    word0 = 0x0000001800000007   kind = 0x07 = RT_VALUE_HEAP_ENUM
    word1 = 0x80f86b381ed418e2   enum_id 0x1ed418e2 (== the enum-id immediate
                                 materialised in substitute_stmt's disassembly)
    word2 = 0xaccbc8021 -> payload array (len 3 = Let(symbol, type_, init))
      elements = [0xacc72f171 sym, 0xaccbc3e41 ty, 0xaccdab261 init]

ty = 0xaccbc3e41 -> object @0xaccbc3e40
    word0 = 0x0000001800000007   kind = 0x07 = AN ENUM, not a HirType struct
    word1 = 0xf198715900000001   *** THE FAULTING WORD ***  enum_id = 1 = Option
    word2 = 0xacc72e6e1 -> the real HirType {kind: heap-ref, span: heap-ref}
```

`HirStmtKind.Let`'s second slot is declared `type_: HirType`
(`hir_definitions.spl:765`), **not** `HirType?`. It was holding a
`Some(HirType)` **Option handle**. `substitute_stmt`'s
`case HirStmtKind.Let(sym, ty, init)` CoW-clones `ty` as a 2-word
`HirType{kind, span}`: it takes the enum header's word0 as `kind` and word1 —
`enum_id | (variant << 32)`, i.e. `0xf1987159_00000001` — as `span`, then
deep-clones that as a 6-word `Span` (`rt_alloc #0x30`) behind nothing but the
`tag == HEAP && (v & ~7) != 0` shape test. `enum_id == 1` makes the word
HEAP-tagged and non-zero, so the guard passes and `0xf198715900000000` is
dereferenced.

### Why it is NOT the i32-truncation family

A census of the admitted Stage-2 binary (`objdump -d`, 64-bit register
operands) finds the wrong 32-bit flag-setting mask
`ands xN, xN, #0xfffffff8` at exactly **7** sites, **all** of them inside
`hc_enc_hir_module` — the defect recorded in
`stage2_hir_codec_segv_is_i32_truncated_heap_ref_2026-08-24.md`.
`substitute_stmt` uses the **correct** 64-bit mask
(`#0xfffffffffffffff8`). The mask is right here; the **value** is an Option
handle. The remaining 367 32-bit `and` sites are all in vendored LLVM/C++.

### Producer and fix

`src/compiler/20.hir/hir_lowering/statements.spl` built one local as an Option
and passed it to two consumers with different contracts:

```
val hir_type = if type_.?:
    Some(self.lower_type(...))
else:
    nil
val symbol = self.symbols.define(name, ..., hir_type, ...)   # wants HirType?  OK
HirStmtKind.Let(symbol, hir_type, hir_init)                  # wants HirType   BUG
```

`SymbolTable.define` (`hir_types.spl:316`) genuinely takes `HirType?`. Four
sites did this: `StmtKind.Val` and `StmtKind.Var` in the `match`, and their two
early-return twins (`v_hir_type`, `vr_hir_type`). The fix computes the bare
`HirType` once and wraps it for the symbol table only, so the HIR node stores
the bare value — matching every other `HirStmtKind.Let(...)` site in the tree,
which pass a bare value or literal `nil`.

### Minimal reproducer (seconds, not 9 minutes)

Against the *unfixed* Stage 2, this six-line file faults identically —
same symbol, same `+1520`, same `0xf198715900000000`:

```
fn id<T>(v: T) -> T:
    val x: T = v
    x

fn main():
    print(id(1))
```

Any generic template whose body contains a **type-annotated** `val`/`var` is
enough: `collect_generics` canonicalizes every template, and
`canonicalize_template` walks its body.

### Family

This is a fourth surfacing of "a wrong-shaped value sits in a slot and a shape
test lets it through", alongside `lower_hir_block` (`7c453e7b076`),
`hc_enc_hir_module`, and the `if val` binder (`9854efed570`). It shares the
`if val` case's *consequence* — an Option handle where the payload belongs, so
field reads land on the enum header — with a different producer: here the
`Some(...)` is explicit in the source, not a lost binder marker.

`rt_heap_ref_wellformed` cannot catch this class: it accepts any HEAP-tagged
word whose payload is `>= 4096`, and `0xf198715900000000` is. Rejecting
non-canonical addresses (`payload >= 1<<47`) would have caught it; that
hardening is deliberately NOT bundled into this producer fix.

### Verification (measured, this lane)

A cold Stage 2 was rebuilt from the fixed source (`--fresh-cache`,
`750 compiled, 0 cached, 0 failed`, 845 s compile), sha256 `e6761bfea2d9…` —
distinct from the crashing `3e535c58…`.

**Two earlier warm rebuilds produced a BYTE-IDENTICAL binary** (`cmp` rc=0,
`3 compiled, 747 cached`) even though a deliberate syntax-error probe proved
the build re-parses the edited file "during discovery". The Simple object cache
did not invalidate on the content change; only `--fresh-cache` picked the edit
up. Anyone validating a compiler-source fix on this lane must force a cold
cache or they will measure the OLD binary and conclude the fix does nothing.
That `Some(...)` really does emit code is independently confirmed: `lower_hir_stmt`
contains 44 `rt_enum_new` call sites.

On the fixed Stage 2 the reproducer now reports **`phase4:monomorphize:done`**
and proceeds to `phase5:mode_dispatch` / `aot:lower_to_mir`. The monomorphize
SIGSEGV is gone.

### Still open — the SAME family, one phase later

The reproducer now faults at the identical address `0xf198715900000000` in MIR
lowering, which was previously unreachable:

```
 #0 MirLowering.lower_type + 200        (ldr x10, [x9])
 #1 MirLowering.lower_call + 14968      (`ret_type = self.lower_type(callee.type_)`)
 #2 MirLowering.lower_expr + 1580
 #3 MirLowering.lower_bootstrap_print_call + 96
 ...
 #9 bootstrap_lower_flat_hir_module_to_mir + 2312
 #12 CompilerDriver.aot_compile + 568
```

`HirExpr` uses the same desugared shape as `HirBlock` (`has_type_: bool` +
`type_: HirType`), and `switch_operators_calls.spl:4781` guards correctly on
`callee.has_type_`. So an Option handle was **stored into** `type_` by some
producer; a grep for `type_: Some(` / `.type_ = Some(` finds nothing, so the
producer is an Option-typed *variable* flowing into the field rather than a
literal `Some(...)`. NOT yet located.

### Latent siblings of the same shape, NOT touched

Explicit `Some(...)` flowing into a non-Option HIR field elsewhere — each needs
its own evidence before being changed, and none is on the path fixed here:

* `_Expressions/expression_support.spl:635` — `HirBlock(..., value: Some(...), ...)`
  (`value: HirExpr` gated by `has: bool`)
* `statements.spl:132` — `lower_hir_assign_op_opt` into `Assign`'s `op: HirAssignOp`
* `statements.spl:622` — `val yield_value = Some(...)`
* `_Items/trait_impl_lowering.spl:352` — `Some(self.lower_type(at.default))`

The generated codec (`hir_codec.spl:4695`) writes
`var f_type_: HirType? = nil; ... HirStmtKind.Let(f_symbol, f_type_, f_init)`,
which LOOKS like the same bug but is not: assigning a bare value to an
optional-typed variable does not box (`hc_dec_hir_stmt_kind` contains exactly 5
`rt_enum_new`, one per HirStmtKind variant). Only an explicit `Some(v)` boxes.
Do not "fix" the generated codec on the strength of its spelling.

## VERIFIED on the real Stage 3 (2026-08-24, after `d4b1dee0d63`)

The fix above was verified on the **full sanctioned Stage-3 build**, not only on
the minimal reproducer. Stage 2 was rebuilt from a tree carrying the fix
(sha256 `7e45db55…`), re-admitted via `planner-admission-v2`, and Stage 3 was
resumed with `--resume-stage3-from-admitted`. Both cache-scope ownership gates
PASSed.

```
[BOOTSTRAP-PHASE] +898664ms phase4:monomorphize:start
[BOOTSTRAP-PHASE] +907601ms phase4:monomorphize:done     <-- CLEARED (8.9 s)
[BOOTSTRAP-PHASE] +907601ms phase5:mode_dispatch:start
[BOOTSTRAP-PHASE] +907601ms aot:lower_to_mir:start
command-snapshot.shs: line 182: 19229 Segmentation fault: 11
```

`HIR lowering error` count 0, `post_hir_validate 692/692`.
**`phase4:monomorphize` is cleared.** The blocker this record was opened for is
fixed and verified end to end.

**Still no Stage-3 artifact**: no `stage3/aarch64-apple-darwin/simple`, no
`provenance.env`, no `full/`. Stage 4, Stage 5 and deployment remain
unreachable, now for a different reason.

### New frontier: `aot:lower_to_mir`, same family again

The minimal reproducer (`fn id<T>(v: T) -> T: val x: T = v; x`) reaches the same
point and gives the frame the Stage-3 sandbox cannot:

```
EXC_BAD_ACCESS (code=1, address=0xf198715900000000)   <-- identical address
 #0 MirLowering.lower_type + 200            (ldr x10, [x9])
 #1 MirLowering.lower_call + 14968          (`ret_type = self.lower_type(callee.type_)`)
 #2 MirLowering.lower_expr + 1580
 #3 MirLowering.lower_bootstrap_print_call + 96
 #5 MirLowering.lower_stmt_impl + 2256
 #8 MirLowering.lower_function_with_gpu_metadata + 10952
 #9 bootstrap_lower_flat_hir_module_to_mir + 2312
 #12 CompilerDriver.aot_compile + 568
```

Same defect family, one phase later: an Option handle sitting in a non-Option
slot, dereferenced through the same `tag == HEAP && (v & ~7) != 0` shape test.
`switch_operators_calls.spl:4781` is *correct* — it guards on `callee.has_type_`
and `HirExpr` uses the desugared `has_type_: bool` + `type_: HirType` shape — so
the handle was **stored into** `type_` upstream. `type_: Some(` and
`.type_ = Some(` both find nothing, so the producer is an Option-typed
*variable* flowing into the field rather than a literal `Some(...)`.
**Producer NOT located** — that is the next piece of work, and it is plausibly
the same root as `9854efed570` (`if val` binds the Option handle), whose
lowering fix is still in flight in a sibling lane.
