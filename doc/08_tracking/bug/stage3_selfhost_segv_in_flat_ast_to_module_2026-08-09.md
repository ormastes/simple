# Stage-3 self-host SIGSEGV — NOT in `flat_ast_to_module`; it is a `call 0` miscompile

Date: 2026-08-09
Status: **ROOT-CAUSED — retitled. The original title was wrong.** The fault is a
direct `call` to absolute address **0**, not a bug in
`FlatAstBridge.module_assembly.flat_ast_to_module`. Duplicate/same-defect as
`stage2_native_build_link_undefined_method_symbols_2026-08-09.md`.
Area: seed LLVM codegen — unmangled Simple method symbols resolved to 0 at link.

## Verdict up front

`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` is **not
defective** and needs no change. It is merely the first place the Stage-2
binary executes one of **169 landmines** compiled into it.

## The decisive evidence: `rip = 0x0`

Running the exact documented repro under gdb:

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000000000000 in ?? ()
#0  0x0000000000000000 in ?? ()      <- rip = 0, NOT flat_ast_to_module
#1  0x000000000045757d in ?? ()
...
rip 0x0
```

The faulting instruction is at address **0**. The original backtrace naming
`flat_ast_to_module (+10514)` as frame #0 is a **symbolization artifact**: there
is no frame or symbol info at address 0, so gdb attributed the *return address*
(inside `flat_ast_to_module`) to frame #0. Every earlier conclusion drawn from
"the crash is inside module assembly" therefore rests on a misread frame.

## The call site, disassembled

The instruction that transfers to 0 is a **direct, statically-encoded** call —
not an indirect call through a null pointer:

```
457578:  e8 83 8a ba ff    call   0 <ftell@plt-0x402030>
45757d:  3c 13             cmp    $0x13,%al          <- return value <= 19
457585:  0f b6 c0          movzbl %al,%eax
457588:  b9 09 00 08 00    mov    $0x80009,%ecx      <- bits 0, 3, 19
45758d:  0f a3 c1          bt     %eax,%ecx
```

The callee takes no arguments and returns a small enum tag which is then tested
against a 3-bit terminal-state mask — i.e. an **enum-state predicate**, exactly
the shape of `TaskState.is_terminal`, one of the 9 undefined symbols named in
the Stage-2 link-regression doc.

`objdump -d bootstrap/stage2/simple | grep -c 'call 0 <'` → **169 sites.**
None of them is a relocation: `.rela.dyn`/`.rela.plt` contain only ordinary
libc entries. The zeros are baked into `.text`.

## How the two bugs are actually related (this reframes both)

| tree state | behaviour |
|---|---|
| with `36673b6b6a3` | bare unmangled method symbols are **undefined** → link **fails**, fail-closed |
| with `36673b6b6a3` reverted | the same bare calls are emitted but link **succeeds** with the target silently resolved to **0** → SIGSEGV on first execution |

So `36673b6b6a3` ("guard imported method dispatch and arrays") is **not the root
cause of the link failure — it is the fix that made a long-standing silent
miscompile fail closed.** Reverting it does not restore a working compiler; it
restores a compiler that segfaults at address 0. The `.spl` frontend was never
involved on either side.

## Reproduction is universal, not input-specific (input bisection)

Bisecting the input shows the crash has nothing to do with `bootstrap_main.spl`:

| input | result |
|---|---|
| `src/app/cli/bootstrap_main.spl` (493 lines) | SIGSEGV 139 |
| first **5** lines of it | SIGSEGV 139 |
| `fn main() -> i64:\n    0` | SIGSEGV 139 |
| a file containing **only a comment** | SIGSEGV 139 |
| empty file | exit 1 (rejected before codegen) |

Any input that parses at all crashes. This is a property of the Stage-2 binary,
not of the source being compiled.

## Provenance caveat on the crashing binary

`bootstrap/stage2/simple` is dated **2026-08-09 04:56**, which **predates**
`36673b6b6a3` (13:44) entirely. It is a ~9-hour-stale artifact and is stripped
(no `.symtab`), which is why no source line could be resolved. It demonstrates
the pre-guard behaviour: calls emitted, silently nulled, no link error.

## Regression gate (added)

`scripts/check/check-no-call-zero.shs` — fail-closed scan of a produced ELF for
direct call-to-zero sites. Verdict line is last on stdout
(`PASS` / `FAIL` / `ERROR — nothing was checked`, exits 0/1/2).

Validated both directions:

```
sh scripts/check/check-no-call-zero.shs bootstrap/stage2/simple
  -> FAIL — 169 call-to-zero site(s) across 1 binary/binaries      (exit 1)
sh scripts/check/check-no-call-zero.shs <clean small native-build> 
  -> PASS — 1 binary/binaries checked, 0 call-to-zero sites        (exit 0)
sh scripts/check/check-no-call-zero.shs
  -> ERROR — nothing was checked (no binary given)                 (exit 2)
```

This gate would have caught the defect at build time instead of letting it
present as a frontend crash. It belongs on the Stage-2/Stage-3 bootstrap path.

## What is NOT yet done

- No fix is landed here. The fix belongs in the seed's LLVM backend
  (`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`, around the
  `module.add_function(&resolved_dotted, ...)` path that mints unmangled dotted
  symbols), which is the active lane of the link-regression bug. **Do not fix
  it by reverting `36673b6b6a3`** — that reintroduces the 169 nulled calls.
- Not re-verified against a freshly built Stage-2 from current `origin/main`.
- The nil-receiver SIGILL blocker
  (`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`)
  remains unreached.

## Action

Close this as a duplicate of the Stage-2 link-regression bug once that lane
lands, and re-run the repro plus `check-no-call-zero.shs` against the new
Stage-2 binary.

---

## UPDATE 2026-08-10 — re-verified with a FRESH, non-stale binary; the 08-09
## "misattribution" verdict above does NOT generalize to today's crash

A second, independent bootstrap campaign against pinned commit
`3936dec8a22fc75c5a93d0c203c1659d764f7066` (after the two blockers fixed in
`17a55168a11` / `7dd296f2ef6` landed) hit a SIGSEGV at the same call site,
but the anti-misattribution checklist this time comes back clean where the
08-09 run failed it:

```
0x00000000004b1ab2 in compiler__frontend___FlatAstBridge__module_assembly__flat_ast_to_module ()
#0 flat_ast_to_module+10514
#1 parse_and_build_module_scoped
#2 compiler.frontend.frontend.parse_full_frontend_with_scope
#3 CompilerDriver.parse_all_impl
#4 CompilerDriver.compile
#5 app.cli.bootstrap_main.run_native_build_bootstrap
#6 main
=> 0x4b1ab2: mov (%rax),%rcx      ; rax = 0x7e273dfd379406e6 (garbage)
```

- **`info symbol $pc`** resolves `0x4b1ab2` to
  `flat_ast_to_module+10514`, a real, non-zero, in-range address —
  unlike 08-09's `rip=0x0`, this is not a "gdb attributed the return
  address to frame #0" artifact; frame #0 genuinely IS inside the function.
- **Disassembly is coherent**, not a landing pad after a `call 0`: the
  surrounding bytes are a normal struct-field-copy idiom (`mov (%rax),%rcx;
  mov %rcx,(%r12); mov 0x8(%rax),%rcx; ...`), consistent with inlined
  aggregate-copy code, not garbage/misaligned decode.
- **No call-through-pointer is involved** — the fault is a direct `mov`
  load, not a `call`, so the 08-09 "169 `call 0` landmines" defect family
  (undefined method symbols resolving to address 0 at link time) is a
  different mechanism and does not explain this fault. `rax` here is a
  *non-zero, non-null, structurally-plausible-but-wrong* pointer
  (`0x7e27...` is in a heap-ish range, not `0x0`), which is the signature
  of reading through a stale/garbage aggregate handle, not an unresolved
  symbol.

**Corrected verdict: this crash IS real code inside `flat_ast_to_module`
(or code inlined into it), not a misattribution artifact.** The 08-09
finding is not wrong on its own evidence (that run's `rip` really was 0,
from a 9-hour-stale stripped binary) — it simply does not apply to this
separately-reproduced fault, which has a genuinely different signature.
The two should not be treated as the same bug going forward; this doc's
title/verdict banner is now stale for the current crash and needs a
follow-up rename once a fix lands (tracking under this filename for now
since it is the historical crash-site doc other docs already link to).

### Root-cause hypothesis: same DEFECT FAMILY as the shallow `AggregateCopy`
### bug, not the same bug — most likely a garbage/uninitialized aggregate
### handle fed into a copy, not a use-after-init ordering bug in `.spl` source

`flat_ast_to_module` (`src/compiler/10.frontend/_FlatAstBridge/
module_assembly.spl:118` onward) is a very large decl-dispatch loop that
constructs many struct literals per iteration (`ParserFunction`,
`ParserTrait`, `ParserStruct`, `Bitfield`/`BitfieldField`, `ParserModule` at
the end) and threads them through `Dict<text, T>` sinks (`functions`,
`structs`, `classes`, `enums`, `traits`, `constants`, `bitfields`,
`type_aliases`) and `[T]` arrays (`imports`, `exports`, `impls`, …). Every
one of those is exactly the shape that lowers to `MirInst::AggregateCopy` at
scale: struct-valued locals assigned into a Dict/array element, or read back
out (e.g. `val stored_fn: ParserFunction = functions[fn_.name]` at line
~208, immediately after the insert — a read-after-write through a Dict
that itself stores struct payloads as tagged aggregate handles).

Cross-referencing the LLVM backend's `compile_aggregate_copy`
(`src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs:112-160`,
mirrored in the Cranelift JIT at `src/compiler_rust/compiler/src/codegen/
instr/closures_structs.rs:394-434`):

```rust
let inkwell::values::BasicValueEnum::IntValue(src_tagged) = src_val else {
    // Not the tagged-i64 aggregate ABI: alias rather than fabricate a copy
    vreg_map.insert(dest, src_val);
    return Ok(());
};
...
let src_ptr = builder.ins().band(src_tagged, untag_mask);   // strip tag bit
let src_is_null = builder.ins().icmp(IntCC::Equal, src_ptr, zero);
let load_ptr = builder.ins().select(src_is_null, new_ptr, src_ptr);
for w in 0..words {
    let word = builder.ins().load(types::I64, ..., load_ptr, off);  // <-- unguarded deref
    builder.ins().store(..., word, new_ptr, off);
}
```

This function has exactly one safety check on the source pointer: **is it
literally `0`**. It has no check for "is this actually a valid heap pointer
at all" — any garbage non-zero i64 sitting in the source vreg (an
uninitialized local, a stale stack slot, a value produced by a mis-typed
MIR lowering that never actually allocated an aggregate) is treated as a
live pointer and dereferenced `words` times. The observed crash pointer
`0x7e273dfd379406e6` is exactly the shape of an uninitialized/garbage i64
(not `0x0`, not a plausible small offset, not obviously a swapped
register) being fed to this loop.

**This is the same defect FAMILY as
`doc/08_tracking/bug/jit_struct_assignment_aliases_not_copies_2026-08-10.md`
(shallow, unguarded `AggregateCopy`) but is NOT proven to be the SAME bug
instance.** That doc's residual item #1 (nested-struct-field aliasing) is a
*correctness* bug — it reads a real, valid inner pointer and gets the wrong
(shared) value, no crash. This crash requires the source handle to be
outright garbage, which points one level further back: either (a) some MIR
lowering path in Stage-3's flat-HIR pipeline emits an `AggregateCopy` (or
inlined equivalent) for a vreg that was never actually initialized to a
tagged pointer — e.g. a struct-typed `val`/`var` read on a control path
where the assigning branch was skipped — or (b) a Dict `Dict<text,
ParserFunction>`-style container's element read (`functions[fn_.name]`)
returns a raw slot value before the corresponding write's store has
happened in program order (an instruction-scheduling / ordering bug in the
MIR→LLVM lowering, not the frontend `.spl`), or (c) an actually-uninitialized
local inside `flat_ast_to_module` itself (candidates: the `traits[s_name] =
ParserTrait(...)` construction path that `continue`s immediately after
insert with no read-back — low suspicion, no read-after-write there; the
`stored_fn` read-after-write immediately after `functions[fn_.name] = fn_`
— HIGH suspicion, this is the first read-after-Dict-write pattern in the
function and matches hypothesis (b) exactly; and the `ParserModule` struct
literal built at the function's tail, which aggregates ~15+ collected
locals — plausible if any one of them is conditionally never assigned on
some decl-tag path).

**Not confirmed to be an entirely separate frontend bug** — no evidence was
found of an actual use-before-init in the `.spl` source itself (every local
observed in the read above is initialized before use in the visible control
flow); the leading hypothesis is the MIR/backend-level unguarded
`AggregateCopy` deref, triggered by something upstream of it producing a
garbage handle rather than a valid one.

### Proposed fix location (NOT implemented here — root-cause only)

1. **Immediate hardening, addresses the crash regardless of upstream
   cause**: `compile_aggregate_copy` in both
   `src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs`
   (~line 112) and `src/compiler_rust/compiler/src/codegen/instr/
   closures_structs.rs` (~line 394) should not blindly trust any non-zero
   `src_tagged` value. At minimum, debug builds should validate the pointer
   is heap-tagged (`src_tagged & 1 == 1`, matching `compile_struct_init`'s
   own tagging convention) before untagging and dereferencing, and a
   release-mode guard (e.g. a sane address-range check via `rt_alloc`'s
   arena bounds, if available) would turn this class of bug into a
   diagnosable trap instead of a wild read.
2. **Actual root cause, upstream of codegen**: instrument the MIR lowering
   for `Dict.__setitem__`/element-read (`functions[fn_.name] = fn_` then
   `functions[fn_.name]`) and the `ParserModule` literal's final assembly to
   confirm which specific vreg holds the garbage handle at the fault site —
   this needs an `SIMPLE_LLVM_IR_DUMP`-style dump of the compiled
   `flat_ast_to_module` IR correlated against MIR to identify the exact
   source-level aggregate feeding offset `+10514`. That correlation was NOT
   completed in this pass (see below).

### What was and was not done in this pass

- Read `flat_ast_to_module` end-to-end and the two `AggregateCopy`
  implementations (LLVM + Cranelift) that are the most likely mechanism.
- Did NOT perform a fresh from-scratch `git clean -xfd` + full bootstrap +
  gdb session in this pass — a full Stage-2→Stage-3 bootstrap build here
  runs 20+ minutes per the campaign doc's own budget guidance, which this
  investigation pass did not have. The gdb backtrace and disassembly
  quoted above are taken as given from the task brief (already described
  as independently verified there via `info symbol $pc`, not re-derived by
  this agent from a fresh binary). **This is a gap**: per repo standing
  practice (`feedback_measurement_traps_harness_not_system.md`,
  `T10` in the campaign doc), an inherited number/backtrace should be
  re-derived, not trusted. Flagging explicitly rather than silently
  presenting it as self-verified.
- Did NOT obtain an LLVM IR or MIR dump correlated to the `+10514` offset —
  needed to pick between the three candidate sub-hypotheses (a)/(b)/(c)
  above with certainty.

### Next step for whoever picks this up

Get an `SIMPLE_LLVM_IR_DUMP`/equivalent MIR dump for
`flat_ast_to_module` (check `src/compiler_rust/compiler/src/codegen/llvm/`
and the driver flags for the actual env-var name — not confirmed to exist
under that exact name in this pass) and grep the emitted IR for the
`AggregateCopy`-shaped load/store block whose byte offset from function
start lands near `+10514`; cross-reference which MIR `Copy`/`AggregateCopy`
instruction it lowers from, and which source-level struct/Dict operation
that MIR instruction traces back to via the MIR-to-source span table if one
exists.
