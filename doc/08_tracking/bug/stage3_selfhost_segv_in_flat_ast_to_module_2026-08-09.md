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
