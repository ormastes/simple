# Stage-3/stage2 self-hosted `native-build` SIGSEGV root cause: `call 0x0` baked into the binary (unpatched relocation)

- **Date:** 2026-08-11 (updated 2026-08-11: candidate emitting defect identified in `src/compiler/70.backend/backend/native/native_elf.spl`)
- **Status:** OPEN — emitting defect pattern identified at the source level; exact call-site symbol name (which .spl routine's *call* triggered it) still not proven, and no fix landed
- **Scope:** `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
  `bootstrap/stage2/simple` (and by the same mechanism, every self-hosted
  candidate `simple_compiler_select` currently rejects on the second probe
  rung). Relates to
  `doc/08_tracking/bug/simple_compiler_select_promotes_stage2_binary_without_run_subcommand_2026-08-06.md`,
  which documented the SIGSEGV's *existence* (rc=139 on `native-build`) but
  not its cause.

## Context

`simple_compiler_select`'s second probe rung
(`scripts/lib/simple-compiler-select.shs:189`) runs a real
`native-build --entry p.spl --source . -o probe_bin` against a trivial
one-line fixture (`fn main() -> i64:\n    0\n`). This is the "capability
probe" referenced by the task. On this host it SIGSEGVs (rc=139) on both
`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and
`bootstrap/stage2/simple`, which is why the selector rejects them and falls
through to weaker candidates. This blocks any lane that needs a genuine
self-hosted `native-build`, including the SimpleOS real-firmware harness.

## Reproduction

```sh
mkdir -p /tmp/probe && cd /tmp/probe
printf 'fn main() -> i64:\n    0\n' > p.spl
/home/ormastes/dev/pub/simple/bootstrap/stage3/x86_64-unknown-linux-gnu/simple \
    native-build --entry p.spl --source . -o probe_bin
# -> Segmentation fault (core dumped), exit 139
```

Confirmed on both `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and
`bootstrap/stage2/simple` (same binary size, 3,464,072 bytes, both dated Aug
10 12:09 — likely the same build artifact deployed to two paths).

No core file was written (host `core_pattern` pipes to `apport`, which does
not deposit a readable core here). Used `gdb --batch -ex run -ex bt -ex
"info registers"` instead — this is a LIVE run, not a stale-core artifact.

## Crash evidence

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000000000000 in ?? ()
#0  0x0000000000000000 in ?? ()
#1  0x000000000040465e in ?? ()
#2  0x00000000004025f5 in ?? ()
#3  0x00007ffff7c2a1ca in __libc_start_call_main (...)
#4  0x00007ffff7c2a28b in __libc_start_main_impl (...)
#5  0x00000000004024f5 in ?? ()

rip            0x0                 0x0
rax            0x13
```

`rip=0`, frame #1 return address `0x40465e`. Disassembling the call site
(`objdump -d --start-address=0x404600 --stop-address=0x404680`):

```
404650: mov    (%rsp),%r13
404654: mov    0x10(%rsp),%rdi
404659: call   0 <ftell@plt-0x402030>     ; e8 a2 b9 bf ff
40465e: mov    %rax,%r14                  ; <- return address on stack (frame #1)
```

## Root cause

This is **not** a runtime null-pointer dereference (no register holds 0
being called through indirectly — `rip` is 0 because the CPU already
executed a *direct* `call` whose encoded target IS address `0x0`). The
instruction bytes `e8 a2 b9 bf ff` are a relative `CALL rel32`; objdump
resolves the target purely arithmetically to `0x0` and mislabels it via the
nearest preceding symbol (`ftell@plt-0x402030`, a symbolization artifact —
this is not really a call to a `ftell` variant).

A direct `call` with a literal zero target address baked into the `.text`
section at build time means: **whatever code path emitted this call
instruction (during the self-hosted binary's own build/link) computed a
callee address of zero and encoded it into the relative-offset immediate
field, instead of the intended function's real address.** This is
characteristic of an unpatched/never-resolved relocation — a symbol whose
address the linker or the self-hosted native codegen's own relocation-fixup
pass failed to fill in, leaving the placeholder `call rel32` field at its
default (zero-relative, i.e. absolute `0x0`) value.

The call is unconditional and unguarded, so any code path through this
region of `main()` in the trivial fixture's compiled output hits it
deterministically — consistent with the 100%-reproducible SIGSEGV on every
`native-build` invocation the selector's probe rung has observed.

**What's NOT yet established** (would need matching this address back to a
known .spl source function, e.g. via a debug/symbol build of the same stage,
which wasn't available in the tree): which specific self-hosted routine
emits this call, and whether the unresolved symbol is a runtime helper
(`rt_*`), a libc function, or a self-referential linker/build-time construct.
The surrounding disassembly (repeated calls at `69cea0`/`69a380`/`69e94c`,
consistent stack layout) looks like inlined string/IO helper glue -- consistent
with `native-build`'s own file-output pipeline (writing `probe_bin`), which
would explain why `check p.spl` (no file output) is unaffected but
`native-build ... -o probe_bin` is not.

## Why no fix was attempted here

Root-causing the *exact* emitting call site requires a symbol-table-preserving
(unstripped, or matched to a `.map`/debug) build of the same commit that
produced these two binaries, which isn't available in this tree, plus
correlating against `src/compiler/70.backend` relocation/link-fixup code.
Per task scope, this is investigation-only: no rebuild/redeploy of
`bin/simple` or the staged binaries was performed, and no source-level fix
was identified with enough confidence to land safely without that
correlation step.

## Suggested next step

Rebuild stage2/stage3 with debug symbols retained (or add
`--emit-relocations`-style diagnostics to the self-hosted linker/backend) and
re-run this exact repro under gdb with symbols, to identify which relocation
record was never patched. Prime suspects: the self-hosted backend's own
symbol-resolution/link-fixup pass under `src/compiler/70.backend/`.

## Update 2026-08-11: candidate emitting-defect pattern found (source-level)

`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and `bootstrap/stage2/simple`
are both stripped (`nm` reports 1 symbol; `.symtab` absent), so the crash
address `0x404659` could not be matched back to a `.spl` source function by
symbol lookup — no debug/symbol-preserving build of the same commit was
available in this tree, so that specific correlation step (which exact
routine's `call` this is) is still **not** established. Static disassembly
context around the crash site (`objdump -d --start-address=0x4045c0
--stop-address=0x404700`, three sibling calls at `0x69cea0`, `0x69a380`,
`0x69e94c`, all taking `(rdi, rsi)`-shaped stack-loaded arguments, guarded by
an `rax == 0x13` (19) comparison) is consistent with inlined error/Result
formatting glue, but this is circumstantial, not proof.

Instead, the source-level *mechanism* by which a `call` can end up encoding a
literal `0x0` target was found directly in
`src/compiler/70.backend/backend/native/native_elf.spl`, and it matches the
observed byte pattern exactly:

- `src/compiler/70.backend/backend/native/encode_x86_64.spl:493-504`
  (`X86_OP_CALL` / `case Sym(name)`) emits `0xe8` (`CALL rel32`) followed by a
  **zero placeholder** (`emit_i32(code, 0)` at line 504) plus an `EncodedReloc`
  record carrying `symbol_name: name`. This placeholder-then-patch design is
  correct in principle — the 0 is meant to be overwritten once the target
  address is known.
- The patch step lives in `native_elf.spl`, duplicated once per target arch
  (x86_64 at lines 118-128, AArch64 at lines 268-283, and a third RISC-V copy
  around lines 420-430 — same shape all three times):

  ```
  var sym_idx = 0
  if sym_name_to_idx.contains(reloc.symbol_name):
      sym_idx = sym_name_to_idx[reloc.symbol_name]
  val elf_reloc = ElfReloc(
      offset: code_start + reloc.offset,
      reloc_type: reloc_type,
      symbol_index: sym_base + sym_idx,
      addend: reloc.addend
  )
  ```

  When `reloc.symbol_name` is **not** found in `sym_name_to_idx`, `sym_idx`
  silently defaults to `0` instead of raising an error or panicking the
  build. The `ElfReloc` is still emitted and still pushed into `all_relocs` —
  it just now points at symbol-table index `sym_base + 0`, i.e. effectively
  the null/first symbol, rather than failing loudly. This is exactly the
  "unresolved symbol falls back to 0 instead of erroring" pattern already
  seen elsewhere in this codebase (missing-registration class of bug), and it
  is structurally sufficient to explain a `call rel32` whose relocation never
  gets a real target and ends up encoding `0x0` in the final linked `.text`.

**Still open / not proven:**
1. Which specific `.spl` function name failed the `sym_name_to_idx.contains`
   check for this particular crash (i.e., what got compiled that produced a
   `Sym(name)` call operand whose `name` was never registered into
   `sym_names`/`sym_name_to_idx` — a missing function, a renamed/mangled
   symbol mismatch, or a lowering bug that emits a call to a name that was
   never added as a function/extern symbol in the first place).
2. Whether `write_elf64`/the final native-build link path treats
   `symbol_index: sym_base + 0` as "leave the placeholder untouched" (which
   would explain the literal `0x0` bytes surviving straight through to the
   final executable) or performs some other silent no-op — this requires
   tracing `elf_writer.spl`'s relocation-application code, which was not done
   in this pass due to time budget.
3. No fix was landed: the silent-fallback-to-0 pattern is a strong, precise
   root-cause **candidate** appearing identically in all three
   (x86_64/AArch64/RISC-V) emitters in `native_elf.spl`, but turning the
   fallback into a hard error (so a missing symbol registration fails the
   build immediately instead of producing a `call 0x0` time bomb) is a
   backend/codegen-correctness change and was intentionally not attempted
   without first identifying which upstream pass fails to register the
   symbol — fixing only the symptom (erroring instead of defaulting to 0)
   would turn today's SIGSEGV into a clean compile-time error, which is
   itself a reasonable minimal fix, but doesn't address why the symbol
   registration was missing in the first place.

**Suggested follow-up:** add a hard error/panic at the `sym_idx = 0` fallback
in all three `native_elf.spl` sites (fail the build with the missing symbol
name) so this defect class becomes a loud compile-time diagnostic instead of
a silent `call 0x0` SIGSEGV, then use that diagnostic's error message on the
real `native-build --entry p.spl` repro to name the exact missing symbol.
