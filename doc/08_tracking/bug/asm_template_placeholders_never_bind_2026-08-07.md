# `asm """..."""` template placeholders never bind — and `@cfg("target_arch", ...)` is inert

- **Date:** 2026-08-07
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** blocker (Stage-3 self-host blocker #10)

## Symptom

Stage-3 native-build reached LLVM codegen and died with an assembler error that
names no Simple source file, three phases after the real fault:

```
error: <inline asm>:2:25: unexpected token in argument list
        movzx eax, byte ptr [{addr}]
                        ^
```

Evidence: `/home/ormastes/dev/simple-s3red/build/red/stage3.log` (rc=1) and
`/home/ormastes/dev/simple-s3family/build/green/stage3.log` (rc=1, identical).

## Root cause A — placeholders without an operand list

The language DOES implement inline-asm operand binding. The supported spelling is
documented at `src/compiler/10.frontend/parser_types_expr.spl:689`:

```
asm volatile("mov r0, {op}", op = in(reg) value, clobber_abi("C"))
```

The binding lives in the operand list, not the template. `HirAsm` /
`MirInstKind.InlineAsm` carry `inputs` / `outputs` populated from
`AsmConstraint` (`In` / `Out` / `LateOut` / `InOut`) — see
`src/compiler/20.hir/hir_lowering/expressions.spl` `lower_asm`, and
`src/compiler/50.mir/_MirLowering/function_lowering.spl:900-925`.

The **bare** `asm """..."""` form carries no operand list at all. A `{name}` in a
bare template is therefore not a placeholder — it is literal text, emitted
verbatim into LLVM inline asm, where the integrated assembler chokes on `{`.

Five files were written against an imagined Rust-`asm!`-style syntax that this
language never had, using the template half without the operand half.

## Root cause C — `out(reg)` bindings compile and are then SILENTLY DROPPED

**Do not "fix" the remaining files by rewriting them to the bound form.** The
bound form parses, compiles, links, and runs — and never writes its outputs back.

Initially the bound form looked correct because it built at rc=0. That test was
vacuous: it checked compilation, not binding. Checking the *value* shows the
output operand is discarded:

```
fn asm_copy(src: i64) -> i64:
    var dst: i64 = 0
    asm volatile("movq $1, $0", dst = out(reg) dst, src = in(reg) src)
    dst                          # returns 0, expected 7

fn asm_const() -> i64:
    var dst: i64 = 0
    asm volatile("movq $$42, $0", dst = out(reg) dst)
    dst                          # returns 0, expected 42
```

Both build at rc=0 and both return `0`. A constant load that cannot fail still
returns zero, so this is the output path, not operand numbering or syntax.

Consequence: **inline assembly is currently non-functional for any
value-producing use, and it fails silently.** Nothing diagnoses it — no warning,
no error, just zeros. A `rdtsc` rewritten to the bound form compiles cleanly and
reports a timestamp of 0 forever.

This was caught while evaluating whether to rewrite `timer.spl` /
`topology.spl`. Verified there too: `read_tsc()` returned `tsc1=0 tsc2=0`
(non-increasing) and `cpuid_leaf(0,0)` returned max-leaf `0`. Landing that
rewrite would have put silently-zero TSC and CPUID into the kernel while looking
green. Those two files are therefore left with their (loud, obvious) placeholder
breakage rather than converted to quiet, plausible wrongness.

Explicit register constraints, which `rdtsc` / `cpuid` actually need, are not
supported either — `out("eax")` fails to parse:

```
parse: Unexpected token: expected identifier, found FString([Literal("eax")])
```

## Root cause B — `@cfg("target_arch", ...)` parses but gates nothing

All five files carry per-architecture asm blocks annotated
`# @cfg("target_arch", "riscv64")` etc. Those are **comments**, so every arch
variant was emitted unconditionally. Worse, writing the attribute for real does
not help: `@cfg("target_arch", "arm")` was tested both as a statement-level
attribute and as a function-level attribute, and in **both** cases the arm asm
was still emitted into an x86_64 build:

```
error: <inline asm>:2:9: unknown use of instruction mnemonic without a size suffix
        mov r0, r1
```

The attribute is accepted by the parser and silently ignored by codegen. This is
a separate, independently serious defect: it fails open.

`asm match:` (`case [x86_64]: ...`), which exists in `HirExprKind.InlineAsmMatch`
and is spec'd in `test/01_unit/compiler/native/asm_match_spec.spl`, is NOT
available in the stage2 compiler — it fails to parse:

```
parse: Unexpected token: expected expression, found Case
```

So there is currently **no working arch-gating mechanism** for inline assembly.

Consequence: `semi_host_call` emitted thumbv7m `bkpt`, arm `svc`, and two riscv
`ebreak` sequences back to back. That is invalid on *every* target — an arm
build chokes on the riscv blocks exactly as x86_64 chokes on all of them. These
functions never worked anywhere; nothing was regressed by replacing them.

## Family — 44 placeholder asm lines across 5 files

| file | lines | on Stage-3 path | disposition |
|---|---|---|---|
| `src/compiler/35.semantics/volatile.spl` | 12 | yes | **deleted** (dead duplicate) |
| `src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl` | 18 | yes | **fixed** (12 rerouted to SFFI, 6 in `semi_host_call` withdrawn) |
| `src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl` | 6 | yes | **fixed** (`semi_host_call` withdrawn) |
| `src/os/kernel/arch/x86_64/timer.spl` | 2 | no (`src/os` is not a `--source` root) | **open** |
| `src/os/kernel/arch/x86_64/topology.spl` | 6 | no | **open** |

`src/lib/nogc_async_mut_noalloc/baremetal/x86/serial_test_kernel.spl:14` also has
an `asm """..."""` block but it is `cli` / `hlt` with no placeholders — correct,
not part of this family.

The two remaining files are x86_64-only (`rdtsc` → `{lo}`/`{hi}`, `cpuid` →
`{leaf}`/`{subleaf}`/`{eax}`). They need no arch gating, only the bound form, so
they can be closed with a mechanical rewrite to
`asm volatile("rdtsc", lo = out(reg) lo, hi = out(reg) hi)`.

## Why the compile set includes files nothing imports

The Stage-3 harness passes `--source src/compiler --source src/lib --source
src/app`. Every `.spl` under a source root is compiled, **whether or not it is
reachable from `--entry`**. Verified with a minimal repro: a `src/lib/dead_asm.spl`
that nothing imports still reached LLVM and still produced the error. This is why
a proven-dead function in `volatile.spl` could block the whole build, and why
fixing one file only moved the error to the next.

## Fixes applied

1. **`src/compiler/35.semantics/volatile.spl`** — deleted `volatile_read_u8/16/32/64`,
   `volatile_write_u8/16/32/64`, `memory_barrier`, `load_barrier`, `store_barrier`,
   `compiler_barrier`. Dead-code proof:
   - not in the re-export list at `src/compiler/35.semantics/__init__.spl:125-129`
     (which exports only `VolatileAccess`, `VolatileContext`, `VolatileKind`,
     `is_volatile_access`, `mark_volatile`, `generate_volatile_read`,
     `generate_volatile_write`, `volatile_for_naked_context`);
   - zero references across all nine numbered compiler layers and `common/`;
   - the canonical implementations are the SFFI wrappers in
     `src/lib/nogc_sync_mut/io/volatile_ops.spl`, binding `rt_volatile_*` /
     `rt_memory_barrier` from `src/runtime/runtime.h:222-226`.

   `generate_volatile_read` / `generate_volatile_write` in the same file return
   assembly as **text** and are live and exported — untouched.

2. **`semihost_transport.spl`** — `semihost_uart_write_reg`,
   `semihost_uart_read_reg` and `uart_probe_lsr` were single MMIO byte
   load/stores. Rerouted to `rt_volatile_write_u8` / `rt_volatile_read_u8`:
   architecture-neutral, correct on every target, and the same primitive the rest
   of the tree already uses.

3. **`semi_host_call`** (duplicated in both baremetal files) — the semihosting
   debugger trap has no architecture-neutral spelling and no working gate. It now
   returns `-1` (unavailable) with a `TODO` pointing here, rather than emitting
   wrong-architecture instructions. This is an explicit failure, not a fake
   success: the previous code returned an uninitialised `result` when it
   assembled at all, which it never did.

## Open work

- **`@cfg("target_arch", ...)` is parsed and ignored.** Fail-open attribute.
  Fixing this is the prerequisite for restoring the real semihosting traps.
- **`asm match:` does not parse in stage2** despite being spec'd and having HIR /
  MIR representations.
- **`out(reg)` write-back is silently dropped** (root cause C). This is the most
  serious of the three: inline asm is non-functional for any value-producing use
  and reports nothing. It must be fixed BEFORE any file is converted to the bound
  form, otherwise the conversion trades a loud assembler error for a silent zero.
- **`timer.spl` / `topology.spl`** — 8 placeholder lines. Blocked on root cause C;
  they also need explicit register constraints (`rdtsc` writes EDX:EAX, `cpuid`
  clobbers RBX), which do not parse today. Left loudly broken on purpose.
- **Diagnostic gap.** The compiler silently accepts an `asm` template containing
  `{ident}` with an empty constraint list and lets LLVM report it three phases
  later, against `<inline asm>` with no Simple file or line. It should error at
  the asm site. Deliberately NOT landed in this change: the check would also fire
  on `timer.spl` / `topology.spl` and turn them into hard failures for any build
  including `src/os`. Land it after those two are fixed.

## Reproduction

Fast oracle (seconds, not the ~1h full Stage-3 run) — a two-file tree through the
prebuilt stage2:

```sh
RT=/home/ormastes/dev/simple-t3-final-20260806/build/bootstrap-t3-final-20260806/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority
SIMPLE_RUNTIME_PATH="$RT" SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  /home/ormastes/dev/simple-s3clean/build/clean/stage2-simple native-build \
    --runtime-path "$RT" --source src/lib --source src/app \
    --entry src/app/cli/probe_main.spl -o probe
```

with `src/lib/m.spl` containing any bare `asm """..."""` block that mentions
`{name}`.

Full run: `/home/ormastes/dev/simple-s3red/run_stage3.shs <worktree> <tag>`.
