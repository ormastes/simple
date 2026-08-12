# Stage-3/stage2 self-hosted `native-build` SIGSEGV root cause: `call 0x0` baked into the binary (unpatched relocation)

- **Date:** 2026-08-11
- **Status:** OPEN — root cause diagnosed, no fix landed
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
