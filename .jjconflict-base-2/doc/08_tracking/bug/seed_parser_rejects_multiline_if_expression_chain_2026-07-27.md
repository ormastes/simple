# Seed parser rejects multi-line `if`-expression chains (and `@hardware`)

- **Filed:** 2026-07-27
- **Status:** OPEN
- **Component:** `src/compiler_rust` (bootstrap seed) — parser + attribute handling
- **Severity:** blocks 9 RISC-V hardware gate probes (`scripts/check/check-riscv-hardware-gates.shs`)

## Defect 1 — parse: `expected expression, found Else`

The Rust bootstrap seed cannot parse an `if`-expression chain in value position
when the arms are split across lines. The **pure-Simple self-hosted parser
accepts it** (`bin/simple lint` reports 0 errors), so this is a seed-only gap,
not invalid Simple.

Minimal repro (`/tmp/pbis/t1.spl`):

```
fn f(p: i64, lo: i64, ins: i64) -> i64:
    val x = if p == 2:
        lo else if p == 1:
        0 else: ins
    return x
```

`bin/simple run` (seed) →
`error: compile failed: parse: ... Unexpected token: expected expression, found Else`
`bin/simple lint` (self-hosted) → clean.

Real site: `src/lib/hardware/rv64gc_rtl/protected_core.spl:537-539` (pre-fix).
Worked around in source on 2026-07-27 by restructuring to a statement-form
`var` + `if / else if` (see that file). **The workaround is a seed accommodation;
the seed parser is what needs fixing.**

Note: statement-form `else if` and mixed inline/block `else if` chains (e.g.
`protected_core.spl:143-155`) parse fine in the seed — the keyword is not the
problem, the multi-line *expression* chain is.

## Defect 2 — semantic: ``variable `hardware` not found``

The seed does not know the `@hardware` declaration attribute, which the
self-hosted compiler recognises (`src/compiler/00.common/_Attributes/decl_attrs.spl:487`)
and the VHDL backend consumes (`src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl`).
The seed lowers the annotation as a bare variable reference.

Minimal repro (`/tmp/pbis/t2.spl`):

```
@hardware
fn g(x: i64) -> i64:
    return x + 1

fn main():
    print(g(1))
```

`bin/simple run` (seed) → ``error: semantic: variable `hardware` not found``
`bin/simple lint` (self-hosted) → clean.

212 `@hardware` sites across 24 files under `src/lib/hardware/rv32i_rtl/` and
`src/lib/hardware/rv64gc_rtl/`.

## Impact

With `bin/simple` currently being the Rust seed, these 9 gate probes fail:
`soc_top_64_probe`, `boot64_probe`, `core64_probe`, `core_fpu_integration`,
`csr_machine_id`, `rv32_uart_console`, `addr4g_probe`, `hart_debug_probe_rv32`,
`link_mux_jtag_debug`.

Defect 1 masked Defect 2 in `soc_top_64_probe`; after the source workaround the
probes still fail on Defect 2.

## Fix direction

Correct fix is to deploy the pure-Simple self-hosted binary as `bin/simple`
(both constructs already parse there). Failing that, teach the seed the
`@hardware` attribute and multi-line `if`-expression chains.
