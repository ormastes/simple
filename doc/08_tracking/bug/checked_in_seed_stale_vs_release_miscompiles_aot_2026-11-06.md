# Checked-in bootstrap seed is stale vs release/1.0.0 and silently miscompiles

- **Status:** OPEN
- **Filed:** 2026-11-06
- **Severity:** high — every AOT emission produced by the checked-in seed is
  suspect; several days of lane evidence needed re-derivation after discovery.

## Evidence (2026-11-06, lane `work/riscv-struct-init-codegen-20261105`, PR #7020)

The checked-in seed at `src/compiler_rust/target/bootstrap/simple` was built
from a diverged main tree, not from release/1.0.0. Measured symptom: AOT
cranelift emission of a four-field struct literal (four `[i64]` fields) is
correct through MIR and CLIF, but the emitted object miscompiles — in-guest
the literal's fields receive allocation-header garbage. The identical program:

- passes under host JIT (`LocalExecutionManager::cranelift()`),
- emits exactly-right CLIF (`SIMPLE_DUMP_CLIF=probe`: four independent
  box/new/push chains, stores paired with offsets 0/8/16/24),
- and **boots `PROBE OK four-field struct literal` in-guest when the seed is
  built from the current release commit** — no seed source change required.

release/1.0.0 already contained the fix; the checked-in binary predates it.

## Operational rule (load-bearing, effective immediately)

Any AOT-emission evidence (in-guest kernel builds, native objects, cranelift
AOT output) must be produced with a seed built from the SAME release commit
being tested. `SIMPLE_BIN` must point at that freshly built seed. The checked-in
bootstrap binary may only be used for interpreter-mode and parse-level checks
that do not exercise the defective emission path — and even there, divergence
is possible.

## Required resolution

1. Rebuild the checked-in seed from release/1.0.0 and redeploy it through the
   normal bootstrap qualification path (see `.agents/skills/bootstrap`), OR
2. Gate every AOT-producing gate script on a seed-freshness check (seed build
   commit == HEAD), failing closed when stale.

Either way, the kernel build script's existing "freshly built seed" warning
should cite this record: the miscompile is demonstrated, not hypothetical.
