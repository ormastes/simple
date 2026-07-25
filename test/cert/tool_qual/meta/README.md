# `meta/` — DO-330 tool-PROPERTY corpus (beyond I/O correctness)

`positive/` + `negative/` qualify the compiler's **input→output** behaviour against
independent goldens. This `meta/` corpus qualifies a **property of the tool itself**:
its output must be a *function* of (source, tool-operational-environment) alone. A tool
whose output depends on hidden run-to-run state produces non-reproducible builds whose
CM baseline cannot be verified — DO-330 failure mode **TOR-FM-04 (nondeterminism)**
(`doc/03_plan/cert/tool_qualification_plan.md` §1.3).

Runner: `scripts/check/cert/tool-qual-meta.shs`.

## What is asserted

For every program in `deterministic/`, the runner executes it **K times** (default 5) in
**both** execution modes of the deployed binary —

- interpret  (`SIMPLE_EXECUTION_MODE=interpret`)
- compiled   (default codegen path)

— and requires that the K stdout streams of a given mode are **byte-identical**. Any
run-to-run divergence within a mode is a nondeterminism defect and fails the gate
(non-zero exit); the runner prints the two differing outputs as evidence.

This is a *per-mode run-to-run* property. It is intentionally narrow — see Scope below.

## Layout

- `deterministic/` — the gated corpus. Relative symlinks to the already-golden
  `positive/*.spl` fixtures (reuse, not duplication). Each was observed byte-stable
  across 5×2 runs on 2026-07-06 before being admitted here.
- `nondeterministic/array_identity.spl` — a **genuine** compiled-mode defect kept as the
  discrimination oracle (a valid program that leaks ASLR-varying heap identity
  `<array@0xADDR>`). **Excluded** from the gate walk, exactly as `known_defects/` is
  excluded from the `run-tool-qual-corpus.shs` gate. `--self-test` uses it to prove the
  runner actually flags nondeterminism rather than rubber-stamping.

## Genuine finding

`print` of a `List` value in compiled mode emits `<array@0xADDR>` — the heap identity, not
the elements — and that address varies with ASLR run-to-run. Interpret mode prints the
correct deterministic `[1, 2, 3]`. This is a real compiled-mode identity-leak /
mode-divergence defect, retained as reproducible evidence in `nondeterministic/`.

## Scope (honest)

Covered: **cross-run stdout reproducibility** of the deployed binary, per execution mode,
on one host.

NOT covered here: bit-for-bit reproducibility of emitted **binaries/artifacts**;
**cross-machine** or cross-TOE reproducibility; determinism of **stderr**; timing/RSS
determinism; O0-vs-O2 optimizer invariance (that is TOR-FM-05, a separate `meta/` axis).
Passing this gate means "same source, same host, same mode ⇒ same stdout each run" and
nothing stronger.
