# Seed cfg_strip ignores compound arch `@cfg` (`not(a or b)`)

- **Status:** open
- **Severity:** P2. Fails open: wrong code on x86, no diagnostic.
- **Found:** 2026-11-20, Opus review of PR #10587 (riscv64 kernel link lane)
- **Component:** seed `src/compiler_rust/compiler/src/pipeline/cfg_strip.rs`

## Symptom
`cfg_attr_arch_verdict` (cfg_strip.rs ~line 325) recognises only `@cfg(<arch>)`
and `@cfg(not(<arch>))`. For anything else (`not(x86_64 or x86)`, `x86_64 or x86`,
`all(...)`) it returns `None`, meaning "not an arch gate, leave it in".
A per-arch variant set like

```
@cfg(x86_64)
fn f(): ...
@cfg(x86)
fn f(): ...
@cfg(not(x86_64 or x86))
fn f(): fallback
```

therefore keeps BOTH the x86 body and the fallback on a seed-built x86 kernel.
Either the duplicate is rejected, or the fallback silently wins: the x86 RTC
would return Err, and reset would skip the 0xCF9 write.

## Pure Simple
No gap. `src/compiler/50.mir/mir_cfg_select.spl` parses the full
`not`/`and`/`or` grammar (`_mcs_not`/`_mcs_and`/`_mcs_or`), and
`mir_cfg_select_cross_target_spec.spl` already covers `not (windows or arch = "arm")`.
This is a seed/pure-Simple semantic divergence.

## Workaround (tagged in source)
Use one arch per `@cfg` line (`pci.spl`, `rtc.spl`, `reset.spl` after #10587). The
`hal_arch_gating_contract_spec.spl` case "uses one arch per @cfg in shared drivers"
forbids the compound form in those files.

## Fix
Evaluate the attribute expression tree in the seed (not/or/and over arch
idents, mirroring `mir_cfg_select`). If any sub-term is not an arch, keep
returning `None`; never guess. Add a Rust unit test and turn on
`seed_cfg_strip_compound_arch_spec.spl` (the fix adds `cfg_compound_arch_verdict`).

## Repro
`test/01_unit/compiler/pipeline/seed_cfg_strip_compound_arch_spec.spl` (`@tag:in-development`, RED).
