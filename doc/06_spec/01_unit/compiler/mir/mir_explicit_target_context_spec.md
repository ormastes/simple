# Explicit MIR target context preparation

Source: `test/01_unit/compiler/mir/mir_explicit_target_context_spec.spl`.
Status: authored manual; executable and generated-manual qualification pending.

This preparatory API supports the immutable HIR / TargetHIR plan's strict target
normalization boundary. It does not implement TargetHIR, deep freezing, portable
HIR admission, cache identity, or target backend capability checks.

| Scenario | Observable requirement |
|---|---|
| Six architecture widths × Linux, Windows, SimpleOS | Explicit tuples retain their requested architecture, OS and ABI independently of the compiler host. Recognition is not cross-compilation or execution qualification. |
| Canonical aliases | Trim/case normalization agrees with the existing context owner; ARM subarchitecture, ABI, backend and version survive. |
| Missing or ambiguous target | Empty/host/native, unknown suffixes and extra components return named errors; legacy host behavior remains available only through the old API. |
| Lossy CPU names or unknown backend | ISA-bearing RISC-V and x86-generation spellings (`i386` through `i686`) are refused until their details can be represented; empty/auto/unknown backend never silently becomes LLVM. |
| Architecture-specific ABI | RV32/lp64d, RV64/ilp32d and non-ARM eabi combinations fail; valid RISC-V contexts still cannot authorize collection lowering. |
| Existing collection policy | Every previously recognized explicit tuple remains admitted only for the original backend set. Newly recognized contexts do not widen collection support. |

The executable cases exercise the actual pure context owner and named error
results. No compiler invocation or native target result is implied by this manual.
