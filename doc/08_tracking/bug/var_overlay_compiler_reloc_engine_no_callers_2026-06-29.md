# Variant Overlay — compiler/linker reloc_engine: No Active Callers (Seam Not Integrated)

Date: 2026-06-29
Candidate: `variants/compiler/reloc/` overlay keyed on target arch
(x86_64 / aarch64 / riscv32 / riscv64)

## Candidate alternative considered AND REJECTED: per-arch encoders (Opus review)

A first pass flagged the per-arch ENCODER files
(`encode_x86_64.spl`/`encode_aarch64.spl`/`encode_riscv64.spl`/`encode_riscv32.spl`)
as a "qualifying" build-time arch seam. **On review this FAILS criterion (2)**:
the encoders are NOT a build-time single-target choice — the compiler is
intentionally MULTI-TARGET at RUNTIME. Evidence:
- `src/compiler/70.backend/backend/native/mod.spl:21-24` imports ALL four
  encoders together, and lines 59/72/85/98 call each via a SEPARATE function
  (`encode_module`, `encode_module_aarch64`, `encode_module_riscv64`,
  `encode_module_rv32`) — distinct names, not one shared interface.
- `native_macho.spl:26,34` emits BOTH aarch64 AND x86_64 from the same binary.

So a single compiler binary dispatches target arch at runtime (per `--target`).
Baking ONE encoder via a build-time `variants/` choice would BREAK
cross-compilation — same failure mode as os/env path_separator (runtime decision,
not build-time). To qualify it would need the compiler to become single-target
per build (it is deliberately not). NOT pursued.

---

## Verdict on reloc_engine itself: FAILS — seam is not integrated (zero confirmed external callers)

### Evidence

File: `src/compiler/70.backend/linker/reloc_engine.spl` — exports:
`reloc_apply`, `reloc_apply_x86_64`, `reloc_apply_aarch64`, `reloc_apply_riscv`,
`reloc_patch_bytes`, `reloc_arch_from_machine` (lines 270-279).

Import search across entire `src/` for `use.*reloc_engine|import.*reloc_engine`:
- **Only one match**: `src/compiler/70.backend/linker/__init__.spl:224`
  — a comment `# Re-exported from reloc_engine.spl` followed by a re-export
  declaration. This is API surface exposure, not a call-site.

Call-site search for `reloc_apply|RelocArch|RelocTarget|RelocResult` outside
reloc_engine.spl:
- `linker/__init__.spl:225-226` — re-export only, not a call.
- `99.loader/loader/module_loader.spl:316,330,484` — variable named `reloc_result`
  from `moduleloader_apply_relocations()` (an internal function); does NOT import
  or call `reloc_apply*` from reloc_engine.
- `wine_dll_view_relocation.spl` / `wine_pe_loader_runtime.spl` — call
  `wine_pe_apply_relocation_plan` (Wine PE format); entirely separate API.

The per-arch encoders (`encode_x86_64.spl`, etc.) define their OWN R_* constants
and appear to implement inline reloc patching rather than delegating to reloc_engine.

### Criterion check

| Criterion | Result |
|-----------|--------|
| (1) Real existing variation | PASS — three arch branches x86_64/aarch64/riscv exist |
| (2) Build/deploy-target choice, not runtime-host | FAIL — target arch is a RUNTIME choice (`--target`); the compiler is multi-target (one binary emits all arches) |
| No unused code rule | FAIL — no confirmed caller outside linker package invokes reloc_apply* |

### Precondition to qualify later

Wire `reloc_apply` (or `reloc_patch_bytes`) into the actual native ELF/Mach-O
writer paths (`elf_writer.spl`, `_ElfWriter/writer.spl`, `smf_writer.spl`) so the
seam is live. Once there is a real call-site driven by target arch, the overlay
migration is straightforward: replace the `RelocArch` enum dispatch with a
compile-time-resolved module import.
