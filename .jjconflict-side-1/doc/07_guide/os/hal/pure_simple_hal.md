# Pure-Simple HAL Policy — Simple First, C as Boundary, Asm Last

**Status:** Policy (user directive, 2026-08-28). This is the single full statement;
guides, rules, skills, and LLM-wiki entries point here instead of duplicating it.

## 1. Pure Simple first

Never write a C version of a fix or feature when pure Simple can do it. The only
sanctioned non-Simple code is the Rust seed (`src/compiler_rust/`) and the 3
bootstrap scripts. The C runtime (`src/runtime/`) is a **boundary**, not a place
for logic: it exists to touch the OS/hardware surface, and everything above that
surface is written in Simple. A C implementation of expressible-in-Simple logic
is a defect, not a shortcut.

## 2. Bootstrap C keeps a Simple twin

Where bootstrap genuinely requires C (`src/runtime/`), the same behavior must
ALSO exist as a pure-Simple implementation. The C copy is then verifiable
against its twin and eventually replaceable by it. Prior art and the enforcing
gate: the C/Simple dual-run shadow harness —
`scripts/check/check-dual-run-shadow.shs` (fail-closed;
`src/lib/common/spec/dual_run.spl` `dual_check_f64`/`dual_check_text` over
migrated C<->Simple symbol pairs), documented in
`doc/07_guide/infra/c_migration/dual_run_shadow.md`. New bootstrap-required C
lands together with its Simple twin and a dual-run pairing; C without a twin is
migration debt, tracked, not accepted silently.

## 3. Minimize asm — even in Simple

HAL / low-level Simple code prefers, **in order**:

1. **Typed bitfield register views + volatile/MMIO-typed access** — model the
   register, don't poke raw addresses.
2. **Tags/annotations that prevent harmful optimization** (no-reorder,
   no-elide, exact-layout) or a strict-running mode, when ordinary typed access
   would be miscompiled-by-optimization.
3. **Compiler intrinsics** for operations the type system cannot express.
4. **Inline asm ONLY for architecturally irreplaceable ops:** boot entry,
   CSR/MSR access, context switch, interrupt entry/exit, and barriers/atomics
   the ISA requires. Anything below rung 4 written in asm is a bug to fix or a
   concrete compiler feature request to file — never a normalized workaround.

See also `doc/07_guide/language/rt_hal_attribute.md` (`@rt(hal, ...,
providers: pure+c+rust)`) — the provider mechanism that makes rules 1–2
enforceable per operation.

## Pointers back

Rules: `.claude/rules/language.md`, `.claude/rules/code-style.md`,
`.claude/rules/board-runnable.md`. Skills: `.claude/skills/impl.md`,
`.claude/skills/refactor.md`, `.codex/skills/coding/SKILL.md`,
`.agents/skills/impl/SKILL.md`, `.gemini/commands/coding.toml`. LLM wiki:
`doc/00_llm_process/layer_expert/{hardware,os,runtime}/skill.md`.

## Census numbers (landed 2026-08-28)

From `doc/01_research/os/hal/pure_simple_hal_asm_minimization_2026-08-28.md`
(counted at `0fce018eda3`; the 36 owned `.S` paths re-listed at release tip
`3df474c19fd` match):

| Population | Files | Sites | Lines |
|---|---|---|---|
| Standalone `.S` (src/**) | 36 | — | 2,543 (all class (a) irreplaceable text; movable into `.spl` as `@naked` bodies) |
| Standalone `.S` (examples) | 26 | — | 2,886 |
| Simple inline-asm sites | 14 HAL files | 126 | ~430 — ~111 eliminable via CSR/barrier intrinsics |
| C asm statements | 28 | 182 | ~360 — ~200 eliminable |
| Pure-perf asm (class d) | 0 | 0 | 0 — perf code is C-with-intrinsics, a strict-codegen/dual-run target |

Ranked features (asm eliminated per cost): 1 CSR/sysreg intrinsics, 2
barrier/cache intrinsics, 3 `@naked`/`@section`/`@interrupt`/`@align`/`@global`
end-to-end, 4 `@volatile`/`@no_reorder` + `@exact_layout` bitfield MMIO, 5
strict-codegen + dual-run.

Measured 2026-08-28 (survey §0): a `@naked` twin of
`src/runtime/startup/linux/x86_64/start.S` compiled by the Rust seed emits the
28-byte body **byte-identical** to `as`, but with a trailing `ret` (seed
ignores `@naked`), in `.text` regardless of `@section` (seed ignores it), and
AT&T `$` immediates must be written `$$` (raw block passed verbatim as an LLVM
template). Every pure-Simple stage binary SEGVs on any input, so the
self-hosted path cannot yet compile or verify embedded asm — the blocker is
compiler stability, not asm-compile cost (asm lowering is milliseconds;
seed startup is ~110 s / 2 GB).

## Design and plan

- Design (asm-embedding contract, five features, dual-running architecture):
  `doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md`
- Plan (feature phases with acceptance specs, `.S`→`.spl` batches, Opus review
  gates, soak/stability bar): `doc/03_plan/os/hal/asm_to_simple_migration_plan.md`
- Survey of existing HAL docs and the Q1/Q2 evidence:
  `doc/01_research/os/hal/hal_asm_embedding_dual_run_survey_2026-08-28.md`
- Glossary: `doc/glossary.md` "Dual running".
