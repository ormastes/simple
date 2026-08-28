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

## Census

A parallel research lane is producing an asm/C census (planned at the session
scratchpad `hal/asm_census_REPORT.md`). It was not yet available when this
policy was written; numbers are pending and should be folded in when the census
lands. Raw gather artifacts (asm file lists, C asm sites, intrinsic users)
already exist in that scratchpad directory.

## Pointers back

Rules: `.claude/rules/language.md`, `.claude/rules/code-style.md`,
`.claude/rules/board-runnable.md`. Skills: `.claude/skills/impl.md`,
`.claude/skills/refactor.md`, `.codex/skills/coding/SKILL.md`,
`.agents/skills/impl/SKILL.md`, `.gemini/commands/coding.toml`. LLM wiki:
`doc/00_llm_process/layer_expert/{hardware,os,runtime}/skill.md`.
