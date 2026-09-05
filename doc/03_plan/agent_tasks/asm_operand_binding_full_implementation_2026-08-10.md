# Inline-asm operand binding — full implementation plan

**Slug:** `asm_operand_binding_full_2026-08-10`
**Written:** 2026-08-10
**Audience:** a single agent per work unit, working alone, no memory of this
session. Each unit states its own preconditions and exact scope.
**Precondition already met:** the compile-time diagnostic for unbound
`{name}` placeholders in the bare `asm """..."""` form has already landed —
`check_asm_unbound_placeholders` in
`src/compiler/10.frontend/core/_ParserPrimary/asm_raw_parsing.spl:171-191`,
wired from `parse_raw_asm_braced_payload`/callers. Do not re-implement it;
build on top of it (units below only need to special-case it for the bound
form, see Unit A).
**Bug doc (read first, it is the source of truth for prior findings):**
`doc/08_tracking/bug/asm_template_placeholders_never_bind_2026-08-07.md`.

---

## 0. What is actually true today (verified by reading code, not guessed)

**The "bound form" (`asm volatile("...", op = in(reg) value)`) that the bug
doc's Root-Cause-A section describes as already implemented is NOT
implemented at the parser level.** This session re-verified from source:

- `struct AsmConstraint` / `enum AsmConstraintKind` / `enum AsmLocation` exist
  in `src/compiler/10.frontend/parser_types_expr.spl:698-722` — types only.
- The flat-AST bridge constructor `flat_asm_expr()` in
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:593-600`
  hardcodes `constraints: []` and `clobbers: []` **unconditionally**, for
  every `asm` spelling. There is no code path that ever produces a non-empty
  `AsmConstraint` list.
- `parse_legacy_parenthesized_asm()` in
  `src/compiler/10.frontend/core/_ParserPrimary/asm_raw_parsing.spl:193-217`
  — the function that handles the parenthesized `asm volatile(...)` spelling
  — only collects `TOK_STRING_LIT` tokens and joins them with `\n`. It has no
  logic for `,`, `=`, `in(...)`, `out(...)`, or identifiers; those tokens are
  silently skipped (`parser_advance()` in the catch-all branch). So
  `asm volatile("mov r0, {op}", op = in(reg) value)` today parses only by
  accident — it extracts the string literal and drops the operand list
  entirely, which is functionally identical to the bare form.
- The comment block directly above `check_asm_unbound_placeholders`
  (`asm_raw_parsing.spl:162-170`) states this explicitly: *"Bare `asm "..."`
  / `asm { ... }` / `asm volatile(...)` text has NO operand-binding mechanism
  reachable from source syntax ... every parse path above ... funnels into it
  with no constraint/operand list attached."*
- Downstream, `HirAsm` / `MirInstKind.InlineAsm` (referenced from
  `hir_lowering/expressions.spl:1912` `lower_asm`, and
  `_MirLowering/function_lowering.spl`) DO have `inputs`/`outputs` fields
  ready to carry constraint data — the HIR/MIR shape exists — but since the
  parser never populates `AsmConstraint`, those lists are always empty in
  practice too. The bug doc's Root-Cause-C claim ("out(reg) compiles and is
  silently dropped") is consistent with this: whatever reaches codegen from
  today's parser has no real operand list, so there is nothing to write back.

**Conclusion: there is no working prior art in this codebase for `{name}`
substitution.** Both the bare form and the "bound" form are equally
unimplemented for operand binding; the bound form differs only in that its
surface syntax already parses (permissively, by ignoring most of it) without
a hard error, which makes it look further along than it is.

## 1. Rust `asm!` semantics this design borrows (reasoned from what's already
   spec'd in this repo, not fetched externally)

The existing struct shapes already encode the right target model — this is
not a from-scratch design, it's completing what `AsmConstraint` describes:

- `in(reg) expr` / `out(reg) var` / `inout(reg) var` — operand direction +
  register class, matching `AsmConstraintKind.{In,Out,InOut,LateOut}` and
  `AsmLocation.{Reg,RegSpec,Mem,Imm}` already declared.
- Named operands (`op = in(reg) value`) bind a `{op}` placeholder in the
  template to that operand's assigned register at codegen time, matching
  `AsmConstraint.name`.
- `clobber_abi("C")` / explicit clobber lists — `AsmExpr.clobbers: [text]`
  already exists as a field.
- Positional operands (`{0}`, `{1}`, ...) are Rust's fallback when operands
  are unnamed; **out of scope for this plan** — every real call site in this
  repo uses named placeholders, so positional numbering adds parser
  complexity with no current consumer. File a follow-up bug if a future
  caller needs it; do not build it speculatively (see `code-style.md`:
  never add unused code).
- Explicit register constraints (`out("eax")`) are needed by `cpuid` (clobbers
  RBX) and `rdtsc`-family reads — the bug doc confirms `out("eax")` currently
  fails to parse (`Unexpected token: expected identifier, found FString(...)`).
  This plan's Unit A must support `AsmLocation.RegSpec(text)` parsing, not
  just bare `reg`.

## 2. Recommended approach — with reasoning

**Approach chosen: implement real operand binding for the bound
`asm volatile(...)` form; keep the bare `asm """..."""` form
diagnostic-only forever (no substitution ever added to it). Migrate the two
remaining files to the bound form only after binding is proven correct.**

Reasoning:

- Scope check performed this session: exactly **2 files, 8 placeholder
  lines** now use the bare form with unresolved `{name}` placeholders —
  `src/os/kernel/arch/x86_64/timer.spl` (2 lines: `{lo}`, `{hi}` in
  `_read_tsc`) and `src/os/kernel/arch/x86_64/topology.spl` (6 lines: `{leaf}`,
  `{subleaf}`, `{eax}`, `{ebx}`, `{ecx}`, `{edx}` in `x86_cpuid_regs`). The
  other three files named in the bug doc (`volatile.spl`,
  `semihost_transport.spl`, `system_api.spl`) are already closed (deleted or
  rerouted to SFFI) per that doc's "Fixes applied" table — re-verified via
  `grep -rln 'asm """' src/` this session, which found no other repo source
  files with brace placeholders. This means "add substitution to the bare
  form" would have to design and implement full Rust-`asm!`-shaped grammar
  changes to the primary `asm """..."""` string-template path used
  everywhere else in the tree (including `cli`/`hlt`-only bare blocks that
  must keep working unchanged), to serve only 2 files — a much larger,
  riskier surface than fixing the one already-designated bound-form entry
  point and rewriting 2 files to use it.
- The bare form's compile-time diagnostic already gives a clear, actionable
  error steering users to the bound form (see its message text: "remove the
  placeholder or inline the value directly" — this plan additionally updates
  that message once the bound form is real, see Unit A). Reversing that
  decision now (making the bare form itself do substitution) would
  contradict the intentional design already landed and documented in the
  code comment at `asm_raw_parsing.spl:162-170`.
- The bound-form grammar (`op = in(reg) value`) is the only spelling any
  existing type (`AsmConstraint`) was ever built to represent, so completing
  it is finishing an existing design, not inventing a new one.

## 3. Parallel work units

Four units, ordered by dependency but each independently assignable. **A is
a hard prerequisite for B, C, and D** — do not start B/C/D until A's operand
list is real and lands, or they will build against a moving target. B and C
touch disjoint file sets and can run in parallel once A lands. D depends on
A+B (needs real binding to write meaningful acceptance tests) and C (needs
final file contents to test against), so it runs last, but its spec
*scaffolding* (empty spec files, oracle stubs) can be written in parallel
with A.

### Unit A — Parser: real operand-list parsing for `asm volatile(...)`
**TIER: judgement** (grammar/AST decisions)

- **Touches:**
  `src/compiler/10.frontend/core/_ParserPrimary/asm_raw_parsing.spl`
  (replace `parse_legacy_parenthesized_asm`'s body — keep the function name
  and call sites stable), `src/compiler/10.frontend/parser_types_expr.spl`
  (only if `AsmConstraint`/`AsmLocation` need new fields — they likely
  already have everything needed; do not add fields speculatively),
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (`flat_asm_expr`
  — must build the real `[AsmConstraint]` and `[text]` clobber list instead
  of hardcoding `[]`).
- **Must NOT touch:** the bare-form diagnostic
  (`check_asm_unbound_placeholders`) except to adjust its error message
  text if the bound-form spelling changes; HIR/MIR/backend files (Unit B's
  territory); `timer.spl`/`topology.spl` (Unit C's territory).
- **Design decisions this unit must make explicit (not leave ambiguous):**
  parse `name = in(reg) expr` / `name = out(reg) expr` / `name = inout(reg) expr`
  as comma-separated operand clauses after the template string; parse
  `name = out("eax")` / `in("edi")` as `AsmLocation.RegSpec("eax")`; parse a
  trailing `clobber_abi("C")` or bare clobber-register list into
  `AsmExpr.clobbers`; template placeholders `{name}` must resolve against the
  operand list's `name`s at PARSE time (reuse
  `check_asm_unbound_placeholders`'s brace-scanning logic, but check against
  the actual bound names instead of always erroring) — a bound-form
  `{name}` with no matching operand must still be a parse-time error, not a
  silent passthrough.
- **Acceptance test:** a scratch `.spl` file with
  `asm volatile("mov {out}, {in}", out = out(reg) x, `in` = in(reg) y)`
  parses to an `AsmExpr` with `constraints.len() == 2` and correct
  `name`/`kind`/`location` per constraint (verify via a print-debug harness
  or LSP `lsp_hover`/AST dump — do not just check parse succeeds with rc=0,
  that was exactly the vacuous-test trap the bug doc's Root-Cause-C section
  warns about). Also verify `out("eax")` parses to
  `AsmLocation.RegSpec("eax")`, not a parse error.

### Unit B — HIR/MIR/LLVM-backend: real register allocation + write-back
**TIER: judgement** (this is root cause C — the most serious open defect)

- **Touches:** `src/compiler/20.hir/hir_lowering/expressions.spl`
  (`lower_asm`, ~line 1912), `src/compiler/50.mir/_MirLowering/function_lowering.spl`
  (asm lowering, ~lines 900-925), LLVM codegen for `MirInstKind.InlineAsm` in
  `src/compiler/70.backend/backend/_MirToLlvm/` (find the asm-emission site;
  it must emit LLVM's `asm sideeffect "...", "constraints"(...)` form with
  real operand/output value bindings, not just the raw template string).
- **Must NOT touch:** `asm_raw_parsing.spl`, `convert_nodes.spl` (Unit A's
  territory — consume `AsmExpr.constraints` as A defines it, don't
  reshape it); `timer.spl`/`topology.spl` (Unit C).
- **Acceptance test:** the exact repro from the bug doc must pass with real
  values, not zeros:
  ```
  fn asm_copy(src: i64) -> i64:
      var dst: i64 = 0
      asm volatile("movq $1, $0", dst = out(reg) dst, src = in(reg) src)
      dst   # must return 7 when called with src=7, NOT 0

  fn asm_const() -> i64:
      var dst: i64 = 0
      asm volatile("movq $$42, $0", dst = out(reg) dst)
      dst   # must return 42, NOT 0
  ```
  Run through the real LLVM/native pipeline (not the interpreter — inline
  asm has no interpreter semantics) and check the actual returned integer
  value, per `feedback_measurement_requires_a_pinned_worktree` /
  `reference_sabotage_is_not_an_oracle_for_lint` memory entries: verify
  against a freshly rebuilt, provenance-checked binary, not a stale deployed
  one.

### Unit C — Migrate `timer.spl` / `topology.spl` to the bound form
**TIER: routine** (mechanical, but MUST wait on A+B)

- **Touches:** `src/os/kernel/arch/x86_64/timer.spl` (`_read_tsc`, 1
  function), `src/os/kernel/arch/x86_64/topology.spl` (`x86_cpuid_regs`, 1
  function).
- **Must NOT touch:** anything under `src/compiler/`. Do not "fix forward" by
  also implementing `@cfg("target_arch", ...)` gating or `asm match:` parsing
  — those are the bug doc's Root-Cause-B and are explicitly out of scope for
  this plan (separate defect, separate plan). Do not touch
  `semi_host_call`'s withdrawn stub in `semihost_transport.spl`/
  `system_api.spl` — that's already closed per the bug doc.
- **Exact rewrite target** (already spelled out in the bug doc, mechanical
  once A+B land):
  ```
  asm volatile("rdtsc", lo = out(reg) lo, hi = out(reg) hi)
  ```
  for `_read_tsc`, and for `x86_cpuid_regs`, register-pinned operands
  (`cpuid` reads EAX/ECX, writes EAX/EBX/ECX/EDX, and clobbers RBX per the
  `push rbx` / `pop rbx` save in the current bare template) — use explicit
  `RegSpec` bindings (`leaf = in("eax") leaf`, etc.) plus a clobber list
  entry for `"rbx"` if Unit A's grammar makes that spellable; if Unit A
  cannot express a clobber-without-bind for rbx, keep the existing
  push/pop-rbx sequence inside the template and only bind the actual
  operands — do not invent new asm semantics inside this unit, escalate to
  whoever owns Unit A if the grammar is insufficient.
- **Acceptance test:** on real x86_64 hardware or an OVMF-booted QEMU proxy
  per `.claude/rules/board-runnable.md` (SimpleOS kernel code — QEMU alone is
  not a completion), `_read_tsc()` returns a monotonically increasing,
  non-zero value across two calls, and `x86_cpuid_regs(0, 0)` returns a
  non-zero max-leaf in `eax` — both explicitly called out in the bug doc as
  the values that were silently zero before Unit B's fix. Do not accept
  build-succeeds (rc=0) as the acceptance bar; that is the exact vacuous
  test the bug doc documents as having previously hidden root cause C.

### Unit D — Spec tests for all of the above
**TIER: routine**, but blocked on A+B (and ideally C) landing first

- **Touches:** new or existing spec files under `test/01_unit/compiler/native/`
  (there is already `test/01_unit/compiler/native/asm_match_spec.spl` per the
  bug doc — follow its structure/location convention for a new
  `asm_operand_binding_spec.spl`), and `test/01_unit/compiler/backend/` for
  LLVM-codegen-level checks if that's the existing convention for backend
  specs (check `test/01_unit/compiler/backend/interpreter_backend_spec.spl`,
  currently modified in this session's WC, for house style before adding a
  new file there).
- **Must NOT touch:** production compiler code (any file owned by A/B/C).
- **What it must cover (from the bug doc's own list of what was silently
  broken and must not regress silently again):** (1) named `in`/`out`/`inout`
  operand binding round-trips a real value through registers (the
  `asm_copy`/`asm_const` cases from Unit B, promoted to a permanent spec, not
  a throwaway repro); (2) `out("eax")`-style explicit register constraints
  parse and bind correctly; (3) the bare-form diagnostic
  (`check_asm_unbound_placeholders`) still fires on an unbound `{name}` in a
  bare `asm """..."""` block — this is a regression guard so a future change
  to Unit A's parser doesn't accidentally start silently accepting bare-form
  placeholders; (4) a bound-form `{name}` with NO matching operand is a
  parse-time error (from Unit A), not a pass-through to LLVM.
- **Acceptance test:** the spec file runs GREEN under
  `bin/simple test <path>` with an explicit `SPEC FILE VERDICT ...
  executed=N` line showing N>0 (per
  `reference_simple_test_with_absolute_path_runs_nothing_exits_zero` memory
  trap — never trust bare exit-code 0), AND at least one deliberately
  sabotaged variant of each positive assertion (e.g. force `dst` to stay 0)
  is confirmed to turn the spec RED, proving the oracle isn't a tautology
  (`reference_agent_written_oracles_default_to_tautology` memory trap).

## 4. Explicitly out of scope for this plan

- `@cfg("target_arch", ...)` gating (bug doc Root-Cause-B) — separate defect.
- `asm match:` parsing in stage2 — separate defect, already spec'd
  elsewhere.
- Positional (`{0}`, `{1}`) operand numbering — no current caller needs it;
  do not build speculatively.
- Any file other than `timer.spl`/`topology.spl` — the grep in §2 found no
  other remaining bare-form placeholder call sites in owned source as of
  2026-08-10; re-run
  `grep -rln 'asm """' src/ --include=*.spl | xargs grep -l '{[a-zA-Z_]'`
  before starting Unit C in case a new one was added meanwhile.
