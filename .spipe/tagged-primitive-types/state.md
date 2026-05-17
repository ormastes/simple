# SStack State: tagged-primitive-types

## User Request
> refactor find all primitive type in public interface. and same types in function but caller not specify arg name. and make tag that same types on function but change place not make difference tag. check allow tagged also. with sonnet agents with opus advisor

## Task Type
code-quality

## Refined Goal
> 1. Extend DTYP001 lint to understand `# @tag(role_name)` annotations on parameters
> 2. When two same-type params have the SAME tag → suppress warning (commutative/interchangeable)
> 3. When two same-type params have DIFFERENT tags → warn if called positionally (swap = bug)
> 4. When two same-type params have NO tags → warn suggesting to add tags
> 5. Refactor all ~108 public functions with same-type primitive params to add `@tag` annotations
>
> **Mechanism:** `# @tag(role_name)` comment annotation on the line of the parameter
> **Deliverable:** Extended lint rule + all 108 functions annotated

## Acceptance Criteria
- [ ] AC-1: Lint parser recognizes `# @tag(name)` annotations on parameter lines
- [ ] AC-2: Same tag on same-type params = no warning (commutative case)
- [ ] AC-3: Different tags on same-type params = warning when called positionally
- [ ] AC-4: Missing tags on same-type params = warning suggesting to add tags
- [ ] AC-5: All ~108 `pub fn` with same-type primitive params in `src/lib/` are annotated with `@tag`
- [ ] AC-6: Lint integrates with `bin/simple build lint`
- [ ] AC-7: Existing tests pass after the annotation refactoring

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable
- Sonnet Agents: available (user-specified)
- Opus Advisor: available (user-specified)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-research (Analyst) — 2026-05-17
- [x] 3-arch (Architect) — 2026-05-17
- [x] 4-spec (QA Lead) — 2026-05-17
- [x] 5-implement (Engineer) — 2026-05-17
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** code-quality
**Refined goal:** Lint tool + report for "primitive type confusion" in public APIs
**Key observations from research:**
- ~50+ functions in `src/lib/` have 2+ same-type primitive params (i64, f64, text)
- Examples: `memset(dst: i64, value: i64, n: i64)`, `file_write(path: text, content: text)`, `linspace(start: f64, end: f64, steps: i64)`
- Simple currently has `type` aliases but they're NOT distinct types (just aliases)
- Some funcs are commutative (e.g., `hash_combine(h1, h2)` — order doesn't matter) and should NOT be flagged
- Linker code already has `# reason: positional` comments acknowledging this risk
- Named args exist in Simple syntax but interpreter rejects them at callsites (memory: `feedback_simple_parser_strict_callsites`)

**Approach:** Build analysis tool in Simple that parses pub fn signatures, classifies commutative vs non-commutative, and generates tagged type proposals.

### 2-research
<pending>

### 3-arch

**File layout:**
- New: `src/compiler/35.semantics/lint/param_tag.spl` — parser + checker
- Modified: `src/app/cli/query_lint.spl` — register `check_param_tag`
- Annotation target: `src/lib/**/*.spl` (~108 pub fn sites)

**Annotation format** (line immediately before `pub fn` / `fn`):
```
# @tag(h1=hash_value, h2=hash_value)
pub fn hash_combine(h1: i64, h2: i64) -> i64
```
Multiple same-type params share one `@tag(...)` line; one entry per param.

**Algorithm — `check_param_tag`:**
1. **Text-heuristic scan:** iterate source lines; detect `# @tag(...)` on line N, then expect `pub fn` / `fn` on line N+1.
2. **Parse tag map:** extract `{param_name → role_name}` from the annotation string.
3. **Signature grouping:** collect params sharing the same type; look up each in tag map.
4. **Role classification:**
   - All params of that type share one role → commutative → suppress DTYP001.
   - Params have distinct roles → non-commutative; for each positional call site → emit PTAG002.
   - No `@tag` annotation present on a `pub fn` with same-type params → emit PTAG001.
5. **Call-site check:** reuse DTYP001 positional-call detection; apply PTAG002 only when roles differ.

**Warning codes:**
- `PTAG001`: `pub fn` has ≥2 same-type primitive params with no `@tag` annotation.
- `PTAG002`: Same-type params carry different tags; positional call site risks silent swap.

**Integration:**
- Add `use compiler.semantics.lint.param_tag.{check_param_tag}` in `query_lint.spl`.
- `check_param_tag` returns `List<LintWarning>`; merged with existing results.

**Refactoring plan (~108 functions):**
- Phase A: `bin/simple run scripts/lint_tag_scan.spl` — grep `pub fn` with same-type primitives, emit candidate `@tag` lines to stdout.
- Phase B: Parallel Sonnet agents (disjoint lib subdirectory scopes) apply annotations + verify lint clean.
- Phase C: Final `bin/simple build lint` green gate before ship.

### 4-spec

**Test fixture:** `test/lint/param_tag_test_fixture.spl`

Cases covered:

| Case | Function | Expected |
|------|----------|----------|
| 1 | `copy_file(src: text, dst: text)` | PTAG002 — @tag present, different roles |
| 2 | `add_values(a: i64, b: i64)` | No warning — same tag (commutative) |
| 3 | `hash_bad(h1: i64, h2: i64)` | PTAG001 — pub fn, no @tag |
| 4 | `internal_helper(x: i64, y: i64)` | No warning — non-pub fn |
| 5 | `write_file(path: text, content: text)` | PTAG001 — pub fn, no @tag |
| 6 | `hash_combine(h1: i64, h2: i64)` | No warning — commutative allowlist |
| 7 | `linspace(start: f64, end_val: f64, steps: i64)` | PTAG002 — different roles on f64 pair |

**PTAG002 note:** Call-site positional detection is future AST work. PTAG002 fires on the
function definition when same-type params carry different roles (callers must use named args).

### 5-implement

**New file:** `src/compiler/35.semantics/lint/param_tag.spl`
- `pub struct ParamTagWarning` — code, severity, message, hint, fn_name, line_num, file_path
- `pub fn parse_tag_annotation(line: text) -> {text: text}` — parses `# @tag(a=role, b=role)` → map
- `pub fn extract_fn_name_from_sig(sig_line: text) -> text` — extracts fn name from declaration
- `pub fn extract_param_names_from_sig(sig_line: text) -> [text]` — parallel array of param names
- `pub fn extract_param_types_from_sig(sig_line: text) -> [text]` — parallel array of param types
- `pub fn check_param_tag(lines: [text], file: text) -> [ParamTagWarning]` — main scanner
- Constants: `BARE_PRIMITIVES`, `COMMUTATIVE_FN_NAMES`

**Modified:** `src/app/cli/query_lint.spl`
- Added `use compiler.semantics.lint.param_tag.{ParamTagWarning, check_param_tag}`
- Added `_check_param_tag_text(lines, file, format) -> i64` wrapper that calls `check_param_tag`
  and emits via `_diag_emit_or_collect` (JSON) or `print` (text), matching other heuristic lints
- Registered the call inside `_emit_text_heuristic_lints`
- Updated docstring to mention PTAG001/PTAG002

**Design decisions:**
- `check_param_tag` returns `[ParamTagWarning]` (not inline emit) because the file lives in
  `compiler.semantics.lint` and cannot import `app.cli.query_rich_common._diag_emit_or_collect`
- The emit wrapper in `query_lint.spl` handles both JSON and text format paths
- Blank lines and other `#` comment lines between `# @tag(...)` and `fn` are tolerated
- PTAG002 emitted on fn definition only; call-site detection deferred to AST pass

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
