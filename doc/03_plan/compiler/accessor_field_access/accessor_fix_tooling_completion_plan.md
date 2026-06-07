# Accessor Field-Access Tooling — Completion Plan

Status: planned (transform shipped; surfacing + cleanup outstanding)
Date: 2026-06-07
Owner: lint/fix tooling

## Context

The dummy-accessor auto-fix shipped to `origin/main`:

- ACC001 (`dummy_accessor`) lint flags trivial `get_*/set_*/is_*` forwarders.
- The auto-fixer rewrites call sites to direct field access
  (`obj.get_x()` → `obj.x`, `obj.set_x(v)` → `obj.x = v`) and, for globally
  **unambiguous** names, deletes the wrapper. It cleared **199 → 111** warnings.
- The new `L:short_grammar_field_access` refactor (in stdlib
  `std.tooling.easy_fix.accessor_field_access`, wired into `check_all_rules`)
  rewrites a class's own `self.`/`me.` dummy-accessor calls to field access —
  type-known and Safe — and is emitted by `bin/simple fix`/`lint`.

Two gaps remain. This plan covers both.

| Gap | Why it's open |
|-----|----------------|
| **A. Editor surfacing (LSP)** | The LSP serves only `check` (compiler) diagnostics; it never runs the lint/fix pipeline, so ACC001 and EasyFixes (incl. `field_access`) are not shown as diagnostics or quick-fix code-actions. |
| **B. The remaining 111 warnings** | They are **type-ambiguous** names (a real same-named method exists elsewhere). A textual delete would miscompile a real accessor, so clearing them needs **receiver-type** knowledge. |

```sdn
flow {
  transform: "field-access rewrite (shipped)"
  partA: "LSP code-actions (surface fixes in editors)"
  partB: "type-aware wrapper deletion (clear the 111)"
  transform -> partA
  transform -> partB
  note: "A surfaces; B removes. Independent; either order."
}
```

---

## Part A — LSP EasyFix code-actions + lint diagnostics

### Current behaviour (verified)

`src/app/lsp/lsp_handlers.spl::_collect_diagnostics` shells out to
`<binary> check <file> --format=json` and parses compiler diagnostics only
(`_parse_json_diagnostic` / `_parse_text_diagnostic`). There is **no**
`textDocument/codeAction` handler and **no** lint/EasyFix path. So ACC001 and
`field_access` never reach the editor.

### Goal

1. Surface lint warnings (ACC001, NAME001, SPIPE*, etc.) as LSP diagnostics.
2. Offer every `EasyFix` (incl. `field_access`, `short_grammar_*`,
   `deprecated_if_let`, …) as a `quickfix` code-action that applies the
   `Replacement`s as a `WorkspaceEdit`.

### Design

- **Diagnostics source**: add a lint pass alongside `check`. Prefer in-process
  `Linter.lint_source(path, content)` (from `compiler.tools.lint.main`) over a
  shell-out — it avoids a second process and already returns `LintResult`
  (code, level, line, col, message, optional `easy_fix`). Map
  `LintLevel.{Deny,Warn,Allow}` → LSP severity `{Error,Warning,Information}`.
- **Code-actions**: implement `textDocument/codeAction`. For the request range,
  call `collect_fixes_from_source(path, content)` (now `pub`) →
  filter `EasyFix`es whose `Replacement` lines overlap the range → build one
  `CodeAction` per fix: `title` = `easyfix_description`, `kind` = `"quickfix"`,
  `isPreferred` = (`confidence == Safe`), `edit` = `WorkspaceEdit` whose
  `TextEdit`s come from each `Replacement`.
- **Offset conversion**: `Replacement.start/end` are **byte** offsets; LSP
  positions are **line + UTF-16 code-unit** columns. Add a
  `byte_offset → (line, utf16_col)` converter (reuse the line table from
  `helpers.byte_offset_of` inverted). ASCII is 1:1; multi-byte/emoji must use
  UTF-16 counting to stay LSP-correct.
- **Capability**: advertise `codeActionProvider: { codeActionKinds: ["quickfix"] }`
  in the `initialize` result.
- **Config gating**: respect the project lint config (`simple.sdn`
  `dummy_accessor = warn/allow`) so suppressed lints don't appear.

### Files

| File | Change |
|------|--------|
| `src/app/lsp/lsp_handlers.spl` | add `lsp_handle_code_action`; extend `_collect_diagnostics` with a lint pass |
| `src/app/lsp/*` (capabilities/init) | advertise `codeActionProvider` |
| `src/app/lsp/*` (offset util) | byte→UTF-16 position converter |
| `src/lib/.../lsp` model (if any) | `CodeAction`/`WorkspaceEdit`/`TextEdit` types |

### Verification

- Unit spec: a `codeAction` request over a dummy-accessor `self.set_x(v)` line
  returns a `quickfix` whose edit yields `self.x = v`.
- Unit spec: ACC001 appears as a `Warning` diagnostic with code `ACC001`.
- Offset spec: a fix after a multi-byte character maps to the correct UTF-16
  column.
- Note: the native `bin/simple_lsp_mcp_server` / `bin/simple` are compiled
  artifacts; these changes are live only after a bootstrap rebuild/deploy.

### Risks

- UTF-16 column conversion is the classic LSP foot-gun — must be tested.
- Running lint per keystroke can be slow; debounce / run on save + on demand.

---

## Part B — Clear the remaining 111 (receiver-type-aware deletion)

### Why the 111 can't be deleted textually

A name is in the 111 because `total_headers[name] != dummy_count[name]` — i.e.
some class implements a **real** method of that name (often in an `impl` block,
e.g. `UICanvas.set_visible`, `MixerSnapshot.set_volume`). Rewriting every
`x.get_name()` → `x.name` would miscompile the classes whose `get_name` does
real work. The auto-fixer therefore (correctly) leaves these alone. To delete a
**specific** class's dummy wrapper we must rewrite **only** the call sites whose
receiver is statically that class.

### Step 0 — Classify the 111 (policy gate, do first)

Not all 111 should be deleted. Partition them:

- **(i) Production-redundant** — a dummy wrapper in real `src/` code with no
  behavioural reason → candidate for type-aware deletion.
- **(ii) Intentional** — mocks (`mocking_advanced`, `mock_phase*`), trait/alias
  forwarding tests (`trait_forwarding_spec`), teaching examples. Here the
  accessor *is* the subject under test; do **not** delete. Either suppress via
  `# simple:allow dummy_accessor` (add a file/line allow mechanism) or accept
  the warning by policy and exclude from the count target.

Output: a tracked list (`doc/08_tracking/...` or an sdn) tagging each of the 111.

### Step 1 — Receiver-type resolution (the core)

Two options; **Option 2 recommended**.

- **Option 1 — LSP-driven (external).** For each ambiguous `(class C, name N)`:
  `lsp_references` to enumerate every `.N(` call, then `lsp_type_at` /
  `lsp_hover` on each receiver to get its type; rewrite only `type == C`.
  - Pros: reuses existing LSP. Cons: per-call round-trips, reliability across
    ~20k files, slow; depends on Part A-adjacent LSP maturity.
- **Option 2 — compiler-driven, in-process (RECOMMENDED).** Run the compiler's
  name/type-resolution pass and read the **resolved receiver type** at each
  `MethodCall`/`MethodCallStatic` node. Emit a rewrite only when the resolved
  receiver type is the dummy-defining class. This is correct and fast (one pass,
  no round-trips) and integrates with the existing `accessor_fix` core.
  - Touchpoints: a new fix mode that consumes the typed AST (post Pass 0.5/type
    inference) instead of raw text; reuse `accessor_rewrite` for the edit and its
    statement-position / multi-arg / expression-context guards.

### Step 2 — Safe deletion protocol (per class C, name N)

1. Resolve all call sites of `N`; partition into `C-typed` vs `other`.
2. If **every** `C`-typed call is statement-rewritable AND there is **no**
   un-resolvable / `ANY`-typed / method-reference (`&:N`, `_.N`, bare `.N`)
   usage that could bind to `C.N` → rewrite the `C`-typed calls and delete
   `C`'s wrapper.
3. Otherwise **fail closed**: keep `C`'s wrapper, rewrite nothing for it, and
   report it as "needs manual review".

### Step 3 — Verification harness (reuse this session's gates)

- Dry-run report (counts per name: callers, C-typed, other, decision).
- `0 dangling references` check: for each deleted name, no residual `.N(`,
  `&:N`, `_.N`, or bare `.N` to a now-absent def (the textual grep family used
  this session).
- Baseline-vs-sweep spec comparison in an isolated `git worktree` (clean
  `origin/main` vs swept) over every changed spec → **0 regressions**.
- Bootstrap / `native-build` of the changed `src/compiler` + `src/lib` set.
- Apply in an **isolated worktree** (the shared jj working copy is reset by
  concurrent agents and clobbered writes this session).

### Step 4 — Roll-out

Pilot on 2–3 names (`get_count`, `get_data`), pass the full gate, then expand in
batches with agent-team verification fan-out. Target: drive ACC001 from 111 to
the residual set that is *intentional-only* (category (ii)).

### Files

| File | Change |
|------|--------|
| `src/compiler/.../fix/*` or a typed fix mode | receiver-type-aware rewrite + delete |
| `src/lib/.../tooling/easy_fix/accessor_*` | reuse parse/rewrite/guards |
| `doc/08_tracking/...` | the classification list + dry-run reports |
| `test/01_unit/compiler/tools/fix/*` | type-aware specs (C-typed rewritten, other untouched, fail-closed) |

### Risks

- Type resolution gaps (`ANY`, dynamic dispatch, cross-module non-`use` imports)
  → fail-closed keeps it safe but leaves some uncleared; report them.
- Intentional accessors must not be deleted — Step 0 is a hard prerequisite.
- This is the same false-green-prone area; keep the absolute-oracle gates.

---

## Sequencing

A and B are independent. Recommended order: **B first** (it reduces the 111, the
visible metric), **A second** (surfaces the remaining intentional ones + all
EasyFixes in-editor). Each lands behind its own verification gate; neither needs
the other.
