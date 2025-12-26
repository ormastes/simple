# Simple Codebase Research: Grammars, AOP, SDN — Consistency Review and Alternatives (2025-12-23)

This document consolidates findings from the repository regarding grammar specifications and implementations, AOP (Aspect-Oriented Programming) capabilities, and SDN (Simple Data Notation). It highlights consistency issues across documentation, maps real code locations, and proposes pragmatic alternatives and next steps.

## Scope & Sources

- Read: CLAUDE.md (development guide), simple.sdn (project config)
- Specs: doc/spec/{sdn.md, language.md, syntax.md, lexer_parser.md, gherkin_dsl.md}
- Research: doc/research/{aop.md, sdn_self_hosting.md}
- Status/Features: doc/features/feature.md, doc/features/feature_done_*.md, doc/status/*, log/DOC_REFACTOR_MAP.md
- Code: src/{parser, compiler, sdn, runtime, driver, ui}/

---

## 1) Grammars: What’s Implemented vs. Documented

### Implemented Parser (Rust)
- Parser architecture:
  - src/parser/src/parser.rs — Recursive descent + Pratt parser for expressions
  - Submodules: expressions/, statements/, types_def/, helpers, diagnostics
  - Lexer with INDENT/DEDENT: src/parser/src/lexer/* (strings, numbers, comments, identifiers, indentation)
- Tests reference parser and lexer extensively across tests/system/* and tests/unit/*.

### Grammar Documentation
- Tree-sitter grammar documents:
  - doc/spec/parser/lexer_parser_grammar.md
  - doc/spec/parser/lexer_parser_grammar_definitions.md (contains `module.exports = grammar({ ... })` inlined)
  - doc/spec/parser/lexer_parser_grammar_expressions.md
  - doc/spec/parser/overview.md, lexer_parser_scanner.md (scanner/build.rs notes)
- EBNF sections exist in multiple specs (sdn.md, gherkin_dsl.md, basic_mcp.md, invariant.md, syntax.md).

### Gaps & Inconsistencies
- Docs repeatedly reference a Tree-sitter grammar and associated files (grammar.js, node-types.json, build.rs), but no actual runtime Tree-sitter project/code exists in the repository; it is documentation-only.
- The active Rust parser is authoritative. Doc/spec/parser/* should clearly state “reference-only” and defer to Rust parser for implementation status.

### Recommendations
- Adopt “Single Source of Truth” for grammar:
  - Mark Tree-sitter docs as design reference and planned work; point readers to src/parser/* as implemented grammar.
  - Add short “Implementation Status” banner to doc/spec/parser/* pages: “Current implementation: Rust recursive descent + Pratt (see src/parser). Tree-sitter is planned.”
- If editor integration is desired, scope a separate crate: tree-sitter-simple/ with minimal rules synchronized from Rust parser; generate tests from existing samples.

---

## 2) SDN (Simple Data Notation): Implementation & Consistency

### Implementation
- SDN crate: src/sdn/
  - lexer.rs (INDENT/DEDENT), parser.rs (one-pass LL(2)), value.rs, document.rs (editable), bin/sdn.rs (CLI: check/to-json/from-json/get/set/fmt)
- Spec: doc/spec/sdn.md (syntax, grammar, CLI examples, crate structure)
- Project usage:
  - simple.sdn (root project configuration) — used by build and tooling docs (simple/BUILD.md)
  - Compiler options produce coverage in SDN (src/compiler/src/coverage.rs and src/runtime/src/coverage.rs)

### Consistency
- Strong alignment between code and docs: spec references match crate paths; CLI usage in docs matches bin/sdn.rs; examples under doc/examples/*.sdn and fixtures under simple/std_lib/test/fixtures/sdn/*.
- Status docs confirm SDN Self-Hosting (#1051-1060) complete; lint config in simple.sdn (#1144) documented and present in src/compiler/src/lint.rs.

### Alternatives & Interop
- SDN vs TOML/JSON/YAML: doc/spec/sdn.md includes comparison table and conversion commands.
- Pragmatic stance:
  - Keep SDN as first-class project config.
  - Maintain conversion tooling (to/from JSON) for interop; consider TOML migration helper for legacy projects.
  - Validate schemas via “sdn check” and add CI hook.

### Actionable Next Steps
- Add a small “authoritative index” in doc/spec/sdn.md pointing to src/sdn/* and CLI.
- Wire CI target to run `sdn check simple.sdn` and format check.

---

## 3) AOP & Unified Predicates: Reality vs. Status Documents

### Code Locations
- Parsing & AST:
  - src/parser/src/statements/aop.rs — AOP statements (`bind on pc{...} -> Impl`, `forbid/allow` rules, etc.)
  - src/parser/src/ast/aop.rs — AST nodes for AOP/predicates
- Predicate parsing:
  - src/compiler/src/predicate_parser.rs — Unified predicate expressions (operators, wildcards, selectors)
- Weaving/runtime:
  - src/compiler/src/weaving.rs — Advice forms (before/after_success/after_error/around), join points (execution/within/attr/effect/test/decision/condition)
  - src/runtime/src/aop.rs — Runtime AOP support (proceed enforcement)
- DI/Mocking/Arch rules:
  - src/compiler/src/di.rs — DI bindings, profiles (#1010-1015)
  - src/compiler/src/mock.rs — Mocking via DI selectors (#1020-1025)
  - src/compiler/src/arch_rules.rs — Architecture rules (import/depend/use/export/config selectors)

### Documentation
- Primary spec: doc/research/aop.md — Unified predicate grammar, contexts (weaving/DI/mock/arch), semantics
- Status variance across files:
  - feature_done_11.md: “AOP & Unified Predicates (51/51) — Complete”
  - Multiple status docs claim 82%, 88%, 94%, 98% complete with differing test counts and feature tallies
  - release_validation_complete_2025-12-23.md indicates #1034-1035 checks (runtime AOP disabled on release) complete

### Consistency Issues
- Conflicting completion percentages and totals:
  - 51/51 complete vs. 46/49 vs. 40/49 verified vs. 98% — these cannot all be true simultaneously
- Tests counts differ across summaries (34/43/74), likely due to including/excluding DI/mock/arch tests or different time snapshots.

### Recommendations
- Establish an authoritative AOP status page (doc/status/aop_authoritative.md):
  - Derive automatically from feature.md and test suite discovery (cargo metadata + grep of tests) at build time.
  - Choose a single metric definition: “features complete” driven by feature.md IDs; “tests passing” driven by nightly CI.
- Update feature_done_11.md if it’s meant as archival snapshot; otherwise remove “51/51 complete” claim or move to archived state with date.
- In CLAUDE.md, replace the AOP summary line with a link to the authoritative status page.

### Alternatives & Pragmatic Guidance
- Runtime AOP in release builds should remain disabled (already validated by #1034-1035); prefer compile-time weaving.
- For cross-cutting concerns in Rust-hosted components (compiler code), continue using tracing (`#[tracing::instrument]`) — doc/architecture/dev.md endorses this as a pragmatic AOP alternative.
- Keep DI/mocking via unified predicates regardless of weaving enablement (as documented).

---

## 4) Grammar, AOP, SDN — Cross-Consistency Check

- Grammar docs vs. code: Parser implementation is Rust; Tree-sitter docs are design-only → mark accordingly.
- SDN: Code, specs, CLI, examples align well.
- AOP: Code is robust; documentation status is fragmented → consolidate to single source.
- CLAUDE.md provides an accurate structure map; however, AOP progress line should point to the single authoritative status page.

---

## 5) Suggested Improvements & Better Alternatives

- Documentation hygiene:
  - Add “Status: Implemented/Design-only/Archived” banners at top of major docs (parser, AOP, SDN) with last-updated date.
  - Introduce doc/report/authoritative_indexes.md that links to canonical implementation locations.
- Automation:
  - CI job to compute and publish AOP completion metrics from feature.md and test discovery (avoid manual percentages).
  - CI check for SDN configs: `sdn check simple.sdn` and format lint to ensure consistent style.
- Editor support:
  - If Tree-sitter is pursued, create tree-sitter-simple/ crate with rules excerpted from Rust parser; use doc/spec/parser/* as seed, then keep a sync script.
- Interop:
  - Maintain SDN ↔ JSON converters; consider TOML migration for legacy; keep SDN first-class.
- AOP usage guidance:
  - Recommend compile-time weaving by default; runtime AOP only in debug/testing; leverage tracing for compiler-internal cross-cutting concerns.

---

## 6) Quick Reference Index

- SDN
  - Spec: doc/spec/sdn.md
  - Crate: src/sdn/{lexer.rs, parser.rs, value.rs, document.rs, bin/sdn.rs}
  - Config: simple.sdn; examples: doc/examples/*.sdn; fixtures: simple/std_lib/test/fixtures/sdn/*
- Parser/Lexer
  - Code: src/parser/src/{parser.rs, lexer/*, expressions/*, statements/*, types_def/*}
  - Spec: doc/spec/{lexer_parser.md, syntax.md, language.md}
  - Tree-sitter docs: doc/spec/parser/lexer_parser_grammar_*.md (design-only)
- AOP & Predicates
  - Spec: doc/research/aop.md
  - Code: src/parser/src/statements/aop.rs; src/compiler/src/{predicate_parser.rs, weaving.rs, di.rs, mock.rs, arch_rules.rs}; src/runtime/src/aop.rs
  - Status: doc/features/feature.md; doc/features/feature_done_11.md; doc/status/* (to be consolidated)

---

## 7) Action Plan (Minimal, High-Impact)

1. Add “implementation status” banners to doc/spec/parser/* indicating Rust parser is the authoritative implementation.
2. Create doc/status/aop_authoritative.md generated from feature.md + test discovery; link from CLAUDE.md.
3. Add CI hooks:
   - Run `sdn check simple.sdn` and ensure formatting.
   - Publish AOP completion metrics from authoritative source.
4. Keep SDN as primary config, maintain JSON conversion tooling; provide TOML migration path for legacy.
5. For editor grammar, plan a tree-sitter-simple crate only if needed; otherwise, maintain Rust parser as the single source.

---

## 8) Appendix: Notable Lines Found (Evidence Pointers)

- SDN implementation references:
  - src/sdn/src/{lexer.rs, parser.rs, document.rs, bin/sdn.rs}, doc/spec/sdn.md, simple/BUILD.md
- AOP references and inconsistencies:
  - feature_done_11.md (51/51 complete), doc/status/aop_* (82%/88%/94%/98%), release_validation_complete_2025-12-23.md (#1034-1035)
  - Code: src/parser/src/statements/aop.rs, src/compiler/src/{weaving.rs, predicate_parser.rs, di.rs, mock.rs, arch_rules.rs}, src/runtime/src/aop.rs
- Grammar docs referencing Tree-sitter without code:
  - doc/spec/parser/lexer_parser_grammar_{definitions,expressions}.md include grammar.js sections; actual parser is Rust.

---

## 9) Summary

- SDN is solid and consistent across code/specs; keep as first-class with CI validation.
- AOP code is comprehensive, but documentation claims conflict; consolidate to an authoritative status.
- Grammar docs should be clarified: Rust parser is implemented; Tree-sitter materials are design references.
- Proposed changes are documentation-only and CI automation; no functional changes required to code today.
