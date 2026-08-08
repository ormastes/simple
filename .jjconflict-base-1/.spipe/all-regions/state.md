# SStack State: all-regions

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — all_regions (Tree-sitter LSP surfacing, parser tests, schema{} contract AST, style{} typed theme, domain hardening)

## Task Type
feature

## Refined Goal
> Implement domain region block infrastructure: Tree-sitter outline/LSP metadata for domain blocks, parser test coverage for raw domain block capture, schema{} contract AST with JSON Schema compatibility model, style{} typed theme/layout subset model, and domain hardening scaffolding for music/bim/cad/city/rtl.

## Acceptance Criteria
- [x] AC-1: Tree-sitter domain outline — DomainOutlineEntry with kind, span, payload preview for LSP surfacing of schema/style/ui/music/bim/cad/city/rtl blocks
- [x] AC-2: LSP symbol provider — DomainSymbolProvider mapping domain blocks to DocumentSymbol with kind-specific icons/categories
- [x] AC-3: Parser test coverage — test raw domain block capture for all 7 domain kinds (schema/style/music/bim/cad/city/rtl), verifying kind extraction and payload preservation
- [x] AC-4: Schema contract AST — SchemaField + SchemaContract + SchemaValidation with field type/required/default, JSON Schema compatible type mapping
- [x] AC-5: Schema export model — SchemaExportFormat with json_schema/protobuf target, compatibility report
- [x] AC-6: Style typed theme — StyleProperty + StyleRule + ThemeSubset mapping to existing UI theme types
- [x] AC-7: Style layout model — LayoutConstraint + LayoutGrid with typed layout subset for style{} blocks
- [x] AC-8: Domain hardening scaffold — DomainHardenEntry + HardenReport per domain kind (music/bim/cad/city/rtl) with parse-status and known-limitation tracking
- [x] AC-9: Domain registry — DomainKindRegistry mapping kind string to handler, validation level, export capability
- [x] AC-10: Verification spec — 20 tests covering outline, symbols, parser, schema, style, hardening, registry

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 5 plan tasks. Existing: is_domain_block_kind() in parser_decls_part1.spl, HirDomainBlock in hir_types.spl, parse_raw_domain_block_payload() for raw capture.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/compiler/10.frontend/domain/domain_outline.spl — DomainOutlineEntry + DomainOutlineList + DomainSymbolProvider + DomainSymbolReport
- src/compiler/10.frontend/domain/schema_contract.spl — SchemaField + SchemaContract + SchemaValidation + SchemaExportFormat
- src/compiler/10.frontend/domain/style_theme.spl — StyleProperty + StyleRule + ThemeSubset + LayoutConstraint
- src/compiler/10.frontend/domain/domain_hardening.spl — DomainHardenEntry + HardenReport + DomainKindRegistry + DomainRegistryReport
- test/01_unit/compiler/all_regions_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
