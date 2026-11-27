# Outline identifier ranges collide with declaration prefixes

Status: source fix and prevention spec authored; **runtime NOT_RUN**. Narrow lane8 source follow-up, not completion of LSP qualification or unfinished PR7265.

## Original boundary and cause

Reviewed base: release `05c57b4368292f3df439c76cd94d4307d9311d77`. Its outline includes public visibility recognition from PR7502 (`2e982bd67fc64904504899c966e0aeba16114d00`). The production chain is `parse_outline_source` → `parse_outline_lines` → `_append_top_level_symbol`/`_append_nested_symbol` → `_parse_fn` or `_symbol` → `_symbol_start_col`.

The start calculation searched the entire signature for the first substring equal to the name. Therefore `fn f()` selected the `f` in `fn` at0 instead of3. Public recognition exposed the same mechanism for `pub fn p()` (0 instead of7) and `pub(package) fn package()` (4 instead of16). Class/binding/import names could collide with their keywords as well. This finding is a source-derived reproducer; no old or new binary result is invented.

## Change and acceptance

Reuse the existing canonical visibility-prefix owner and existing symbol kind to establish a search lower bound after the recognized declaration introducer. Preserve the authored signature, name/kind, parent, documentation, line, end calculation and trimmed-signature position convention. Field/domain behavior and declaration recognition remain unchanged. No new public interface, compiler/lib owner or competing parser is introduced.

The focused actual-owner SSpec covers eight scenarios: the original short function, public/private prefixes, equal scoped names, nested method/static forms, extern/repeated names, type/binding collisions, import/field/domain neighbors and unsupported-prefix recognition controls. Every ranged assertion also checks that the selected signature substring equals the authored name. The manual mirrors these cases and explicitly records NOT_RUN. Existing multi-space identifier parsing and unsupported async declaration recognition are outside this narrow location repair; neither is silently claimed fixed.

## Evidence and remaining gates

No admitted Simple runtime is available to this lane, and no Rust seed or heavy build was used. Source-only review/static whitespace evidence is distinct from SSpec execution. Historical PR7502 native workers are not the final source closure and are not reused as qualification of this change. Actual final-source compiler/lib/MCP/LSP checks, protocol regressions, native smoke, startup/request latency and RSS remain open under the compiler lane/root admission owner.

Open text-width PR7429 already owns the proposed `lsp_location.spl` and `lsp_reference_role.spl` migration sites, so this follow-up does not duplicate them. Broad revision-bound actions, source sessions and snapshot diagnostics stay within unfinished PR7265 and its explicit qualification limits.
