# Native outline import forms

Status: CLAIMED by source_view / release100-next. Runtime regression execution NOT_RUN pending admitted compiler.

The canonical token outline in `src/compiler/10.frontend/treesitter/outline.spl` dispatches KwImport but not distinct KwUse, even though the lexer exposes both. `parse_module_path` consumes the dot before grouped/star imports, but `parse_import` expects another dot before reading those forms. A leading relative dot reaches `parse_identifier` before any relative handling. These source findings block exact native import grouping for normal repository source; do not work around them in a viewer grammar.

Repair the existing owner: route KwUse to parse_import, consume braces/star at the position left by parse_module_path, preserve a leading relative prefix, and keep existing alias processing. Cover use/import, grouped items, wildcard, relative path and alias alongside noncontiguous source-range grouping. `parse_module_path` has only the import grammar caller plus its compatibility wrapper.

The same inspected dispatcher annotated parse_attributes output as parser Attribute rather than the actual AttributeOutline return type. Correct that owner annotation and remove its unnecessary full parser-type import. No external parser or alternate line grammar is introduced.

Resolve only with admitted native/provider test receipts and landing. Current source review is not execution evidence.
