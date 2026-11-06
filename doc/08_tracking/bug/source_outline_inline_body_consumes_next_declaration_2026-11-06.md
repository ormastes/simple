# Native outline inline-body boundary

Status: CLAIMED by source_view / release100-next, 2026-11-06. Runtime reproduction and verification pending admitted pure-Simple CLI.

Static reproducer: `fn first(): 1` followed by `fn second(): 2`. The canonical `TreeSitter.skip_block` in `src/compiler/10.frontend/treesitter/outline.spl` initializes indentation depth to one even when no Indent token is present; it then consumes the following declarations until EOF. The sole direct grammar caller is `parse_function_outline`; the free `treesitter_skip_block` compatibility wrapper delegates to it.

Repair the canonical owner: inline bodies stop at the logical newline/EOF, retaining existing inline-asm and opaque block parsing. Indented bodies preserve the existing nested Indent/Dedent behavior. Do not duplicate a line-based grammar in the source viewer.

Required regressions: inline function followed by another declaration, adjacent inline class methods, nested multiline function bodies, and inline asm/opaque-block boundaries. The new native source-outline adapter must expose the second declaration and never label a heuristic scan as native syntax. Resolve only after admitted execution and landing.
