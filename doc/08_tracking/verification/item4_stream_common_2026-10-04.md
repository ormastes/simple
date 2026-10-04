# Bounded ELF common-symbol verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

This slice implements existing common-symbol semantics in the file-backed
stream linker: coalescing, precedence, aligned writable zero storage and real
relocations, retaining read/output/scan/scratch limits. It must not allocate a
resident symbol table or a common-sized buffer. Logical limits do not prove
whole-job RSS enforcement; UnsupportedBudget remains required in production.

Test intent precedes implementation. Runtime execution, canonical docgen,
coverage, compiler/lib/MCP checks and NFR measurements are UNRUN pending an
admitted self-hosted runtime. Prior capped build diagnostics are not repeated.
