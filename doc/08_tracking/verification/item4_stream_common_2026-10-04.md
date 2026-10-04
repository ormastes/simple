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

Source result: the stream resolver retains the canonical first common record,
merges maximum size/alignment independently, and prefers strong regular over
common over weak regular definitions. Layout computes a checked writable tail;
relocations rescan the same allocation order. Emission uses existing zero-fill
windows. Extra table/symbol scans consume the finite work budget and preserve
cancellation. This increases scan work; no runtime performance result is claimed.

The fast archive closure now records definition rank and distinguishes genuine
undefined demand from tentative demand. A selected common provider changes the
demand immediately, avoiding extra common/weak extraction while allowing strong
replacement. Independent review found no P0/P1 in either implementation.

GNU ld 2.46 fixture experiments executed in the research worktree establish the
external semantic oracle: undefined references extract common-only members;
existing common definitions extract strong regular members but not weak or
common-only members. This is not execution of the Simple implementation. See the
source-backed design `doc/05_design/compiler/linker/stream_common_2026-10-04.md`.
