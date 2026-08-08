# AST/Parser Memory Management Survey — Fixing the ~9x-per-char Blowup

Date: 2026-07-24
Scope: cross-compiler survey of parser/AST memory strategy, mapped onto Simple's
self-hosted frontend (`src/compiler/10.frontend/**`), to fix the 64GB / 1777-file
whole-program peak (vs ~90MB flat in the Rust seed equivalent).

## Problem recap

Self-hosted lexer/parser retains, per source character, roughly:
- 1 heap `text` object in `source_chars: [text]` (one object per char)
- 1+ heap `text` object per token (slice/copy of source)
- 1+ heap string field per AST node in the flat arena arrays (`stmt_*`, `expr_*`,
  `decl_*`) for names/literals — arrays are length-cleared between files but the
  element *objects* are never freed, and the runtime is no-GC with a live-pointer
  registry (`heap_registry`), so every one of those objects stays live and
  counted for the life of the process. Multi-file whole-program compilation
  accumulates all of it across all 1777 files.

## Cross-compiler survey

| Compiler/runtime | Lex representation | AST representation | Text/name storage | Lifetime model | Extensibility mechanism |
|---|---|---|---|---|---|
| **rustc** | `Token { kind, span }` — span is `(lo, hi)` byte offsets into the crate `SourceMap`, no per-char objects | HIR/AST nodes allocated in per-crate **arenas** (`bumpalo`/`TypedArena`), referenced by `NodeId`/`HirId` (u32) | Identifiers are `Symbol` — interned once into a global string-interner table (`rustc_span::Symbol`, backed by an index into a dedup'd string arena); comparisons are integer compares | Arena freed/dropped after the owning pass finishes (AST arena dies after lowering to HIR); interner is global and persists for the whole compilation, not per-node | New passes attach data via side tables keyed by `NodeId`/`HirId` (e.g. `TypeckResults`), not by mutating the node |
| **Zig** | Tokenizer yields `(tag, start)` only — token length is recomputed by re-scanning from `start` when needed, so tokens are 8 bytes, no text copy at all | AST is **struct-of-arrays** (`MultiArrayList`): `nodes: {tag, main_token, data}` indexed by `u32 Node.Index`; no pointers | Identifier/literal text is never copied out of the source buffer — everything is a `(start,len)`/token-index back-reference into the one source-file buffer held in memory | Whole per-file arena (source buffer + token list + AST) freed after ZIR/AIR generation for that file completes; nothing per-node to free individually | Extra semantic info lives in side arrays/hashmaps keyed by `Node.Index` (e.g. type info in Sema), not embedded in the node |
| **Lua** (reference impl) | Single-pass recursive-descent parser reads token-by-token from the source string; no persisted token stream | **No retained AST** — parser emits bytecode directly during descent; only a few nodes are stackified transiently for expression precedence resolution then discarded | Identifier strings are interned immediately into Lua's global string table (all short strings are interned, ref-counted, deduped) | Nothing beyond the current statement/expression's transient parse state; peak memory is O(1) w.r.t. source size beyond source+bytecode | Not designed for it — this is the "collapse the layer" extreme, useful as a lower bound on what's achievable, not a template for a compiler needing a real AST for later passes (types, MDSOC, LSP) |
| **CPython** | Tokenizer streams tokens from source buffer | AST built in a `PyArena` — a bump allocator; **all** AST nodes, identifier `PyObject*`s, and constant objects for a single compilation unit are arena-owned | Identifiers are interned via `PyUnicode_InternInPlace` into a process-wide interned-string dict — dedup across the whole compile, not per-node | `PyArena_Free(arena)` called right after `PyAST_CompileObject` turns the AST into a code object — the *entire* AST is freed in one call once bytecode exists; nothing AST-shaped survives compilation | New analyses in later CPython versions (e.g. `symtable`) walk the AST once while it's alive and extract into standalone tables (symbol tables, `co_consts`) before the arena free |
| **Roslyn (C#/VB)** | Tokens carry trivia + text but are pooled | **Red/green tree**: immutable "green" nodes are structurally shared, interned, and reused across edits (object pooling / weak-table dedup of structurally-identical subtrees); "red" nodes are thin, ephemeral wrappers with parent pointers, created lazily and GC'd freely | Green-node text spans reference an interned string table for common identifiers; trivia (whitespace/comments) stored as compact runs, not per-char | Green trees are long-lived (IDE re-analysis needs them) but heavily shared/pooled to keep steady-state memory low; red wrappers are throwaway | Side tables + the red/green split itself: red wrappers are the "extension layer" recomputed per-need without touching green data |
| **Clang** | `Token` = kind + `SourceLocation` (32-bit offset into a source manager) | AST nodes allocated via `ASTContext`'s **bump allocator** (`BumpPtrAllocator`), never individually freed — freed in bulk when the whole `ASTContext` is torn down at end-of-TU | `IdentifierInfo` interned once per identifier spelling in a global `IdentifierTable` (hash-consed); nodes store a pointer to the interned entry, not a copy of the text | One arena per translation unit; TU's arena released as a whole after codegen for that TU — no per-file element-wise freeing, but also no long-term accumulation across TUs in a multi-TU build (each TU's arena is independent and short-lived) | Attributes/side info can be attached via external side-maps (e.g. `ASTContext::getSourceManager()` lookups) without bloating the node |
| **V8 (parser)** | Scanner tokens hold source positions only | **Zone allocation**: each parse gets a `Zone` (bump arena); the AST for a function is allocated in that Zone and the whole Zone is freed after the function is compiled to bytecode (lazy parsing reparses inner functions from source on demand rather than keeping their AST) | `AstValueFactory` interns strings/identifiers once per Zone (and promotes hot ones into V8's global string table) | Zone lifetime = one function's compile; nothing outlives it except bytecode + the interned strings that get promoted | Lazy re-parse instead of caching stale AST — trades a bit of CPU for near-zero retained-AST memory |
| **Sorbet / Carbon** (data-oriented, modern) | Token = tag + span, no allocation | Flat, index-based node storage (`vector<Node>` + `NodeId`), data-oriented layout, cache-friendly iteration | All names interned into a `NameId`/`IdentifierId` table once, globally deduped | Whole-file node vector freed/reset between files where possible; interner spans the compilation | Parallel arrays keyed by `NodeId` for every additional analysis (types, scopes) — this is explicitly the pattern Simple already follows structurally |

## Cross-cutting principles (5)

1. **Never materialize per-character objects.** Lex directly from a flat
   byte/char buffer using integer offsets; a "char" is never boxed — every
   surveyed system (Zig, rustc, Clang, V8) treats the source file as one
   contiguous buffer read by index, not as a sequence of heap objects.
2. **Tokens are `(kind, start, len_or_end)` value structs, not owned strings.**
   Identifier/literal *text* is interned exactly once into a global,
   deduplicated string/symbol table (`Symbol`, `IdentifierInfo`, `NameId`,
   Lua's string table); everything else is a span back into the source buffer
   or a small integer id. Two tokens spelling the same identifier cost one
   table entry, not two heap strings.
3. **AST nodes live in per-file/per-TU arenas or bump allocators that are freed
   or reset in bulk after lowering to the next IR** (HIR/bytecode/ZIR/AIR).
   Only the interned symbol table and the lowered IR survive past that point —
   never element-by-element `free()`, always whole-arena teardown (Clang's
   `ASTContext`, CPython's `PyArena`, V8's `Zone`, rustc's arena-per-crate).
4. **Struct-of-arrays with integer indices beats pointer-linked/heap nodes** for
   both cache behavior and memory: Zig's `MultiArrayList`, Sorbet/Carbon's
   `vector<Node>` + `NodeId`, rustc's `NodeId`/`HirId` — this is the same shape
   as flat arenas.
5. **Index-based flat ASTs stay extensible via parallel side-tables keyed by
   node index/id**, not by widening the node struct — new passes (type info,
   MDSOC layer data, LSP hover info) add a `Vec`/array/dict keyed by the same
   `NodeId`, so the core node stays small and the arena-teardown story stays
   simple.

## Mapping onto Simple's actual gap

Simple's frontend (`src/compiler/10.frontend/core/lexer_chars.spl`,
`lexer_struct.spl`, `lexer_scanners.spl`, `lexer_types.spl`, and the
`20.hir`/`50.mir` flat arenas) already has the *structural* shape right: flat
`stmt_*`/`expr_*`/`decl_*` index-based arrays, matching principle 4/5 above.
The gap is specifically in what principles 1–3 forbid:

- **(a) Per-char text objects** — `source_chars: [text]` boxes every character
  of every source file individually. No surveyed compiler does this; all of
  them index a flat buffer. This is the single highest-multiplier offender
  (1 object per char, guaranteed).
- **(b) Token/node text as fresh heap strings instead of interned/span-based**
  — token and per-node string fields (names, literals) are allocated as new
  heap `text` values rather than (i) being spans into the source buffer or
  (ii) being deduplicated through a global interner. Every occurrence of the
  same identifier currently costs a fresh heap object; rustc/Clang/Zig/V8 all
  collapse this to one table entry per distinct spelling.
- **(c) No arena teardown between files** — arena arrays are length-cleared
  (`len = 0` or similar) between files but the *element objects* they pointed
  to are never freed, and the no-GC live-pointer registry (`heap_registry`)
  keeps counting them as live indefinitely. Every surveyed arena/zone design
  frees or resets the whole arena's backing memory at the same point Simple
  only resets a length counter — this is why memory accumulates linearly (in
  fact worse-than-linearly per the measurement) across 1777 files instead of
  bounded by the largest single file.

## Recommended staged fix path (ordered by risk, lowest first)

**Stage 1 — kill per-char text objects (lexer only, mechanical, low risk).**
Replace `source_chars: [text]` with a flat byte/char buffer indexed by integer
offset (principle 1). The lexer's scanners (`lexer_scanners.spl`) already walk
sequentially; change char access to buffer-index reads. No change to token or
AST shape required. This alone should remove the largest, most mechanical
multiplier and is safe to validate in isolation via the existing
`heap_registry` live-object counter before/after a single large file.

**Stage 2 — string interning table for identifiers/literals + per-file free of
non-interned temporaries (moderate risk, needs a new global table).**
Introduce one process-global (or per-compilation-unit) interning table keyed
by string content, returning a small integer id (mirrors `Symbol`/`NameId`).
Token and AST node "text" fields become either (i) a span `(start, len)` into
the still-live source buffer for cases the buffer outlives, or (ii) an
interned id for cases that must outlive the source buffer's life (i.e.
survive into later phases/IR). Any transient `text` allocated during scanning
that turns out *not* to be needed past tokenization (whitespace/comment
scratch, temporary concatenation buffers) is freed at end-of-file rather than
retained. Validate with `heap_registry` count staying flat across N files
with M unique identifiers each — expect steady-state proportional to unique
identifier count, not total character count.

**Stage 3 — arena element free-or-reuse between files (highest risk, touches
lifetime assumptions).** Once (a) and (b) remove the bulk of the retained
objects, extend the existing "length-cleared" arena reset to also
free-or-recycle the element objects themselves (bump-allocator-style bulk
free per file, mirroring Clang's `ASTContext` teardown / V8's `Zone` free),
rather than only zeroing the length counter. This requires confirming nothing
downstream (MDSOC layer data, cross-file symbol resolution, error reporting
that re-quotes source spans) holds a raw pointer into a freed arena past the
file boundary — anything that must survive should already have been migrated
to the Stage 2 interning table or the lowered IR before the arena is
recycled. This is the stage most likely to need the "side-table keyed by node
index" extensibility pattern (principle 5) if any per-node data was informally
relying on the arena never being freed.

## Validation requirements (do not skip)

- **`heap_registry` live-object counter**: the runtime's live-pointer registry
  already provides an authoritative live-object count; each stage should be
  validated by comparing the registry's peak/steady-state count before and
  after the change on the same fixed corpus, not just wall-clock RSS (RSS can
  be misleading with allocator retained-but-freed pages).
- **`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs`**: this is
  the existing multi-file regression gate and is the correct place to encode
  a hard ceiling (e.g. "peak heap_registry count grows sub-linearly / stays
  flat across file count" rather than the current ~9x-per-char accumulation).
  Also re-run the single-file variant,
  `scripts/check/check-stage4-selfhost-parse-memory.shs`, after Stage 1 to
  confirm the per-char win in isolation before layering Stage 2/3.
- Each stage should be landed and gated independently — per repo rules, do not
  bundle Stage 1–3 into one change; validate the multiplier reduction at each
  step so a regression is attributable to a single stage.

## Non-goals / explicitly rejected approaches

- **Lua-style "no AST retention"** is not applicable — Simple's compiler needs
  a retained AST/HIR for later passes (MDSOC layering, type checking, LSP),
  so the target is "arena freed after lowering," not "no arena at all."
- **Adding a tracing GC** is out of scope — the runtime is intentionally
  no-GC with a live-pointer registry; the fix is to stop retaining objects
  that don't need to survive, not to add collection machinery to clean up
  after them.
