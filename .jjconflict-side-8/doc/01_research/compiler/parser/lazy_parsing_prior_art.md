# Lazy Parsing Prior Art

## User Request

Survey existing lazy-parsing implementations in production language runtimes/compilers, to inform
adding a lazy-parsing mode to the Simple language's parser/interpreter (parse signatures eagerly,
defer function bodies until first call).

---

## 1. V8 (JavaScript / Chrome)

**Architecture:** Two-pass system — PreParser + full Parser.

### What the PreParser must still do

Even when skipping a function body the PreParser must:
- Tokenize the entire body (bracket/paren balance to find the end).
- Verify syntactic validity (early errors per the spec).
- Build real `Scope` objects and resolve variable declarations so the outer function can
  be compiled correctly (stack vs. context / heap allocation decision).
- Record variable allocation metadata in a compact `PreparseData` byte array that the
  full parser can replay to avoid re-preparsing inner functions.

The PreParser does **not** build AST nodes or emit bytecode.

### The "preparse-twice" pitfall (pre-V8 v6.3)

Before Chrome 63, inner-function variables were re-inferred during full-parse by
re-preparsing nested functions. For deeply nested code this made parse cost
**O(depth × size)** — superlinear. V8 fixed this by serializing variable allocation
decisions into `PreparseData` so inner functions are replayed in O(1).

### PIFE heuristic (Possibly-Invoked Function Expressions)

If the parser sees `(function` or `!function` it **eagerly** full-parses the body,
assuming it is an IIFE. This avoids a guaranteed double-parse cost for immediately-called
closures. Advice to developers: do NOT wrap non-IIFEs in parens to "optimize" them —
it forces eager compilation and wastes startup time.

### Reported speedups

- PreParser is ~2× faster than the full parser, giving a theoretical ceiling of 2×
  speedup for code that is never called.
- Real-world JS benchmarks (optimize-js library, React): ~6 ms improvement on a 24 ms
  parse budget (~25 %), though gains have shrunk as the parser improved.
- Parse + compile is historically 10–30 % of total page-load time on mobile.

### Code cache integration

V8 writes a serialized code cache (including `PreparseData`) to disk after the first
full execution. On repeat loads the cache is validated by script hash, and lazy functions
can be compiled directly from cache without re-preparsing.

---

## 2. SpiderMonkey (JavaScript / Firefox)

**Architecture:** Stencil-based lazy parse with delazification.

### Lazy parse (syntax parse)

Default parse mode produces a _stencil_ — a GC-free intermediate representation
containing function metadata, scope chains, and bytecode for top-level code. Function
bodies are skipped but all early errors are still checked. No live JS objects are
allocated during this phase, making it safe for off-thread use.

### Delazification

When a function is first called its stencil entry is upgraded to full bytecode in-place
(no separate `LazyScript` object needed since Firefox ~95). Delazification can run
off-thread with the stencil architecture.

### Relazification

After GC pressure, bytecode can be dropped and a function reverts to its lazy stencil
state. On next call it is delazified again cheaply from the in-memory stencil.

### Cache integration

Delazification metadata is merged back into the stencil before writing to the bytecode
cache, so warm loads skip both the initial lazy parse and the first-call re-parse.

### Self-hosted code sharing

Stencil allows SpiderMonkey's built-in (self-hosted) JS functions to share their stencil
across content processes — one compile, many instantiations.

---

## 3. JavaScriptCore (JavaScript / Safari / WebKit)

**Architecture:** Hand-written recursive-descent parser with lazy compilation tiers.

- Parser runs in _syntax-only_ mode for inner functions: produces metadata but no
  bytecode until the function is invoked.
- LLInt (Low Level Interpreter) is designed for zero startup cost beyond lexing/parsing.
- Bytecode cache (`.jsc` files) stores pre-compiled bytecode; subsequent loads skip
  parsing entirely.
- No documented PIFE heuristic; JSC relies more heavily on the bytecode cache than
  on preparser tricks.

---

## 4. Roslyn (C# / .NET)

**Architecture:** Full-fidelity incremental parsing with Red-Green Trees.

Roslyn does **not** do lazy function-body parsing per se. Instead it achieves similar
latency wins through:

- **Green tree** (immutable, bottom-up, position-agnostic): rebuilt incrementally on
  edit, reusing ~99.99 % of nodes for typical single-character edits (O(log n)).
- **Red tree** (facade, top-down): fabricated on demand, thrown away on next edit.
  Absolute positions and parent references are computed lazily as you descend — you only
  pay for the subtree you touch.

**Takeaway for Simple:** Roslyn shows that eager full-parse + lazy _semantic work_
(type-check, binding) can be as effective as lazy parsing if the parser is fast and
incremental. The lazy boundary is at the semantic layer, not the syntactic layer.

---

## 5. rustc — Query-Based Demand-Driven Compilation

rustc parses the **entire** source eagerly (one pass), then uses a query system to make
all downstream work demand-driven:
- `type_of(DefId)`, `optimized_mir(DefId)`, `codegen_fn(DefId)` are all lazily computed
  on first access and memoized.
- Incremental compilation reuses query results across rebuilds via a dependency graph.

**There is no lazy parsing in rustc.** The parser is fast enough (single-pass, no
backtracking) that lazy-parsing gains would be marginal. The expensive phases (type
checking, borrow checking, MIR, codegen) are where demand-driven laziness pays off.

**Takeaway for Simple:** If parsing itself is the bottleneck (std-lib import graph),
lazy parsing is the right level. If type-checking is the bottleneck, a query system is
the right answer and may complement lazy parsing.

---

## 6. CPython — .pyc Bytecode Caching (not lazy parsing)

CPython does **not** lazy-parse. It compiles full module source to bytecode on first
import, writes `.pyc` to `__pycache__`, and reuses the cache on subsequent imports
(invalidated by mtime or hash). The cache eliminates re-parsing, not first-parse cost.

**Takeaway for Simple:** `.pyc`-style caching of parsed AST / serialized signatures is
orthogonal to lazy parsing but very high ROI for repeated interpreter starts with a
large std-lib import graph. Both techniques compose well.

---

## 7. Zig — Fast Single-Pass Parser, No Lazy Parsing

Zig's parser is a single-pass, data-oriented recursive-descent parser. It prioritises:
- Cache locality (arena allocators, flat node arrays).
- Error recovery (accumulates errors, continues parsing).
- Compile-time computation at the semantic layer, not the parse layer.

Zig achieves fast startup through raw parser throughput rather than deferral. No lazy
parsing documented or needed at their scale.

---

## 8. Go — Single-Pass, Parallel Per-Package Parsing

Go's parser is similarly single-pass. Startup speed comes from:
- Parallel package compilation.
- Pre-compiled `.a` package archives (analogous to `.pyc`).

No lazy parsing.

---

## 9. esbuild / swc — Bundler-Side, No Lazy Parsing

Both tools parse eagerly because:
- They need the full module graph to perform tree-shaking.
- They are already invoked as build tools (not runtime interpreters), so startup cost
  amortises over the full bundle.
- Parallelism (esbuild in Go, swc in Rust) provides speedup without deferral.

---

## Technique Comparison Table

| Engine/Tool | Technique | What is deferred | Scope still needed? | Cache form |
|---|---|---|---|---|
| V8 | PreParser + lazy compile | AST + bytecode | Yes (PreparseData) | Code cache + PreparseData |
| SpiderMonkey | Stencil lazy parse | Bytecode | Yes (stencil scopes) | Stencil bytecode cache |
| JavaScriptCore | Syntax-only parse | Bytecode | Yes | `.jsc` bytecode file |
| Roslyn | Incremental full-parse | Semantic binding | N/A | Incremental green tree |
| rustc | Eager parse, lazy queries | Type/MIR/codegen | N/A | Query result disk cache |
| CPython | Eager full parse | Re-parse only | N/A | `.pyc` bytecode cache |
| Zig/Go | Single-pass eager | Nothing | N/A | Pre-compiled archives |
| esbuild/swc | Eager full parse | Nothing | N/A | Incremental build cache |

---

## Key Design Pitfalls

1. **Scope / closure analysis cannot be fully deferred.**
   Any variable that might be captured by a nested closure must be heap-allocated (closed
   over) rather than stack-allocated. This decision must be made at pre-parse time by
   scanning variable references in inner bodies. Skipping this leads to incorrect code.

2. **The pre-parse-twice trap.**
   Without serialising pre-parse results (V8's `PreparseData`, SpiderMonkey's stencil),
   each function body must be re-scanned when an outer function is eventually
   full-parsed. For deeply nested code this is O(depth²).

3. **Error reporting is delayed.**
   Syntax errors inside deferred bodies are only reported on first call, not at
   load/import time. This surprises users who expect "parse on import". Mitigate by
   offering an `--strict` / `--check` mode that eagerly parses all bodies.

4. **Re-parse cost when most functions are called.**
   If nearly every function in a module is called on startup (e.g., std-lib
   initialisation code), lazy parsing adds cost (pre-parse + full-parse) vs.
   eager-only (just full-parse). Break-even is around 30–50 % of functions never
   called in a session.

5. **IIFE / top-level init functions.**
   Immediately-executed functions should be eagerly parsed (V8's PIFE heuristic).
   For a line/indent-based language: functions at module scope that are called in the
   same file's top-level block should be treated as hot.

6. **Cache invalidation complexity.**
   Serialised lazy boundaries (PreparseData, stencil) must be invalidated when source
   changes. Source hash is simpler than mtime for content-addressable caches.

---

## Recommendations for Simple (line/indent-based, interpreter, large std-lib)

Simple's startup is dominated by parsing a large std-lib import graph. Recommended
approach:

1. **Parse signatures eagerly, defer bodies.**
   On `use X`, parse all `fn`/`class`/`trait` signatures (name, param types, return
   type) but skip bodies (scan to matching indent level). Store signatures in a
   module-level symbol table.

2. **Serialise scope metadata with each deferred body.**
   Record which outer-scope names each body references so that when it is eventually
   full-parsed, variable allocation is O(1) replay, not O(depth) re-scan.

3. **Add a `.smc` (Simple Module Cache) file.**
   Analogous to `.pyc`. Store: serialised AST or bytecode + scope metadata + content
   hash. Invalidate on hash mismatch. This composes with lazy parsing: the cache stores
   already-full-parsed functions so second startup pays nothing.

4. **Treat top-level call sites as hot (PIFE equivalent).**
   If a function is called at module top-level (outside any `fn` body), eagerly
   full-parse it. Avoid the guaranteed double-parse.

5. **Provide `--eager` / `--check` mode.**
   For CI and tooling, full-parse all bodies immediately so syntax errors are reported
   at import time, not first call.

6. **Lazy-parse boundary is the indent fence.**
   Simple's indentation-based syntax makes it easy to scan to the end of a function
   body: find the next line with indent ≤ fn-header indent. No bracket counting needed
   — a significant simplification vs. JS preparsers.

7. **Query-system for type checking.**
   If type inference becomes a bottleneck, add a rustc-style query layer on top of the
   lazy parser rather than eager type-checking all imported signatures.

---

## Sources

- V8 preparser blog: https://v8.dev/blog/preparser
- V8 scanner blog: https://v8.dev/blog/scanner
- SpiderMonkey Newsletter 10 (stencil): https://spidermonkey.dev/blog/2021/04/22/newsletter-10.html
- SpiderMonkey Newsletter 96-97: https://spidermonkey.dev/blog/2022/01/14/newsletter-firefox-96-97.html
- JSC bytecode internals: https://zon8.re/posts/jsc-internals-part1-tracing-js-source-to-bytecode/
- Roslyn Red-Green Trees: https://learn.microsoft.com/en-us/archive/blogs/ericlippert/persistence-facades-and-roslyns-red-green-trees
- rustc query system: https://rustc-dev-guide.rust-lang.org/query.html
- Zig parser: https://mitchellh.com/zig/parser
- esbuild FAQ: https://esbuild.github.io/faq/
- Addy Osmani JS startup perf: https://medium.com/reloading/javascript-start-up-performance-69200f43b201
