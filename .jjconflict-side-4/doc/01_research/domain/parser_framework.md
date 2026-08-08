<!-- codex-research -->
# Parser Framework — Domain Research

**Date:** 2026-07-31

## Source and syntax representation

- LLVM's [`StringRef`](https://llvm.org/doxygen/classllvm_1_1StringRef.html), Clang [`SourceLocation`](https://clang.llvm.org/doxygen/classclang_1_1SourceLocation.html), and rustc [`SourceMap`](https://doc.rust-lang.org/stable/nightly-rustc/rustc_span/source_map/index.html) support one owner-held source buffer with non-owning byte spans and lazy line/column lookup. Span consumers must not outlive the snapshot.
- rustc uses compact spans and 32-bit interned symbols, but explicitly separates session-local symbol identity from stable hashing ([`Span`](https://doc.rust-lang.org/stable/nightly-rustc/rustc_span/struct.Span.html), [`Symbol`](https://doc.rust-lang.org/beta/nightly-rustc/rustc_span/symbol/struct.Symbol.html), [stable hashing](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_data_structures/stable_hasher/)). Parser hashes therefore must serialize semantic text/shape, not arena or interner allocation IDs.
- Dense IDs enable arrays instead of maps in rustc HIR ([rustc HIR](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_hir/index.html)). Flat ASTs improve locality; SoA is most useful when passes touch only selected columns ([Flat ASTs](https://www.cs.cornell.edu/~asampson/blog/flattening.html), [Ori flat AST](https://ori-lang.com/docs/compiler-design/02-intermediate-representation/flat-ast/)).
- rust-analyzer and Roslyn show the stronger alternative: immutable lossless trees with structural sharing and red/AST views ([rust-analyzer syntax](https://rust-analyzer.github.io/book/contributing/syntax.html), [Roslyn syntax](https://learn.microsoft.com/en-us/dotnet/csharp/roslyn-sdk/get-started/syntax-analysis)). That machinery pays off for editor-grade round-tripping but is not required merely to remove copied tokens.

## Determinism

Tree-sitter specifies deterministic lexical tie-breaks and preserves explicit error/missing nodes ([grammar](https://tree-sitter.github.io/tree-sitter/creating-parsers/3-writing-the-grammar.html), [syntax queries](https://tree-sitter.github.io/tree-sitter/using-parsers/queries/1-syntax.html)). LLVM's deterministic-build guidance warns against observable hash-table or thread-completion order ([LLVM deterministic builds](https://blog.llvm.org/2019/11/deterministic-builds-with-clang-and-lld.html)). Observable parser output should commit by source order and stable tie-break key; diagnostics should sort by `(start, end, code, local_ordinal)`.

## SIMD structural indexes

simdjson separates byte classification/UTF validation from branchier parsing and writes ordered structural positions consumed by stage 2 ([paper](https://arxiv.org/abs/1902.08318), [staged parsing](https://simdjson.github.io/simdjson/md_doc_2parse__many.html)). Mison and Pison show the locality benefit and the hard cases when partitions split escapes, strings, nesting, UTF, or CRLF ([Mison](https://www.microsoft.com/en-us/research/publication/mison-fast-json-parser-data-analytics/), [Pison](https://www.vldb.org/pvldb/vol14/p694-zhao.pdf)). A structural index is not a parse result; it must retain cross-block state and prove scalar token/diagnostic parity at adversarial boundaries.

## Parallel/GPU lexing

ParPaRaw partitions bytes, computes each chunk's finite-state transition for every possible entry state, composes those functions with a prefix scan, and then assigns ordered output ranges ([ParPaRaw](https://www.vldb.org/pvldb/vol13/p616-stehle.pdf)). Exact integer prefix scans support deterministic count/scan/emit; stable compaction preserves source order ([CUB DeviceScan](https://nvidia.github.io/cccl/unstable/cub/api/structcub_1_1DeviceScan.html), [Thrust stable `copy_if`](https://nvidia.github.io/cccl/thrust/api/function_group__stream__compaction_1ga5ef681b2c51c35aa4e93fe9ad5e948c5.html)).

The limits are material: lexical state cardinality can explode; nested grammar is not finite-state; transfers and launch overhead dominate small inputs. Requirements should bound summary states, overflow-check counts before allocation, forbid atomic append, retain scalar fallback, and benchmark end-to-end transfer/launch/RSS separately from device throughput.

## Incremental parsing

Lezer reuses change-adjusted tree fragments and warns that untracked lookbehind or broad tokenizer context can invalidate reuse ([reference](https://lezer.codemirror.net/docs/ref/), [guide](https://lezer.codemirror.net/docs/guide/)). Tree-sitter requires editing the prior tree before parsing the new document ([Parser API](https://tree-sitter.github.io/node-tree-sitter/classes/Parser.html)). Immutable green trees make subtree replacement proportional to tree depth, but rust-analyzer still treats full syntax trees as semi-transient to control memory ([rust-analyzer guide](https://rust-analyzer.github.io/book/contributing/guide.html)).

Incremental acceptance must bind reused regions to lexical/grammar context, expose changed ranges and old→new identity mappings, and compare the full ordered result with a clean full reparse after every edit class. Reuse ratio is evidence, not correctness.

## Option implications

The minimum defensible baseline is one immutable UTF-8 snapshot, half-open byte spans, identifier-only interning, typed integer node IDs, bounded arena lifetime, explicit output ordering, and scalar parity. Immediate lossless green trees or wholesale new arena infrastructure are optional; SIMD/GPU execution is safe only after the representation and determinism gates pass.
