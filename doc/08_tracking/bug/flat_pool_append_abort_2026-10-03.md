# Flat-pool append abort: retained evidence and missing failure context

Status: root cause unresolved; fatal diagnostic improvement prepared, native
regression UNRUN. This change neither repairs nor suppresses the append failure.

Ubuntu source `43f626850b6a5531e89110f75cd1eaedc24adcd1`, producer
`e58968bba401407bb04d6b581e62cf1dcf480847ec56338bb7a06ad4003283ff`, runtime archive
`161984579a45eef602be1fb6f9a683ef5a9f2f664fe77dd5708116730d2a2860` aborts with exit
134 and only `flat pool encoder string builder append failed`. The retained
catalog is `D:/dev/ubuntu43f-failure-catalog-20261003/evidence.json`:

| Attempt | Entry | Last parse source | Peak RSS KiB |
| --- | --- | --- | ---: |
| U43F-001 | bootstrap_main | src/lib/sys/pty.spl, 670/1125 | 1860856 |
| U43F-010 | compiler/99.loader | src/lib/sys/pty.spl, 661/1039 | 1833520 |
| U43F-020 | full CLI | src/app/devhub/auth.spl, 675/2573 | 2318268 |

These are actual LLVM-target compilation attempts, complete/quiescent under
monitor-only unlimited RSS policy. A last-progress source is not a per-file
grammar diagnosis. No stack or failed argument value was retained.

Read-only ELF inspection proves that the caller passes a preserved raw builder
handle and one boxed text word to the linked Rust provider, then compares its
return with 1. New/push/finish all resolve to that provider; the escape calls
resolve to `rt_contains` and `rt_string_replace`. The nearby `rt_pool_safepoint`
implements task-pool scheduling, not collector reclamation. This evidence does
not establish a shared ownership bug or an ABI arity defect.

Disassembly evidence under `D:/dev/flat-pool-e589-abi-review-20261003`:

- `caller-builder-disassembly.txt`: SHA256
  `ec870c3d0ca0d8c766fd4b38132933f55433d2c57a667b533f13771b346556a1`.
- `provider-builder-disassembly.txt`: SHA256
  `f39e925f8aa032dd30d11f8900cd3eec565961e712de8dc5c72e12dd3bd70060`.

The patch preserves the fatal check and canonical bytes. On failure only, it
reports encoder site, local element index, original input's validated runtime
length, and provider return. Count fields use item -1. Nested indexes are local
to the innermost pool, not a complete pool path. Length -1 identifies a rejected
original text value. Nonnegative length does not prove the handle is bad:
lowering may transform the input, or its copy may fail. No invalid value or raw
handle is interpolated. Success adds scalar context arguments and index
increments; no diagnostic strings or extra validation are built on success.
Runtime/performance acceptance remains pending.

At the pinned source boundary, runtime `collections.rs::rt_string_len` returns
-1 when `heap.rs::get_typed_ptr` rejects a non-String RuntimeValue, including
NIL. Seed `boxed_text_arg_indices` selects only builder push, not string length.
`rt_array_get_text` delegates to the bounds-checked array accessor; seed's
`compile_inline_array_get_word` also returns its NIL word for an empty array.
These source contracts support the negative fixture. They do not substitute
for checking the new compiled `Any` call boundary: native qualification must
confirm that the original word reaches string length without an intervening
conversion and that the fixture's absent element remains NIL.

## Separate attributable allocation issue

Seed `codegen/instr/calls.rs::boxed_text_arg_indices` selects every
`rt_string_builder_push` call. `box_text_args` unconditionally calls
`rt_string_data`, `rt_string_len`, then `rt_string_new` before append. The emitted
e589 wrapper at 0x562c03 confirms that copy. For long valid text this creates an
additional full-sized runtime string before the builder copies its bytes,
retaining avoidable scratch until its owner ends. No timing improvement or
causal link to the abort has been measured. Removing or replacing that boxing
requires its own valid/raw/malformed-text ABI and allocation regression; this
diagnostic patch does not alter it.

Next evidence: run the changed native negative fixture plus all canonical
encoder cases once with a pinned source-consistent producer when reserved.
Only then consider a bounded changed mini reproducing the parse/cache path;
do not repeat the unchanged full-CLI failure or disable the cache/check.
