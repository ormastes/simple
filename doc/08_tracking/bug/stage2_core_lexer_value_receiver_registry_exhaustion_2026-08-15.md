# Stage 2 CoreLexer value-receiver registry exhaustion (2026-08-15)

Status: fixed-cap containment patch applied; both focused C authorities pass;
Stage-2 runtime/compiler admission passed. A correctly routed pure-Simple
Stage-3 verification remains pending. Lifetime retention remains open.

## Failure

The admitted Stage-2 compiler reached the parser in two independent builds and
then exited with `SIGSEGV`:

- Phase-2 test runner: parse 192/592, 41.28 s, max RSS 1,295,672 KiB.
- direct LLVM Stage 3 diagnostic: parse 64/604, 42.15 s, max RSS 1,390,452 KiB.

The test-runner fault resolves to
`compiler__frontend__core__lexer_struct__CoreLexer.peek_next+0x36`. Generated
code calls `rt_struct_alloc(0x88)` to copy the 17-field lexer for a plain value
receiver, receives null, and immediately stores through that null pointer. The
failure is consistent with exhaustion of the fixed core-C struct allocation
registry; the host still had about 62 GiB available and the process limit was
unlimited, so it is not host memory exhaustion. A live registry count was not
captured, so the narrower allocation/registry failure remains the proven fact.

Retained evidence:

- `build/phase2-qualification/logs/test-runner-build-fb3a882a.log`
- `build/phase2-qualification/logs/test-runner-build-fb3a882a.status`
- `build/phase2-qualification/logs/test-runner-build-fb3a882a.time`
- `build/phase2-qualification/logs/test-runner-progress-fb3a882a.events`
- `build/phase3-parallel/stage3-controller.log`
- `build/phase3-parallel/stage3-build.status`
- `build/phase3-parallel/stage3-build.time`
- `build/phase3-parallel/bootstrap-build-progress.events`

## Root cause and bounded fix

Pure-Simple MIR lowering copies a value-struct receiver for each plain instance
`fn`. Fourteen transitively hot, read-only `CoreLexer` methods were plain
receivers, so parsing a compiler-sized closure consumed millions of 136-byte
temporary structs. Convert only that hot read-only closure to `me` receivers:
`at_end`, `peek`, `peek_next`, `peek_at`, `char_at_pos`, `word_boundary_at`,
`measure_indent_from`, `skip_indent_from`, `line_starts_binary_op`,
`leading_op_continues`, `char_slice`, `fs_nested_string_may_open`,
`fs_expr_has_word`, and `fs_expr_ends_with_word`.

The four token getters remain unchanged because their external wrappers accept
an immutable/by-value lexer and they are not on the canonical parse hot path.

## Successor failure in the value handoff

The lexer-method fix rebuilt and admitted Stage 2 as SHA
`b37de3b5a8df28db04d8e1fd0f40d081d6727b389c5812e352492583a8527fad`.
Disassembly proved zero `rt_struct_alloc` calls in all ten surviving converted
method symbols; four small methods were optimized into callers. The isolated
runner nevertheless exited 139 at parse 0/592. Its instruction pointer
resolved to the free function `lexer.spl::lex_next+0x81`, immediately after another unchecked
`rt_struct_alloc(0x88)`.

The remaining hot wrapper copied `current_core_lexer` into a local and passed
that local through `core_lexer_next_token(CoreLexer)`. The admitted binary
contains three unconditional 136-byte allocations in that local/tuple handoff,
plus a fourth entering the unconditional by-value `current_core_lexer_save`.
The second bounded fix makes `lex_next` call the existing `me next_token` or
`me next_token_after_generic_close` directly on the module-owned mutable lexer,
reads token state from that owner, and performs the by-value environment save
only when the optional environment mirroring mode is enabled.

Retained successor evidence:

- `build/phase2-qualification/logs/test-runner-build-b37de3b5.log`
- `build/phase2-qualification/logs/test-runner-build-b37de3b5.status`
- `build/phase2-qualification/logs/test-runner-build-b37de3b5.time`
- `build/phase2-qualification/logs/test-runner-progress-b37de3b5.events`
- `build/phase3-parallel-corelexer/stage3-controller.log`
- `build/phase3-parallel-corelexer/stage3-build.status`
- `build/phase3-parallel-corelexer/stage3-build.time`

## Third bounded owner: speculative snapshot lifecycle

The direct-owner rebuild admitted Stage 2 as SHA
`7dee33dc3747399058e3c6544a6e64a71a2389d66d1a65e80c258361097f0e3a`
(4 compiled, 842 cached, 0 failed; seed reused and Cargo disabled). Its
`lex_next` and ten surviving converted `CoreLexer` symbols contain zero direct
`rt_struct_alloc` calls. The Phase-2 runner then parsed 592/592 files and
907/907 modules with zero failures before `rt_struct_alloc(0x20)` returned
null in `HirLowering.lower_hir_expr`; the next instruction wrote through the
null result. It exited 139 after 7m05.29s at 3,400,892 KiB RSS. No runner
candidate or focused test result exists.

Two no-host-GPU Stage-3 builds converged at parse 512/604 with exit 139 and
about 4,255,000 KiB RSS. The exact Stage-3 null-return caller is not captured,
but the core-C struct registry ceiling is 4,194,304 live entries and generated
struct temporaries are not unregistered.

Admitted-binary disassembly identified the remaining hot ownership burst in
the speculative lexer snapshot lifecycle: save+commit registered four
structs, while save+rollback registered six. The common
`try_parse_contract_stmt` path also allocated a snapshot for every ordinary
statement and leaked it on unrecognized and successful clauses.

The third bounded fix:

- reads and restores the module-owned `CoreLexer` directly;
- makes `LexSnapshot` commit/rollback alias-receiver operations;
- changes all 16 snapshot owners and 34 terminal calls across the three parser
  consumers to the alias lifecycle;
- allocates no lexer snapshot for an unrecognized ordinary statement; and
- commits both successful contract-clause paths exactly once.

Retained evidence:

- `build/phase2-qualification/logs/test-runner-build-nogpu-parallel.{log,status,time}`
- `build/phase2-qualification/logs/test-runner-progress-nogpu-parallel.events`
- `build/phase3-no-gpu-parallel/`

## Verification gate

The snapshot-lifecycle rebuild admitted Stage 2 as SHA
`286322313919ef7a37d08af8b64ac9c369effbc026e71f33744ca857e7847d5c`.
The next and latest retained Stage-3 run completed parse 604/604 files and
868/868 modules, then exited 139 before the next progress phase at 4,223,084
KiB max RSS. No core or current instruction pointer was retained, so registry
exhaustion in that latest run is a strong inference, not a proven current
caller. The older `HirLowering.lower_hir_expr` null-return/store-through-null
trace above remains the exact proven allocation failure.

## Fixed-cap containment (not lifetime resolution)

Both `runtime_memory.c` and `runtime_native.c` now:

- remove the arbitrary `1 << 22` capacity;
- grow only after an overflow-checked `SIZE_MAX / sizeof(entry)` calculation;
- compute the 70% threshold without overflowing multiplication or addition;
- bound every struct-registry probe and reuse a tombstone after a full scan;
- compact tombstones before unnecessary growth;
- roll a failed rehash transaction back to the complete old table;
- count allocation/registry failures internally and expose len/cap/failure
  accessors only under `SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING`;
- allocate one aligned word for a valid zero-field struct in both authorities;
  and
- reject receiver tags 2 through 7 before pointer masking in both authorities.

The bounded C regressions allocate 384 simultaneous registered structures,
crossing the initial table threshold without a four-million-iteration test.
Both runtime-authority tests compiled and ran successfully with test-only
telemetry enabled. The rebuilt canonical Stage 2 compiled 846 modules with zero
failures and admitted SHA-256
`3d599846e04f954f0e0c518b7314e1263e24a8858a7cb8663b8ea25044f4b556`;
sanity and receiver evidence passed.

This is containment. The older exact null result and latest correctly routed
pre-containment Stage-3 failure indicate retained ownership still grows across
compiler work. The first post-containment diagnostic accidentally delegated to
the Rust FFI because `--compile-stack-mib 64` was misparsed; its 29 GiB timeout
is excluded from this bug's pure-Simple evidence. The next correctly routed run
must measure the
test-only len/cap/failure counters at parse/HIR boundaries and inspect
`ModuleSurface` promotion, retained `default_methods`, and retained enum
`variants`. Do not call the retention leak fixed merely because a larger table
allows Stage 3 to advance.

Static inspection confirms that `module_surface_from_module` retains every
enum's original `[Variant]`, `module_surface_trait_from_trait` retains complete
`ParserFunction` nodes for non-empty trait default bodies, and
`module_surface_promote(surface)` promotes the entire graph before the
per-source transient scope ends. Those fields are intentional semantic
exceptions, so this is a bounded owner hypothesis rather than permission to
drop them. Measure their promoted graph/cardinality separately before changing
the surface contract.

Generated allocation results also remain unchecked before stores; that
independent fail-closed requirement is tracked in
`native_struct_allocation_failure_unchecked_codegen_2026-08-15.md`.

## Remaining verification gate

1. Refresh and verify the frozen manifest for the routing/recovery additions.
2. Rebuild the owning Stage-2 artifact once; do not rebuild only for a hash
   difference.
3. Retry direct LLVM Stage 3 once and record registry telemetry at parse/HIR
   boundaries, exact first failure or candidate hash, elapsed time, and RSS.

Do not treat a compiler hash difference as a failure and do not bypass source,
runtime, manifest, or tool-authority mismatches.
