# Lexer ASCII span cache must retain UTF-8 byte units

Status: fix-implemented-verification-pending. Runtime, native replay and docgen NOT_RUN. This is an independently complete source slice, not completion or supersession of PR7500.

## Provenance and original failure

PR7500 head95156319e2a68c8c6832ecda2551e994281e0717 (fork4eb1de2ecbdb286b539e1d7f76e8e47ff4fcced1) adds an ASCII span shortcut and its cached state. Fable/Opus review correctly blocks its text `source.len() == char_count` decision: when text length becomes code-point count, it is true for multibyte input. The original prevention oracle also uses `c.len()`, so it can agree with the same wrong units. The existing slow-path character-width accumulation has the same migration hazard.

This extraction starts from releaseb37cca889050455644210376e8a9706cd617f0e5. Its lexer preimage is byte-identical to the original PR fork's lexer. Preserve the entire original cache addition: module slot, lazy decision, early ASCII return, initialization reset, LexerState field, take capture/reset, and install restore. Correct byte units in both production decision and slow-path accumulation using already-exported `std.common.string_core.str_len`, which delegates to the existing byte-length runtime owner. No new FFI, method lowering, Rust change or provider is introduced.

## Reproducer and similar-scenario controls

The original three actual lexer token-span reconstruction cases remain: ASCII, multibyte literal/comment text, and alternating source initialization. The oracle prefix and EOF bound now count bytes explicitly. Two added cases pin literal UTF-8 prefix `[0,1,3,6,10]` for `aé中😀`, ASCII and empty prefixes, and call the exported production byte-offset owner directly. They cover forward offsets, backward reset, upper clamp, source replacement, and state take/install between mixed-width and ASCII sources. Fixed numeric expectations prevent production and oracle from drifting together. These are authored controls, not executed failure/pass evidence.

## Scope and remaining PR7500 blockers

Exactly four paths belong to this slice: lexer owner, its existing prevention spec, mirrored manual, and this scoped note. None of the original Rust or RSS-script files is included. Original author branch remains untouched; attribution and original source provenance are retained.

PR7500 remains OPEN with independent blockers: the non-Unix sampler can observe a mixed pointer/length pair and render beyond an allocation; its shutdown does not prove thread quiescence. The RSS budget script's measure_peak discards child exit status, allowing a child that crashes after sufficient RSS to be treated as success. This extraction repairs neither issue. It makes no RSS, speed, memory-floor, full-PR or full-qualification PASS claim.

## Finite verification admission

After an admitted exact-source full runtime exists, run the five-case spec once under the campaign canonical tree watchdog with120second outer cap and one native slot. Require nonzero discovery, all assertions, and valid lifecycle/source/provider receipts. Source-matched native lexer replay is a separate pending criterion; no Rust-seed substitute or old-budget reset. Validate the mirrored manual using admitted spipe-docgen and require0stubs. No compiler or test was run while preparing this source slice.

Provider token/accounting evidence: unavailable for this source-only preparation; no comparable execution cohort or ratio is claimed.
