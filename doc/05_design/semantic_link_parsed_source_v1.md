# B2 parsed-source semantic resolver, first staged producer

Status: CODED / UNRUN. This implements a bounded next B2 step; full B2 and lane06 are not complete. The selected all-kind/signature, interval ranking, ast-link from-line/resolve CLI and downstream Markdown consumers remain required.

## Existing work reused

Authoritative selected contract: `/home/yoon/dev/robust-tdd-20261014/robust-revised-plan.md`, lane06, and original research section 5.2 of `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`.

Retained branch `work/robust-tdd-06_semantic_docs-20261014` at `a49397d66898f01a40cf9d87ec6f2f6a5fdc0064` adds B1 acceptance documentation/specs. Its stable_id.spl and index.spl are byte-identical to the feature tree. Retained untracked tooling/semantic_link.spl supplied reusable strict short-name parsing and name+fingerprint binding rules, adapted with attribution. Its metadata-list index and semantic_link_spans.spl do not establish parsed source or revision authority and are not adopted as proof. Other named retained semantic branches concern HIR budgeting, portable cache verification and facet indexing; none is substituted for B1 document identity.

The current CompilerQueryContext delegates parse_source/build_symbol_table to foreign io.rt_* query APIs. CLI query_outline performs line scanning. This pure-Simple producer instead reuses `compiler.core.parser.parse_module_silent_checked`, `module_decl_at` and existing declaration/type/span accessors. No AST/HIR schema or parser owner changes. The checked parser returns failure directly because a subsequent cross-module parser_has_errors call is known to lose its flag.

## Contract and scope

REQ-MC-008/B2-URI: short `spl:fn@module.path.name~0123456789ab` and package-qualified `spl://package/module.path#fn:name~0123456789ab`. The original package/fragment grammar and B1's existing 12 lowercase hex encoding are preserved. Formatters re-admit their output through the shared URI parser and refuse oversized results; configured package/module fields are individually capped at 4096 bytes. No withdrawn 32hex path syntax, percent decoding, query revision, whitespace trimming, or illustrative base32 acceptance. ASCII identifiers/dotted names are currently admitted; unknown syntax/kinds are typed refusals.

B2-SOURCE: `open_semantic_link_document_v1(package,module,file,revision)` takes configured namespace routing, a real file and its expected 64-hex SHA256 content revision. It never accepts caller-declared symbols/spans as proof. It reads the exact revision through existing strict UTF8 bounded regular/no-follow I/O, parses it, copies declaration facts and resolves primitive type tags before deriving B1 IDs. No arena node/span/type handles escape. Any conditional preprocessor transformation receives UnsupportedSourceTransform until an original-source map exists. Flat declaration spans use codepoint offsets: all spans are converted through existing lex_source_byte_offset while the original lexer remains live, then copied as UTF8 byte offsets before header validation resets lexer state. All construction occurs serially; the core parser is global-state owned and this leaf is not a concurrent LSP adapter.

This stage admits top-level fn declarations with explicit builtin primitive parameter and return types and no generics. A strict existing-lexer header check proves the written primitive spellings, arity and return match the copied flat facts; richer/defaulted headers refuse until supported. This prevents nonstandard widths such as u7, which the core parser collapses to TYPE_I64, acquiring an i64 identity. It does not claim whole-module name/type checking. Unsupported/inferred/named/generic signatures return UnsupportedSignature instead of hashing guessed source spellings. Non-function declarations are not indexed; resolving other known URI kinds returns UnsupportedKind. Extending signature kinds requires an actual resolved-signature producer, not relaxed checks.

B2-IDENTITY: copied facts feed existing build_symbol_index and stable_symbol_id without schema changes. Duplicate declaration locations claiming one full identity are ambiguous, despite B1's intentionally idempotent duplicate-input policy. Different same-name signatures keep distinct IDs; a supplied matching fingerprint disambiguates. Matching fingerprint under a different name/module never retargets. Prefix collision is mapped to FingerprintCollision. The collision-check API uses B1's retained short-length test seam over actual parsed declarations, publishes no alternate index, and cannot change production's fixed 12-character policy.

B2-REVISION: source is checked before parsing and reread after parsing before publication. Resolver checks requested revision equals snapshot revision and rehashes the current bounded file before lookup. Changed bytes, including body-only changes, refuse an old snapshot. A rebuilt snapshot may retain stable identity but has fresh spans. Deletion/read refusal does not become an empty index or stale success. A returned location is for the checked content revision; it makes no promise that disk cannot change after return. Package-qualified URI authority must equal configured source package. Package/module configuration is supplied by the owning caller; this leaf does not authenticate a package registry or infer package routing from a filename.

## Ownership, cost, and limits

Each document owns copied scalar/string facts, one B1 index and per-name row arrays. There is no global document cache, AST retention, shell-out or per-request parse. Requests perform one bounded file read+SHA until an admitted revision-watcher owner can substitute stronger freshness without rereading. This is O(source bytes + same-name candidate count); parser and index construction occur once per published snapshot, bounded at 1MiB source and 4096 top-level declarations. The 4096 check is a snapshot publication limit, not a parser allocation limit. Core parser allocation growth is inherited and unmeasured; 1MiB input is finite but no fixed peak-RSS claim is made.

The actual I/O provider checks handle type/size before allocating and bounds growth to max_bytes+1 while reading. Its byte result is strictly decoded to UTF8. This is not a post-read whole-file length filter. Existing source: runtime_native.c rt_read_regular_no_follow_buffer and rt_file_read_regular_no_follow_bounded_bytes; the Simple facade supplies max_bytes=1048576. Runtime provider behavior remains unqualified until root executes the admitted runner.

Snapshots are owned in-process objects, not signed capabilities against a malicious caller constructing or mutating arbitrary instances. A caller must use the producer and preserve ownership. No public builder accepts externally supplied declaration arrays. An eventual cross-process protocol must add its actual authority/publication adapter; an object-shaped payload alone is never that authority.

## Verification and handoff

23 real-file/public API scenarios cover checked parse→B1 ID/index→short+package URI→resolution; expected ID parity; revisions before indexing and after publication; wrong package; unchanged identity/moved spans; stale signatures; no retargeting; duplicate IDs; overload disambiguation; deterministic prefix collision via the B1 seam; arena replacement; parser failure; unsupported signature/kind; URI negatives; provider size bound; deleted source.

The tests do not inject fake I/O, pretend metadata is parsed source, or claim measured concurrent-race timing. The publication recheck covers an actual edit during parsing in source; deterministic tests cover stale bytes before loading and after publication. A true overlapping writer schedule remains execution work. Baseline product module was absent: source-predicted RED is missing API/discovery, not a claimed observed failing test body. All tests, docgen, timings, RSS, leak/resource counters and MCP/native smoke are UNRUN pending a qualified runner. No runtime PASS or full B2 completion claim.

## Independent review corrections (cycle 2)

Preserved cycle1 packet and HOLD receipt under revision1. Four source findings are repaired locally: transformed-source offsets now refuse, codepoint spans map through the lexer before any reset, exact header token/type agreement rejects collapsed integer annotations, and formatters cannot emit oversized successful URIs. Five added actual-file scenarios cover those defects plus deliberate richer-header refusal. No additional declaration kinds, CLI work, parser/schema edits or runtime launches were added after the root Phase3 priority freeze.

## C4 indexed batch error receipt

`SemanticLinkBatchErrorV1(row,error)` carries the exact zero-based input URI
index for lookup failure, or -1 for common admission/revision failure. New
indexed source/file batch entrypoints retain the actual single parse plus final
revision check. Existing APIs delegate and keep their original error type.
No per-URI reparse or new identity derivation is introduced.
