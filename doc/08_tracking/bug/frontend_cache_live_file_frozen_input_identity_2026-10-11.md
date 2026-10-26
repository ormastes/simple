# Frontend cache key does not bind the exact parser input

Status: PHASE1_SEMANTIC_OBSERVATIONS_PROVENANCE_BLOCKED.
No native miscompile has been demonstrated. Astra review identified coordinated
adoption requirements; this report is not pure-Simple or Phase3 admission.

The driver freezes source content before phase2 parsing. The frontend can also
preprocess conditional, domain or advisory source before parsing. Nevertheless,
`src/compiler/10.frontend/frontend.spl` obtains its parse-cache key from
`frontend_parse_cache_key(file_path)`, which hashes the current disk file.
The restored flat pools are then bridged using the supplied parser-input text.
Those two generations can differ. A live B/frozen A request can look up B's AST,
or store A's pools under B's physical-file hash after a miss.

Repair proposal: key by the exact parser input with a new namespace, retaining
compiler scope, codec and advisory-policy validation. Hash the input first,
then domain-separate that fixed-size digest, avoiding a source-sized temporary
concatenation. Disabled caches must still avoid hashing. Do not introduce a
global mutable AST map or relax TLDR archive/source authority validation.

Actual-owner regression requirements:

- Prime valid B at a path, parse supplied A with B still on disk, and inspect
  actual parsed declarations/imports. Test the converse generation separately.
- Prime valid B, supply malformed A, and require parser diagnostics rather than
  a restored valid B module. Frozen valid input remains separate from a changed,
  malformed disk file; the caller must enforce snapshot freshness independently.
- Verify unchanged exact input can reuse the production cache across the typed
  closure probe and phase2 only under identical scope/advisory/feedback policy.
- Exercise the real driver freeze-to-parse boundary and retain one coherent
  generation or an explicit rejection. No mixed-generation output is acceptable.

Performance/memory qualification must account for intentional old-cache misses,
O(n) input hashing, maximum RSS and source/diagnostic lifetime. This repair does
not establish 0.1-second compilation or solve header-only batch wiring.

Evidence and private proposals:
`build/native_probe/tldr-driver-batch-wiring-review-20261011-sol/`.
No shared frontend source application, native compiler build or remote landing
has occurred for this bug. Bug DB reconciliation is pending a qualified DB runner.

## Actual-owner Phase1 reproduction and candidate checks

The new focused bootstrap diagnostic completed once with unchanged pinned inputs,
four authenticated closed process jobs and no pinned-input postflight errors. The
frontend/cache/parser owners reproduced wrong-generation AST reuse and syntax
error suppression on the baseline. The isolated exact-input candidate passed
both AST/key/reuse and real syntax-error/nonstore predicates. It remains a
hypothetical key namespace, not a completed cross-phase production migration.

Request SHA256:
`4a6f20aad374caac398deea32e1a9d0282fbafe567b019ed8ffb1da684c34e65`.
Results: `exact-input-phase1-closure3/result.json` in the evidence directory.
113 frozen current source owners, 2.15 MiB per lane; immutable 6b133a Rust seed
interpreted actual Simple code. Four collector attempts, two baseline red
reproductions, two candidate green predicates, 96.490709 seconds overall.
Peak sampled RSS: baseline AST490512/candidate AST495244 KiB;
baseline syntax490452/candidate syntax492420 KiB. These different semantic
workloads and single samples are not comparative performance/memory admission.
No green replay, native executable output or pure-Simple qualification occurred.

Post-run log review found missing-export `[use-warning]` messages, ambient library
reads outside the frozen snapshot and a SHA module-resolution warning. The
controller did not reject those warning strings. Preserve its terminal result as
raw evidence, but do not treat `DIAGNOSTIC_EXPECTATIONS_MET` as coherent owner
execution or repair admission. The four semantic outcomes remain observations;
source provenance and provider completeness are BLOCKED. No production adoption
or performance qualification follows. A separate observed-admission correction
must retain the original result and logs; do not overwrite them or rerun green
semantic checks to obtain better-looking evidence.

## Astra integration finding

The standalone key switch is not ready for production application.
`src/compiler/80.driver/cache/phase_compatibility_admission.spl` validates `.fpc`
filenames against the physical source hash and imports entries under that key.
Switching only the frontend would reject new exact-input entries during phase
admission and leave imported old entries unreachable. This is fail-closed for
correctness, but regresses Phase2-to-Phase3 cache reuse beyond a one-time cold
invalidation. Reconcile versioned parser-input identity with the authenticated
cache subject/admission contract, and test actual cross-phase reuse before
adopting the patch. Do not weaken source authority to obtain cache hits.

Nested hashing avoids the extra source-prefix concatenation, but the current
`sha256_text` implementation still allocates a source-sized UTF8 buffer. Peak
memory improvement must be measured; source review alone cannot claim O(1)
auxiliary memory or a compiler speedup.
