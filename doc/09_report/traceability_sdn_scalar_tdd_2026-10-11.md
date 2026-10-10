# Traceability SDN scalar TDD increment

STATUS: WARN — scalar component repair verified; full product and runtime qualification remain open.

The owned product lane is `/home/yoon/dev/simple-traceability-product-20261011`, branch `work/traceability-product-20261011`, based on compiler prerequisite PR #2955 at `39a4cfbf06564a66cb7467dfa48976a5d0946aff`. Original worktrees are preserved. The full user-selected 20 REQ-TRC / 40 AC-TRC / WP0–WP7 scope is unchanged.

## Production change

The shared SDN parser validates the complete quoted scalar before unescaping it, rejecting missing unescaped terminators and trailing content. It uses the existing checked negative-accumulation converter for signed integers, preventing saturation/wrapping while retaining exact signed limits. Escape decoding remains under the existing shared owner; unknown escapes and raw multiline compatibility are inspected, not claimed as executed coverage.

## Actual evidence

- Reliable quoted-scalar RED: 2 examples, 2 failures; GREEN: 3 examples, 0 failures, including escaped quotes/backslashes, Unicode and empty text.
- Reliable integer-overflow RED: 3 examples, 3 failures; GREEN: 4 examples, 0 failures, including both exact signed limits.
- Astra high-effort local source review: PASS for this narrow repair, P0=0, P1=0. No authenticated admission.
- Working direct-env runtime guard: PASS. No green spec was rerun unchanged.
- Machine evidence and source/binary/log digests: `traceability_sdn_scalar_tdd_2026-10-11.sdn`.

Initial fail-only rejection results were falsely green and are explicitly INVALIDATED. An independent control confirms native `fail(...)` does not reject direct/helper cases, while built-in unequal matchers do. See `../08_tracking/bug/phase2_native_sspec_fail_ignored_2026-10-11.md`. Test process exit zero is not used as the verdict. Rust was used only to construct the native pure-Simple capsules.

## Remaining work

The legacy inline array/dictionary/table parser still recovers scalar errors into strings, and lacks full consumption/duplicate validation. This scalar repair does not establish strict whole-document rejection or complete AC001/AC002. Typed qualification/family adapters, multi-table encoding and reference closure, production CLI migration, extraction/resolution, evidence runner and authorization, snapshot admission, projections/migration, Slop and HTML remain open.

The four shared-value baseline examples produced a reported pass after exact payload assertions, but fail-only unexpected-variant branches require strengthening before qualification. No branch-coverage target, generated-manual review, seven-score maintenance, broad compiler/lib/MCP/LSP checks or product-release admission is claimed. A general-purpose qualified runtime remains unavailable in this lane. Compiler prerequisite PR #2955 was merged into release/1.0 at 1bdffb92d6cb646fef19c27349fe27b2b7c2f8bb. This scalar-only submission is prepared separately on fix/sdn-scalar-validation-release-20261011 at release base 3bb214c30fe; the unfinished strict decoder and product drafts are excluded. The named-table rows in the accompanying SDN diagnostic were indented for the SDN layout contract; this artifact layout correction does not establish strict parser qualification.
