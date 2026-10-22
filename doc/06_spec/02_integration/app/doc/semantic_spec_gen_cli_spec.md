# Semantic links through the existing spec-gen CLI

Authored manual; two actual-process scenarios UNRUN. REQ-MC-008 B4.

1. Create real source and an existing-format specification using modern `it` and explicit `**Links:**` annotation. Supply all four existing authority flags to `spec-gen --input`. Require a verified declaration link in the published Markdown. Edit source and require nonzero failure while preserving the previous output exactly.
2. Refuse incomplete authority flags and `--all` with one source authority before generation or repository-wide traversal.

The parser's ordinary caller retains its previous default. Semantic mode only enables existing explicit symbol annotations and modern `it` extraction. The common file-authority batch opens the actual producer once; no initial cache is manufactured. SPipe docgen integration remains a separate open counterpart. No runtime or docgen evidence is claimed.

## C4 authored markerless scenarios — UNRUN

The actual parser and existing spec-gen CLI receive a markerless modern it body
with explicit Links annotation. Require one extracted case and the exact emitted
declaration link. Replace that annotation with a malformed URI and require the
URI-specific 12-hex diagnostic, exit1 and unchanged prior output. Retained legacy
markers cannot hide modern body annotations. Empty extraction refuses with its
own diagnostic and preserves output. Existing marker-based scenarios remain.

## C5 exact leading-comment counterexample — authored UNRUN

A markerless it body has a comment containing a triple-quote example before the
real leading docstring. The actual parser must retain its valid Links URI; the
existing CLI must emit the canonical declaration link. Replacing that real
annotation with `spl:fn@sample.math.increment~bad` must retain it in parsed
symbols, return the URI-specific 12-hex refusal from the actual CLI, and leave the
previous output byte-identical. Missing-entry/unrelated failures are not the
oracle. All earlier scenarios remain verbatim.
