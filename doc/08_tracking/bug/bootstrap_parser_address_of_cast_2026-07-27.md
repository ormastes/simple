# Bootstrap Parser Rejects Address-Of Cast Arguments

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

PARTIALLY RESOLVED. Prefix `&` and `&mut` now pass the flat parser, AST bridge,
HIR, and MIR marker path. Stage 4 parses the previously failing compiler file.
Cast precedence and native stable-place/write-back semantics remain open in
`native_reference_stable_place_writeback_2026-07-27.md`.

## Reproduction

Run:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --deploy --no-mcp --jobs=min \
  --output=build/bootstrap/cosmos-production-20260727
```

The original run failed at `src/os/userlib/device.spl:26` and four equivalent
syscall arguments:

```spl
val info_result = syscall(80, 1, i, &buf as u64, 0, 0)
```

The first diagnostic is:

```text
unexpected token in expression: & '&'
```

The pure-Simple expression parser does not admit `TOK_AMPERSAND`/`&` as the
prefix address-of operator in this argument position, so the subsequent cast
and commas cascade into recovery diagnostics.

## Evidence

- Original source commit: `3e68805fb09f`
- The following Stage 2/3 hashes are unprovenanced artifacts from the later
  dirty-tree run; strict provenance refused continuation.
- Stage 2 SHA-256:
  `51c072812d5cd4b5b80ca2ff289d4e13d3a830adf679e58d61da6762066f816f`
- Stage 3 SHA-256:
  `c2a638a51df632e27352543a458289e857c16bfefd79e020bcce39c608f6870a`
- Focused Stage 4 log:
  `build/bootstrap/cosmos-production-20260727/stage4-focused.log`
- `expr_dispatch.spl` parse completion: `+142622ms`
- Next blocker:
  `bootstrap_stage4_hir_import_crash_2026-07-27.md`

## Required Fix

Fix cast grouping so `&value as u64` is
`Cast(Unary(Ref, value), u64)`, then complete native stable-place/write-back
evidence. Do not rewrite valid userlib syscall arguments as a workaround.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STALE-REF / UNDETERMINED

`grep -rln address_of src/compiler/10.frontend/` returns NOTHING, and the cited
file `src/compiler/10.frontend/parser_types_expr.spl` (783 lines) has no
address-of handling at all. The cited location is wrong; the correct site was
not located by name in this triage. Shares a probable root cause with
bootstrap_prefix_address_of_parser_gap_2026-07-27 (same cited file, same
feature). Owner path: src/compiler/10.frontend/**.
