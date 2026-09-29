# G6 portable HIR integration manifest — 2026-09-11

Status: integration candidate only.  This manifest is not an admission receipt
and does not authorize byte, completeness, or native-loader availability.

## Exact provenance

The isolated worktree started at current `main`:

| role | source commit | integrated commit |
| --- | --- | --- |
| target baseline | `ea03fe06bc635758ff1bab764ea7039097aaee25` | baseline |
| reviewed G6 base | `2cbc2fa0608f3659181f81a5289f5cfa16c06df7` | `0c82007566f28a12346f2284e965af15dcd4f6b8` |
| signature-header precharge | `cf3368309d22e400b1ba37f4862d76182cfb3d52` | `0fe967551c5c2c4f9c8c94bb2638b9a6d6fb4113` |
| semantic-fact precharge | `d722d7688dbc2f92051a7e8de4d5c93d4d34cc55` | `f647796dfbfdc4c0e49d84df082f6cede623ba3b` |
| profile-object single charge | `66e57830912e1bbb2214c1877defca8984ea9f32` | `ca11542652cb3fe569c16289667482cb3ab4791e` |

The source commits share G6 base `2cbc2fa0608f3659181f81a5289f5cfa16c06df7`.
The integration applies that base first, then the two overlapping
`portable_body_semantics.spl` patches in source order, followed by the isolated
profile-object patch.  Git merged the second semantics patch automatically;
no manual semantic conflict resolution or behavior invention occurred.

## Changed product and contract files

- `src/compiler/20.hir/portable_body_semantics.spl`
- `src/compiler/20.hir/portable_object_profile_v1.spl`
- `src/compiler/35.semantics/portable_body_effects.spl`
- Three focused unit specs and their generated Markdown manuals, named
  `portable_body_parameter_header_budget_v1`, 
  `portable_hir_fact_generation_budget_v1`, and
  `portable_hir_profile_counter_v1`.

## Admission state preserved

`portable_hir_semantic_verifier_available_v1()` remains `false`.
`portable_body_semantic_completeness_available_v1()` remains `false`.
`portable_body_semantic_completeness_issue_v1()` still returns
`AuthorityUnavailable`, encoding still returns
`portable_hir_semantic_verifier_unavailable`, verification returns `false`, and
`portable_hir_native_loader_admit_v1()` still refuses with
`portable_hir_verification_failed`.

## Unresolved external prerequisites

G1's physical-TLD and graph-envelope path is not part of this candidate.  The
plan assigns the physical-TLD contract to G0 and the bounded frontend codec to
G1 (`physical_tld_v1` then `physical_tld_codec_v1`); their wire-format,
round-trip, identity, and optional/mandatory-field evidence is absent here.
No graph-envelope bridge, source/section binding, generation/pin/attempt
authority, or native admission receipt is introduced by G6.  These blockers
therefore remain unresolved and all public admission gates stay closed.

## One-pass verification record

| check | result |
| --- | --- |
| `git diff --check main...HEAD` | PASS |
| `bin/simple check src/compiler` | BLOCKED: `bin/simple` is absent in this isolated `main` worktree; attempted once, not retried with a seed or alternate runtime. |
| `sh scripts/audit/direct-env-runtime-guard.shs --working` | PASS |
| `sh scripts/audit/direct-env-runtime-guard.shs --staged` | PASS |

An Astra integration review is required before this branch can be considered
for any later integration.  No push was performed.
