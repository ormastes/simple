# Proposal: `src/app/lint/main.spl`

- Preconditions: ordinary-file SHA-256 remains `32f71c2bc5ef38842a0b714c0ecc2b8c9d689ef71e3426cbc627fc74bf3f14e5`; preserve a recoverable copy.
- Proposed end state: Git mode `120000`, blob text exactly `../../compiler/90.tools/lint/main.spl` with no trailing newline.
- Resolution: discard the stale facade snapshot; do not remove or backport away `legacy_adapter` from the compiler-owned target.
- Reason: the leaf is historical blob `6211849cc02fad67270737844b97c1d00cd461b6`; current target blob adds the tracked `legacy_adapter` export used as part of the canonical lint facade.
