# Monomorphization deleted (2026-10-31)

status: OPEN

Repo owner direction: delete monomorphization, accept a temporarily broken
tree, then fix compile errors in follow-up PRs.

Deleted: src/compiler/40.mono and src/compiler_rust/compiler/src/monomorphize.
Resolved when the seed and stage2 build again without them.
