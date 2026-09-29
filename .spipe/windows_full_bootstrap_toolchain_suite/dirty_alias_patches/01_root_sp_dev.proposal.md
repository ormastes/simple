# Proposal: `.codex/commands/sp_dev.md`

- Preconditions: ordinary-file SHA-256 remains `3bad34c25a4ffd796d432805c255f8500499ea4dc70075f6ec1caf426be1de63`; preserve a recoverable copy.
- Proposed end state: Git mode `120000`, blob text exactly `../skills/sp_dev/SKILL.md` with no trailing newline.
- Resolution: discard the stale ordinary snapshot; do not copy any portion into `.codex/skills/sp_dev/SKILL.md`.
- Reason: the leaf is historical blob `d888e1b148e5634cca36f2361a1768ca83ee37fe`; the canonical target contains later, sometimes conflicting policy updates.
