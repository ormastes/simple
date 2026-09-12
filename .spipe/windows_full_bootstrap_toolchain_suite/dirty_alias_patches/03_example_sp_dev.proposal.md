# Proposal: `examples/05_stdlib/spipe/.codex/commands/sp_dev.md`

- Preconditions: ordinary-file SHA-256 remains `2bb93b0abff35a96341d839cc38ddceb4b8b7b46df6d5675b85b006e2097f4e2`; preserve a recoverable copy.
- Proposed end state: Git mode `120000`, blob text exactly `../skills/sp_dev/SKILL.md` with no trailing newline.
- Resolution: discard the stale ordinary snapshot; do not merge it into the skill target.
- Reason: target-only protected-PR guidance is a later tracked canonical update; the leaf has no unique content.
