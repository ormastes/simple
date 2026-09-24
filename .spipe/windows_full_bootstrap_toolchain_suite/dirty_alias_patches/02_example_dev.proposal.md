# Proposal: `examples/05_stdlib/spipe/.codex/commands/dev.md`

- Preconditions: ordinary-file SHA-256 remains `299e0cd5653f7141ecb19280c3b0b260c4375225000eafe4db9e044114a493f1`; preserve a recoverable copy.
- Proposed end state: Git mode `120000`, blob text exactly `../skills/dev/SKILL.md` with no trailing newline.
- Resolution: discard the stale ordinary snapshot; do not merge it into the skill target.
- Reason: target-only protected-PR guidance is a later tracked canonical update; the leaf has no unique content.
