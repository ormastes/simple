<!-- codex-research -->
# Bootstrap ad-hoc quick check — local research

The canonical full Stage4 CLI imports roughly 1,400 modules and is the wrong
inner loop for a local parser, HIR, MIR, or backend fix. The repository already
has a pure-Simple focused native-build owner, entry-closure loading, bounded
process execution, and content hashing. Exact focused Stage4 is intentionally
restricted to CLI/OS entries and therefore cannot be widened into a release
shortcut.

The selected design compiles a feature-owned positive fixture and a negative
fixture with a verified pure Stage3/deployed producer. Changed paths choose the
minimum phase lane; common ABI, interpreter, loader, MDSOC, and weaving changes
fail closed to the full bootstrap. Receipts are developer evidence only.
