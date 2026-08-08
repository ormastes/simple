# SCV Domain Research

Status: initial Codex research, 2026-05-14.

## Jujutsu UX Model

Jujutsu documents an operation log where each repository-changing operation records a view containing heads, bookmarks/tags/Git refs, and each workspace's working-copy commit. It supports undo, operation restore, and `--at-op` views. Jujutsu also automatically snapshots working-copy changes into commits before most commands, and its glossary distinguishes stable change IDs from rewritten commit IDs.

SCV implication: model `Change` as a stable logical unit, `Commit` as immutable content, and `Operation` as view history. Private working-copy commits should be automatic.

Sources:

- https://jj-vcs.github.io/jj/latest/operation-log/
- https://jj-vcs.github.io/jj/latest/working-copy/
- https://jj-vcs.github.io/jj/latest/glossary/

## Tree-Sitter Parser Index

Tree-sitter supports incremental parsing by editing an old tree with an input edit, reparsing with the old tree, and reusing unchanged structure. Its docs warn that stored `TSNode` instances must be updated after edits, so SCV should not use Tree-sitter node pointers as repository identity.

SCV implication: store byte-exact file objects first, then build immutable SCV-owned syntax node IDs as a derived index. Parser failure or grammar changes must not invalidate private history.

Source:

- https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html

## Structural Diff

GumTree and ChangeDistiller are the relevant prior art for syntax-aware code differencing. GumTree-style matching is useful for move/rename-aware tree diffs. ChangeDistiller is useful for classifying fine-grained source changes.

SCV implication: do not expect Tree-sitter alone to detect moves. Use parser trees as input to a separate structural matcher.

Sources:

- https://www.ifi.uzh.ch/en/seal/research/tools/changeDistiller.html
- https://pinzger.github.io/papers/Fluri2007-changedistiller.pdf
- https://notes.billmill.org/images/gumtree.pdf

## Storage And Compression

Git pack format stores repository objects in pack files and supports delta representations such as ofs-delta and ref-delta. FastCDC is a strong baseline for content-defined chunking because it targets deduplication while reducing rolling-hash overhead. IPFS documentation frames Merkle DAGs as immutable content-addressed nodes whose IDs derive from payload and child IDs.

SCV implication: use content-addressed chunks and Merkle DAG/rope structure for deduplication and integrity. Pack compression is a later maintenance layer, not the first identity model.

Sources:

- https://git-scm.com/docs/gitformat-pack
- https://git-scm.com/docs/pack-format.html
- https://www.usenix.org/system/files/conference/atc16/atc16-paper-xia.pdf
- https://docs.ipfs.tech/concepts/merkle-dag/
- https://arxiv.org/abs/1407.3561

## Recommended MVP Boundary

Implement raw bytes, fallback line/binary views, commit/operation log, and gates before Tree-sitter. Tree-sitter, GumTree-style move matching, full Git import/export, and production pack GC should be explicit later milestones.
