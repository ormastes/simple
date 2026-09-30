# Domain research: bug-linked workarounds

Research date: 2026-09-30. Primary references consulted:

- [ccache manual](https://ccache.dev/manual/4.14.html): direct-mode manifests
  associate compilation inputs with cache results, and validation of changed
  inputs remains necessary for correct reuse.
- [Git restore documentation](https://git-scm.com/docs/git-restore/2.50.0.html):
  restoring from a chosen tree updates selected working-tree/index paths.

Design inference: a workaround index is a discovery cache, not a compiler
cache admission receipt. Refresh it at an explicit maintenance/build boundary
and keep source/content validity under the existing compiler cache owner.
Its Git reference provides material for a reviewed patch; automatic whole-file
restoration could discard newer edits to the same file.

Retained approach, selected by the user's request: source comment plus textual
derived index. Pros: annotations travel with code; lookup avoids source scans;
existing bug identity and state stay authoritative. Cons: index freshness must
be explicit and recovery still needs semantic review. Effort: moderate,
covering parser, serialized state, incremental maintenance, CLI join, focused
tests, and bootstrap/debug knowledge updates.
