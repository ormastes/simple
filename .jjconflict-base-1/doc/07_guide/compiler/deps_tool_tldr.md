# deps Tool — TL;DR

`bin/simple deps <fast|normal|deep> <entry.spl>`

```sdn
deps_modes {
  fast   "per-import: transitive count + sorted file list + CYCLES section"
  normal "adds: exclusive vs shared count + overlap breakdown per import"
  deep   "full closure: SCRIPT (symbols+lines) | SMF (artifact bytes) | NATIVE (bytes/module)"
}
```

Cycle detection: `importgraph_find_cycles` in
`src/compiler/00.common/dependency/graph.spl` (iterative DFS).

## When to use each mode

| Mode   | Use case |
|--------|---------|
| fast   | Quick cycle check + closure size before a refactor |
| normal | Find which import is most expensive to narrow |
| deep   | Audit symbol exposure, artifact completeness, binary size |

## Hub-import trap

`export use x.*` re-export hubs make a single-symbol import cost hundreds of
files. `deps normal` exposes this via the exclusive column. Fix: import the
submodule directly.

Full guide: `doc/07_guide/compiler/deps_tool.md`
