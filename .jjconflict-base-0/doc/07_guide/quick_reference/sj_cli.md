# sj CLI Quick Reference

`sj` is the repo-local wrapper for serialized jj/git operations.

Common forms:

- `sj describe -m "msg"`: direct jj-native command
- `sj git status`: git-shaped command translated to jj
- `sj git commit -m "msg"`: translated to `jj describe -m "msg"` then `jj new`
- `sj raw git <args...>`: explicit escape hatch for raw git passthrough
- `sj raw jj <args...>`: explicit escape hatch for raw jj passthrough

Push patterns:

- Preferred: `sj bookmark set main -r @-` then `sj git push --bookmark main`
- Opt-in worktree path: `sj git push --via-worktree`
- Forbidden: bare `sj git push` and `sj git push --force`

Muscle-memory mapping:

- `gg status` -> `sj git status`
- `gg commit -m "msg"` -> `sj git commit -m "msg"`
- `gg checkout -b topic` -> `sj git checkout -b topic`
