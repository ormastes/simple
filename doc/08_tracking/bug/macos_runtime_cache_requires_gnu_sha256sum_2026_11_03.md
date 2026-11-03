# macOS runtime object memo requires unavailable GNU sha256sum

Status: source fix with native shell-mechanism verification; compiled Simple
regression, compiler smoke and bootstrap qualification remain pending.

Source baseline: `bab4908dfdf31004271f9705a3b7d1353b23ebb3`.
Host: Darwin arm64, 2026-11-03. Scope: the optional POSIX C runtime object
memo in `src/compiler/70.backend/backend/runtime_compiler.spl`.

## Reproduction and impact

`_runtime_object_cache_dir` ran `sha256sum` twice. Stock macOS provides
`/usr/bin/shasum`, but no `sha256sum` in `/usr/bin:/bin`. Running the old
fingerprint command with that PATH and real tiny C/header files returned an
empty key. Its final `cut` exited zero, but the short-key check correctly
disabled caching. Runtime compilation therefore remained available while
repeating work on subsequent builds. No measured compile-time speedup is
claimed by this repair.

## Repair

The small `runtime_object_cache_posix` owner selects `shasum -a 256` for the
macOS host and retains `sha256sum` elsewhere. Selection uses execution-host
OS, not cross-compilation target OS. It quotes caller strings and passes file
names directly through batched `find -exec ... {} +`, avoiding `xargs` filename
splitting. Sorted complete digest/name rows retain deterministic content and
name identity. Cache schema prefix v8 prevents reuse of the older material.

Compiler version capture, source enumeration/hashing, sorting and final hash
must succeed; missing/empty source sets or empty compiler identity refuse a
key. In particular, a failing source hash cannot be hidden behind a successful
final hash. Windows, strict managed runtime authority and explicit cache-off
still bypass this optional memo at the existing entry guards.

## Evidence boundary

The diagnostic assembled the current helper's literal concatenation fragments
with a restricted external evaluator, then executed the resulting command with
native `/bin/sh`, `/usr/bin/find`, `/usr/bin/shasum` and `/usr/bin/cc`. This is
**not execution of the Simple helper or compiler**. The helper source SHA-256
is bound in the receipt. An independent SHA-256 calculation over actual
compiler-version bytes and sorted native hash rows matched the emitted key.

Native shell checks passed once:

- Original GNU-only command produces no key on stock macOS PATH.
- New command handles spaces/apostrophes and repeats the same key.
- Source edits, added headers and semantic flags produce distinct keys.
- Missing source root, failed or empty compiler identification and a failing
  source hash each return nonzero with no key. BSD `find` propagates the
  failing batched `-exec` status.

Receipt: `doc/09_report/evidence/macos_runtime_cache_20261103/command_results.sdn`.
The authored four-case native macOS SSpec remains **UNEXECUTED**. No full
compiler/lib/MCP checks, native MCP smoke, SPipe docgen, successful Phase 3
link/Hello or cache-hit benchmark was produced by this lane. These missing
gates prevent claiming general runtime or bootstrap admission.
