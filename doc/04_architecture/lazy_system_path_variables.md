<!-- codex-design -->

# Lazy system path variables architecture

## Decision

Use a two-stage value:

```text
source literal -> LazyPathTemplate (inert) -> canonical logical path -> anchored host open
```

`std.nogc_sync_mut.env.system_location` owns registered names, override precedence, platform defaults and canonical `/` rendering. It does not own filesystem access. The later host-path authority converts the canonical path to Windows UTF-16 handles or POSIX descriptors and enforces containment.

## Interfaces

```text
SystemLocationKind
SystemLocationInputs
system_location_resolve_from(kind, inputs)
system_location_resolve(kind)
LazyPathTemplate.new(raw_template)
LazyPathTemplate.new_with_override(raw_template, environment_name)
LazyPathTemplate.resolve()
system_path_native(path)
```

The process adapter uses the compiled-in platform name and bounded `env_get` calls only when `resolve()` is first called. The pure `resolve_from` seam makes platform matrices deterministic without mutating the test process environment.

Canonical paths are cache/comparison values. File and process-launch owners call
`system_path_native` only at the final OS boundary. Windows output uses `\\` and
normalizes `C:/x`, `/c/x`, or `c/x` to `C:\\x`; POSIX output retains `/`.

## Grammar migration

Phase A implements the runtime contract through a raw template constructor;
single-quoted literals are the bootstrap-stable spelling when braces must reach
that constructor unchanged. Phase B preserves typed string suffixes in the
pure-Simple flat AST and lowers `"..."_path` to the same token contract. Phase C
propagates expected `Path` types so `file_open("...")` receives identical
lowering. An ordinary untyped string containing `{sys:...}` fails with an
`_path`/type-annotation suggestion; content spelling alone never implies a path.

## Startup closure

The eager surface contains only enum/record declarations and inert construction. Platform/env resolution is called on demand. Filesystem validation, cache daemon, database, CAS and Windows reparse-point code are not imported by template construction.
