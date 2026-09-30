# Frozen entry import identity regression

Copy this fixture's `src` tree into a new, committed Git checkout before using
the public native-build route. Keep build caches isolated from compiler builds.
The closure order is intentional: `consumer` resolves the qualified import
before `relative` resolves `.shared`. Reversing discovery can conceal the bug
because the loaded canonical module shortcut skips the qualified lookup.

## Actual retained-producer failure

- Compiler SHA-256: `250c2d7fc6106e4a3bf5e978b4fda5ed604ae3691197b149b2ea584813b694b4`.
- Compiler source revision: `e4ef2826ff12006989244f97af52abf3e7a57f63`.
- Evidence directory: `/mnt/simple-bootstrap-6b2/mcp-path-repro-250c-20260930-attempt2`.
- `plan.json` records exact argv, sanitized environment, runtime file hashes,
  compiler hash, fixture revision, and source hashes.
- `compile.log`, `process.json`, and `result.json` preserve the actual run.
- Result: exit 1 in 1.870 seconds, before parsing. Four authored files produce
  five physical closure files. `src/app/mcp/shared.spl` and the absolute frozen
  snapshot copy both claim `app.mcp.shared`.
- This is the same failure class as the retained MCP integration log at
  `linux-full-scopefix-20260930/early-continuation-attempt3/phase2-tools-250c2d7/mcp/compile.log`.

The exact public route was:

```text
<pinned-compiler> native-build --entry-closure --source src/app
  --entry src/app/mcp/main.spl --target x86_64-unknown-linux-gnu
  --backend llvm --runtime-bundle core-c-bootstrap --runtime-path <pinned-runtime>
  --threads 1 --cache-dir <isolated-native-cache> --mode one-binary
  --output <isolated-output>
```

Use the recorded plan for the complete environment. It enables inventory cold
initialization and frontend/HIR caches, disables bootstrap delegation and stub
fallback, and does not inject snapshot authority. The compiler acquires the
snapshot through its ordinary public route.

The earlier three-file fixture in `mcp-path-repro-250c-20260930` loaded `.shared`
before the qualified import. It passed source loading and HIR, then failed at
the separately reported cold HIR receipt authority check. It is not a full
successful compilation.

## Fix and verification status

Qualified root and library probes are anchored to the active snapshot only
when the importing directory lies within its exact path boundary. Ordinary
checkout resolution keeps its existing precedence. Missing frozen files do
not fall back to checkout probes on that resolver path. The existing physical
collision guard and `SourceFile` metadata handling are unchanged.

`test/01_unit/compiler/bootstrap/frozen_entry_import_resolution_spec.spl`
checks both orders, terminal-symbol fallback, numbered compiler directories,
explicit and implicit library imports, missing frozen files, path-boundary
isolation, authored path retention, and genuine physical collisions.

The source fix and new specs require a refreshed self-hosted compiler for
runtime verification. No green result, executable admission, full bootstrap
retry, or production-cache invalidation is claimed.
