# Startup Architecture

This is the entrypoint for startup architecture. The detailed launch metadata
contract remains in `simple_app_startup.md`.

## Scope

Startup owns how an executable path, script path, SMF package, native binary,
or SimpleOS launcher request becomes a running app. It must decide launch mode,
argv normalization, metadata reads, mmap/read-ahead, dynSMF/native dynlib load,
and SimpleOS prefetch without duplicating compiler or runtime policy.

## Launch Flow

```text
launcher / CLI / SimpleOS WM
  -> identify artifact kind
  -> read launch metadata
  -> build StartupLaunchPlan
  -> gate argv parser, mmap/read-ahead, dynlibs, dynSMF
  -> hand off to interpreter, SMF loader, native entry, or SimpleOS process
```

## Ownership

| Layer | Owns |
|-------|------|
| Compiler | Emits native trailers, SMF `.launch_meta`, sidecar metadata |
| Startup policy | Pure `StartupLaunchPlan` decisions |
| CLI adapters | Direct file dispatch and one-time argv normalization |
| Loader/runtime | SMF mapping, native entry, interpreter execution |
| SimpleOS launcher | Hover prefetch, app-registry byte cache, click launch |

## Invariants

- Startup policy stays pure: no filesystem reads, process spawn, dynlib calls,
  or VFS calls in metadata decision code.
- Native, script, SMF, and SimpleOS paths use the same logical launch metadata.
- Hover prefetch may warm bytes but must not execute, map callable code, or call
  dynlib symbols.
- Fast startup work must prove unused parser/cache/dynlib code is gated out of
  paths that do not need it.

## Detailed Docs

- `simple_app_startup.md`
- `simple_app_startup_tldr.md`
- `../../03_plan/sys_test/simple_app_startup.md`
- `../../03_plan/app/misc/simple_app_startup.md`

