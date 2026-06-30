# Variant Overlay — os/env paths path_separator: Runtime-Host Decision, Not Build-Time

Date: 2026-06-29
Candidate: `variants/os/` overlay keyed on `path_separator` (`:` vs `;`)

## RESOLVED — OS lane IMPLEMENTED via a different (qualifying) seam

`path_separator` itself stays REJECTED (see verdict below). But the OS lane's
genuine build-time seam is the **build-target file extensions**
(`lib_ext` `.so`/`.dylib`/`.dll`, `exe_ext` `.exe`/``) — a pure build-target
property, advisor-endorsed. Implemented (landed): new seam
`src/lib/nogc_sync_mut/target_ext.spl` (canonical = host detection, so
default/`auto` is unchanged); `platform.spl` `lib_ext`/`exe_ext` delegate to it;
`variants/platform/{windows,mac,linux}/nogc_sync_mut/target_ext.spl` return fixed
extensions for explicit targets. Default-host behavior verified at runtime
(`lib_ext()==".so"`, `exe_ext()==""`); spec
`test/01_unit/lib/nogc_sync_mut/target_ext_spec.spl` green. Unlike
`path_separator`, the canonical falls back to host detection so `auto` never
regresses; only an explicit `platform:` value bakes a fixed extension.

---

## Verdict: FAILS criterion (2) — separator is a runtime-host decision

### Evidence

File: `src/lib/nogc_sync_mut/env/paths.spl` lines 14-24

```
fn path_separator() -> text:
    val os = platform.detect_os()
    if os == "windows":
        ";"
    else:
        ":"
```

File: `src/lib/nogc_sync_mut/env/platform.spl` lines 15-53

`detect_os()` reads `$OS` env var (line 24), then `$OSTYPE` env var (line 29),
then shells out `uname -s` (line 41) — ALL at call time on the running host.
There is no compile-time constant, no build flag, no target triple query.

### Why baking at build time would regress

`bin/simple` is a cross-platform compiler that runs on host A to compile code
for target B. If path_separator were baked into the binary at build time (host A),
running `simple run` on a different host (B) would return the wrong separator
for that host's PATH env operations. The `auto` variant selector also has no
host-detection mechanism yet.

### Criterion check

| Criterion | Result |
|-----------|--------|
| (1) Real existing variation | PASS — `:` vs `;` branch exists |
| (2) Build/deploy-target choice, not runtime-host | FAIL — detect_os() reads env+uname at runtime |

### Precondition to qualify later

Two changes required together:
1. Add a build-time `--target-os=<os>` flag (or read the target triple) so the
   compiler knows the TARGET OS at compile time, not the host OS at run time.
2. Wire an `auto` variant selector that maps target-os to the correct separator
   variant without ever calling `detect_os()` at binary runtime.
Only then can `path_separator` be a legitimate compile-time constant folded via
the overlay.
