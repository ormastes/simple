# Stage 2 MSVC link failure is UNDIAGNOSABLE: the Err payload interpolates to `<invalid-heap:0x...>`

- **Filed:** 2026-09-03
- **Status:** OPEN — current Windows MSVC Stage 2 blocker
- **Platform:** Windows MSVC (self-hosted stage 2 candidate). The masking mechanism is a
  value-representation defect and is not obviously Windows-specific, but it has only been
  observed on this lane.

## Symptom

The Stage 2 struct-receiver/runtime probe fails with:

```
error: in-process native-build: Bootstrap LLVM link failed (input=...bootstrap-stage3-route-guard.app.cli.bootstrap_main.o
  output=...bootstrap-stage3-route-guard): Linking failed:
  Windows MSVC linking failed: <invalid-heap:0x1d72fdbdf01>
```

`stage2-receiver.env`: `status=fail probe_exit=1`,
`candidate_sha256=432d9c981a2c1e3d81163d7e7406f6cd4e2b0d279c9dcc28dca6410c92f223a5`.

## What is actually wrong

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:877`

```
case Err(e):
    Err("Windows MSVC linking failed: {e}")
```

`e` — the `Err` payload of `MsvcLinker.link(...)` — interpolates to `<invalid-heap:0x...>`, i.e.
a corrupt heap reference, in the self-hosted stage 2 binary. **The real linker diagnostic is
destroyed before anyone can read it**, so the underlying link failure cannot be diagnosed at all
from the receipt. This is the same class as the `[bootstrap-error-count] count=N` with no
diagnostic text: evidence that an error existed, and no error text.

Two defects are stacked and must be separated:
1. **The masking defect (fix first).** A `Result` `Err(text)` payload does not survive across the
   `MsvcLinker.link` return boundary under native codegen. Until this is fixed every link failure
   on this lane is undiagnosable.
2. **The underlying link failure**, still unknown.

## Progress this run — what this is NOT

Both previously-suspected causes are eliminated and must not be re-investigated:

- **NOT the exit-127 `aot:lower_to_mir` death.** That was a stack overflow (0xC00000FD) from an
  aliased-import self-recursion; fixed in `3dd179a075a`. See
  `aliased_import_shadowed_by_local_fn_native_codegen_2026-09-03.md`.
- **NOT the `runtime_dynload.c` compile error.** Fixed in `63886bdcc41` (missing forward
  declaration of `runtime_dynload_open_utf8`).

Stage 2 now compiles and links its own 105,888 KB binary successfully
(669.7 s compile + 30.3 s link) and gets all the way through the probe's own native-build to the
LLVM link of the route guard. The remaining failure is strictly later than every previously
known blocker.

## Suggested next step

Make the linker wrapper capture the child's stderr into a freshly-owned `text` at the call site
(rather than propagating a payload through the `Result`), or add a probe that prints the raw
linker stderr before it is wrapped. Once the real diagnostic is visible, re-triage.

## Scope check (2026-09-03, measured on candidate `432d9c98...`)

Re-running the original two-line hello world against the NEW rejected candidate now prints
**`aot:lower_to_mir:done`** (2 occurrences) and proceeds all the way to the link step. The
exit-127 stack overflow is directly, positively closed — not merely inferred.

That run does not discriminate the link failure's scope, however: the hello-world path selects
the MinGW/`gcc` link route, not the MSVC route the probe uses, so it fails differently
(`command: gcc ... -lmingw32 ...`). The `<invalid-heap>` failure has so far been observed only
on the probe's MSVC route. Whether it is specific to the large route-guard link or affects every
MSVC link is still **open** and is the first thing to settle next session — force the MSVC route
on a small input rather than relying on the default route selection.
