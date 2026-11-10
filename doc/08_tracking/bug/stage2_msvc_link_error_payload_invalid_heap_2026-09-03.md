# Stage 2 MSVC link failure is UNDIAGNOSABLE: the Err payload interpolates to `<invalid-heap:0x...>`

- **Filed:** 2026-09-03
- **Status:** OPEN — current Windows MSVC Stage 2 blocker. Masking defect (1) FIXED in source 2026-11-07 (merge 9e7e7a526edb): the wrapper now interpolates `{e.message}`, and `MsvcLinker.link`/`LldLinkLinker.link` print the raw linker output and persist it to `{output}.link.log` at the call site, so the real diagnostic survives even a corrupt Err payload — component-verified on the seed JIT lane 2026-11-11 (lane interp12, see "Addendum 2026-11-11"). The underlying link failure (2) is still unknown: reproducing it requires a self-hosted stage2 native link, which this lane cannot run (no entry-closure native builds; native-build Windows hang is a known live defect). OPEN pending a stage2 lane.
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


## Addendum 2026-11-11 (lane interp12) — masking defect fixed in source; underlying link failure stays OPEN (BLOCKED here)

**Source inspection (current tree, tip f7640d20a458):** the quoted
`Err("Windows MSVC linking failed: {e}")` no longer exists. The wrapper at
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:2807` now
does `Err("Windows MSVC linking failed: {e.message}")`, and
`msvc.spl` (`MsvcLinker.link` ~L242-249 and `LldLinkLinker.link` ~L448-455)
prints the raw linker output before wrapping and persists it to
`{output}.link.log` — exactly this doc's suggested next step ("add a probe that
prints the raw linker stderr before it is wrapped"). `msvc.spl`'s own comment
names the root cause "the `{e}`-interpolates-a-struct defect" and calls the
corrupted-payload theory a misdiagnosis. The change arrived with merge
9e7e7a526edb (2026-11-07); `git log -S 'Windows MSVC linking failed: {e}'`
finds no commit that ever contained the `{e}` form on this branch.

**Component verification actually run** (worktree simple-p3-interp12-20261111,
fresh seed 46fe8f6b6def, seed-smoke, seed JIT lane — the same engine family as
the self-hosted stage2 native lane):

```
./bin/simple.exe run build/review/p3fix-interp12-20261111/tmp/row8_probe.spl --no-cache
# wrapped-message: the real linker diagnostic
# whole-struct: <invalid-heap:0x197f32473a1>
```

`{e.message}` extracts the diagnostic text; interpolating the whole struct
reproduces the documented `<invalid-heap:0x...>` shape — confirming both the
defect class and the fix. (Under the seed tree-walk interpreter the minimal
`Result<T, LinkError>`-match probe trips an unrelated "assertion outside an
`it` block" interpreter quirk; the production path runs native, and no
end-to-end MSVC link was attempted on this lane.)

**Remaining defect (2) — the underlying link failure — is BLOCKED here:**
reproducing it needs a self-hosted stage2 binary to run a native-build through
the MSVC route, and this lane is granted neither entry-closure native builds
nor a workaround for the known live native-build Windows hang.

**Grant command for the owning stage2 lane:**

```
# stage2 lane, with native-build granted (run under the codex-run-guard):
# 1. build/refresh the self-hosted candidate (bootstrap flow), then force the
#    MSVC route on a SMALL input first (this doc's scope-check question:
#    does <invalid-heap>/the link failure hit every MSVC link or only the
#    route-guard link?):
bin/simple native-build --entry <small_probe>.spl --linker msvc --output build/review/msvc-small-probe
# 2. if the link fails, read the real diagnostic from the probe's own stdout
#    ([msvc-link] output-begin..end) and/or `<output>.link.log`, then re-triage
#    the underlying failure and update this doc.
```
