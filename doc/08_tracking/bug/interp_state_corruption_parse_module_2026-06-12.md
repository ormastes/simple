# Interpreter state corruption around interpreted parse_module (hex-literal conversion)

## Closed 2026-11-25 — not reproducible on the committed seed; see the dated verification note at the bottom

## Not closed 2026-09-13 — left open; seed-interpreter defect, and the fix surface is off limits

- **inferred** The entry isolates the trigger precisely (`parse_module(src, name)` fails iff
  `name` is a path to a REAL existing file, dying on the `0xff` hex literal in
  `src/lib/bitwise_utils.spl` with `cannot parse 'f' as i64`), and locates it in the Rust
  seed interpreter, not in `.spl` code.
- **measured** The referenced source still exists and still contains the hex literal, so the
  entry is not stale by removed code.
- **inferred** Its own repro harnesses (`tmp/site12/name_matrix.spl`,
  `tmp/site12/lean_parse_sweep.spl`) are gone from this tree, so the isolation cannot be
  replayed as written without rebuilding them.
- Left OPEN: the fix is in `src/compiler_rust`, which must not be edited while a bootstrap
  is running; the documented fake-module-name workaround remains valid.


- **ID:** interp_state_corruption_parse_module
- **Severity:** P2
- **Date:** 2026-06-12
- **Component:** Rust seed interpreter (`src/compiler_rust`), interpreted execution of the lean frontend
- **Status:** OPEN (workarounds in harnesses; root cause in seed not investigated per fix-.spl-first rule)

## Symptom

`error: semantic: cannot parse 'f' as i64` — the interpreted lean parser dies
converting a hex literal (`0xff` in `src/lib/bitwise_utils.spl:8`) when, and
only when, specific interpreter constructs precede/surround the
`parse_module()` call. The identical parse at top level of `main()` succeeds.

## Repro (minimal, isolated 2026-06-12 via tmp/site12/name_matrix.spl)

The trigger is the MODULE NAME argument: `parse_module(src, name)` crashes
iff `name` is a path to a REAL EXISTING file (e.g.
"src/lib/bitwise_utils.spl"); the identical source with a fake name
("plain.spl", "x/y.spl", "src/lib/fake_zz.spl") parses fine. Earlier
suspicions (for-in iteration frames, file_write_text before parse) were
confounders — every crashing variant passed a real path as the name and
every passing variant did not.

## Hypothesis

When the name resolves to a real file, some interpreter- or lean-side
machinery (error-context source loading, module registration keyed by path)
re-reads/re-lexes the file through a text→i64 conversion that cannot handle
hex literals ("cannot parse 'f' as i64" on `0xff`).

Note: the COMPILED stage4 binary's check pipeline passes real paths without
crashing — this affects only the seed-interpreted lean parser.

## Workaround (active in sweep harnesses)

Pass a fake module name to parse_module and keep the real path only for
reporting. See `tmp/site12/lean_parse_sweep.spl`.

## Verification 2026-11-25 (p2w3-al lane, Windows) — not reproducible on the committed seed, closing

Runtime: committed `bin/simple.exe` (Rust bootstrap seed v1.0.0-rc.1,
38,403,072 bytes), `SIMPLE_LIB=src ... run`, Windows Git Bash, worktree at
release/1.0.0 @ 4c6024f8271.

The original repro harnesses (`tmp/site12/name_matrix.spl`,
`tmp/site12/lean_parse_sweep.spl`) are gone from this tree, so the documented
isolation was rebuilt as a standalone probe
(`build/p2w3-al-probes/parse_module_realname.spl`, not committed): it calls
`parse_module_silent_checked(src, name)` (the same
`_parse_module_with_diagnostics` path as `parse_module`,
`src/compiler/10.frontend/core/parser.spl:1512`) on source containing the
`0xff` hex-literal shapes from `src/lib/bitwise_utils.spl`, once with a fake
name (`plain.spl`) and once with the real existing path
(`src/lib/bitwise_utils.spl` — confirmed present, still contains `0xff` at
lines 10/16/17).

```
fake-name parse failed=false
real-name parse failed=false
EXIT=0
```

The exact isolated trigger from this doc — real existing file path as the
module name — parses cleanly; the `cannot parse 'f' as i64` death does not
occur. The run went through the interpreter (the module demoted off the JIT
per the `[engine-demotion]` lines), so the seed-interpreter path named in
this doc was genuinely exercised. The seed has been rebuilt many times since
2026-06-12, so whatever seed-side defect this was is no longer present in the
committed binary. LIMIT: this host is Windows and the filing was on Linux;
if the defect is host-specific it could persist elsewhere, but there is no
evidence of that and the fix surface (`src/compiler_rust`) remains off limits
regardless. CLOSED as not reproducible on the committed seed.
