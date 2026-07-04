# Interpreter state corruption around interpreted parse_module (hex-literal conversion)

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
