# Interpreter state corruption around interpreted parse_module (hex-literal conversion)

- **ID:** interp_state_corruption_parse_module
- **Severity:** P2
- **Date:** 2026-06-12
- **Component:** Rust seed interpreter (`src/compiler_rust`), interpreted execution of the lean frontend
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## 2026-08-17 (lane w04) — NOT VERIFIED this round

Attempted a direct reproduction of the doc's decisive test (same source, fake
module name vs. real existing path) as a standalone script. It could not be run:
`parse_module` is not reachable as a free function from an ordinary script —

```
error[E1002]: function `parse_module` not found
```

— and the lean-frontend import path that exposes it was not identified within
this lane's budget. **Status unchanged: neither reproduced nor cleared.**

What was confirmed: the hex literal this doc blames is still present and
unchanged at `src/lib/bitwise_utils.spl:11` (`(n >> (pos * 8)) & 0xff`, in
`fn get_byte`). Note the doc cites `:8`; the line has moved but the construct is
the same.

`src/lib/bitwise_utils.spl` is INPUT DATA for this bug, not its cause — the
defect is in the seed interpreter's handling of `parse_module` when the module
name argument resolves to a real file. Nothing in that file was modified, and
nothing in it should be.

Next step for whoever picks this up: find the correct import for the lean
frontend's `parse_module` (it is exercised by the sweep harnesses this doc
mentions), then re-run the fake-name/real-name matrix.
