# Stage 4 full surface traversal crashes after source 400

## Status

Open. The bounded release-slope gate passes, but no full Stage 4 CLI exists.

## Evidence

- Candidate: commit `fc12d6088c`, pure-Simple admission 674 compiled / 0 failed.
- Canonical frontend smoke: PASS.
- Live release slope: `average_growth=10332`, threshold `<=25000`, clean
  `termination=requested seq=10`.
- Full canonical Stage 4 traversal emitted ordered release markers through:
  `seq=400 path=src/compiler/backend/feature_caps.spl`.
- The pure-Simple process then terminated without a compiler diagnostic or
  output artifact. The shell observed signal 15; matching kernel records show
  the `simple` process segfaulting. Host memory was not exhausted
  (113 GiB available after termination).
- A source-discovery-only trace identifies the next physical source as
  `src/compiler/mir_opt/_OptimizationPasses/io_passes.spl`.

`io_passes.spl` contains ordinary top-level functions plus one struct; a
read-only indentation audit found no malformed or unsupported top-level syntax.
The marker boundary identifies the next source to isolate, but does not yet
prove that file caused the segfault.

## Isolation blockers

- Stage 4 correctly rejects a noncanonical entry; a canonical entry expands the
  full main closure and is not a focused probe.
- A standalone `parse_surface_frontend` probe compiles to objects, but current
  runtime bundles cannot link it: `rust-hosted` is removed for noncanonical
  entries, `core-c-bootstrap` lacks hosted parser symbols, and no `simple-core`
  archive is present.
- Clearing parser token text after `lex_next()` was rejected as an unproven fix:
  `CoreLexer.next_token()` has already materialized token text by that point.

## Focused isolation result

A temporary, high-reviewed `surface-probe <path>` branch was admitted into a
pure-Simple bootstrap CLI (674 compiled / 0 failed), used, and then removed.
Both boundary sources pass independently:

- `io_passes.spl`: status OK, 25 functions, one struct;
- `dim_constraints_types.spl`: status OK, two structs, three enums, two impls.

The crash is therefore not a file-local parser/cursor failure in sources 401 or
402. It depends on cumulative process state near 400 surface parses (about
11.56 million no-GC registry entries at marker 400). Further work must inspect
registry capacity/growth and cumulative lexer/parser ownership rather than
patch either boundary source.

## Acceptance

1. Add a bounded cumulative-surface probe or repair the registry/lexer
   ownership failure demonstrated near source 400.
2. Re-run one full Stage 4 traversal; require all surfaces, Phase-3 lowering,
   link success, and a fresh full CLI artifact.
3. Only then proceed to current RV64 web/DB and filesystem toolchain QEMU proof.
