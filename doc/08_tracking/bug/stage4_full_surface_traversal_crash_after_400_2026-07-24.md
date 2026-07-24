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

## Acceptance

1. Provide a supported focused parser-probe runtime/entry or an equivalent
   source-index diagnostic that does not expand the full CLI closure.
2. Prove surface parsing of `io_passes.spl` and its successor independently,
   with the following declaration token materialized correctly.
3. Re-run one full Stage 4 traversal; require all surfaces, Phase-3 lowering,
   link success, and a fresh full CLI artifact.
4. Only then proceed to current RV64 web/DB and filesystem toolchain QEMU proof.

