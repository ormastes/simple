# Spec-to-SSpec / Spec-to-SPipe Domain Research — TLDR

`spec-to-spipe` should be one lossless, version-pinned import pipeline;
`spec-to-sspec` is its compatibility name. Emitting an executable file is not
conversion unless source coverage, requirement disposition, and non-vacuous
production evidence are all proven.

## Core Shape

- Reuse shared lossless parsers for document, XML/HTML, JSON/YAML,
  grammar/IDL, executable-suite, and register families.
- Preserve immutable bytes, mapped preprocessing, malformed `ErrorNode`s,
  license policy, stable semantic identity, and six-layer version differences.
- Prefer official executable suites and schemas over prose-derived tests, while
  retaining a separate source-clause coverage ledger.
- Keep OpenAPI prose authoritative over informational schemas; treat WPT
  manifests as inventory, not coverage proof.
- Normalize CMSIS-SVD/SystemRDL/IP-XACT through one RegisterIR and fail closed
  on unsupported/vendor constructs.

## First Gate

Freeze source/IR/manifest/verifier contracts, then prove the same exact
coverage, recovery, deterministic SPipe/manual output, non-vacuity, and semantic
diff gates on Simple Markdown, openCypher TCK, RFCXML+ABNF, and CMSIS-SVD+NVMe.

## Open Next

- [full domain research](spec_to_spipe_toolchain.md)
- [local repository research](../local/spec_to_spipe_toolchain.md)
- [parallel agent plan](../../03_plan/agent_tasks/spec_to_spipe.md)
- [target architecture](../../04_architecture/app/spec_to_spipe.md)
