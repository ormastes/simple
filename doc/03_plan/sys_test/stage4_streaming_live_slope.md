# Stage4 Streaming Live-Slope Test Plan

## Scope

Prove that a source-matched pure-Simple compiler activates the experimental
streaming `ModuleSurface` path and bounds live registry/RSS growth across a
deterministic 40-file entry closure.

## Acceptance

- The runner rejects the Rust seed, debug binaries, unbounded/failed version
  probes, and any missing compiler binary.
- The canonical bootstrap writes an adjacent provenance manifest after its
  essential-tools smoke. It binds the full CLI, current source, producer/helper,
  parent compiler, and verified Stage3 manifest by canonical path and SHA-256.
- All Stage4, low-memory, entry-closure, profiling, and no-stub opt-ins are set.
- Native build exit and timeout status fail closed.
- Exactly one `phase2:surface:file:released` receipt exists per generated file,
  with contiguous sequence numbers and unique expected `mod*.spl` paths.
- Average and maximum per-file registry growth stay within configured ceilings.
- Peak RSS stays below the configured ceiling.
- PASS output includes fixture dimensions, registry metrics, RSS, and binary hash.
- `--self-test` accepts escaped-newline markers, rejects duplicate/wrong-directory
  paths, validates the canonical Stage4 lane, and rejects missing smoke receipts.

## Boundary

This gate is required before a full CLI Stage4 admission run. It does not prove
the full production closure, deployment, or physical FPGA behavior.

## Producer Contract

`scripts/bootstrap/bootstrap-from-scratch.sh` writes
`<full-cli>.provenance.env` only after the Stage4 essential-tools smoke. The
manifest identifies `pure-simple-full-cli` and binds the binary, source roots,
bootstrap producer, provenance helper, parent compiler, fully verified Stage3
provenance, exact build log, and required essential-tools receipts. Emission
also requires the Stage3-recorded bootstrap lock to be owned by the producer.
An operator-authored manifest is not admissible.

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli
```

Run the gate with both artifacts:

```sh
STAGE4_PARSE_MEM_MULTI_BINARY=<candidate> \
STAGE4_PARSE_MEM_MULTI_PROVENANCE=<candidate>.provenance.env \
  sh scripts/check/check-stage4-selfhost-parse-memory-multifile.shs
```

The gate rejects a non-adjacent or symlinked manifest, duplicate fields, stale
Stage3 authority, any path/hash mismatch, source mutation during the run, and
binary mutation after either the version probe or native build.
