# Pure-Simple Bootstrap Stage Sanity Test Plan

## Scope

Validate retained Stage 2 and Stage 3 pure-Simple compilers. Each stage must
start, compile the existing `p2_add.spl` redeploy fixture with
`SIMPLE_NO_STUB_FALLBACK=1`, and run the produced native binary.

## Pass Criteria

- `--version` exits 0 and identifies `simple-bootstrap`.
- Unsupported `run` exits 1 instead of being misrouted to `native-build`.
- Strict native build exits 0 and writes an executable.
- The executable exits 0 and prints exactly `5`.
- No Rust seed invocation is accepted as stage execution evidence.

## Execution

```bash
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --no-mcp --jobs=half
bin/simple test test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl --native
```

## Traceability

| REQ | Description | Test File | Generated Spec | Coverage |
|-----|-------------|-----------|----------------|----------|
| REQ-BOOT-STAGE-001 | Every retained pure-Simple stage starts, compiles, and runs a strict native fixture | `test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl` | `doc/06_spec/03_system/feature/compiler/pure_simple_stage_sanity_spec.md` | Stage 2 and Stage 3 |
