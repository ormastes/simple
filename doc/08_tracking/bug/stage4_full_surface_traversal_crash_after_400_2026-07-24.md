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

## Method-surface reduction follow-up

Surface parsing now also omits ordinary class, struct, enum, impl, and extend
method bodies while retaining trait default bodies. Focused admission compiled
7 files with 667 cached and 0 failures; the canonical frontend smoke passed,
and the live release slope remained bounded at `average_growth=10240`.

A single full traversal with that candidate advanced through
`seq=275 path=src/os/_QemuRunner/scenario_catalog.spl` at 7,443,718 aggregate
registry entries, then ended with status 143 and produced no artifact. Source
discovery reports 1,315 physical sources (1,807 total source records), so this
marker is still inside Phase 2.

The host journal identifies the termination: at 12:26:19 UTC `earlyoom` sent
SIGTERM to `simple` PID 398434 at 40,480 MiB RSS because host available memory
and swap had both fallen below 10 percent. The process exited 6.1 seconds later,
matching status 143.

A nearby invalid-opcode record was initially suspected, but it belongs to a
different `simple` PID (435827) 18 seconds earlier. It cannot be attributed to
this traversal from the retained evidence. Its mapped HIR instruction is also
Phase-3-only while the terminated build was still in Phase 2. Do not patch the
mapped HIR/MIR functions from that unrelated correlation.

The registry audit rules out a fixed 11.56-million-entry capacity: individual
registries grow geometrically. Strings are never unregistered, so cumulative
growth is real. The registry mutation paths are unsynchronized, but the
`--threads 1` compiler path is sequential through Phase 2, Phase 3, and AOT;
concurrent registry reallocation is therefore not supported as this crash's
cause. The remaining demonstrated failure is cumulative no-GC allocation and
host memory pressure during sequential Phase 2.

## Per-call lexical discard follow-up

The body omission path now advances omitted bodies through the existing lexer
state machine without materializing nonstructural token payloads. It remains
per-call, restores normal lexing before the declaration after the outer
DEDENT, and does not affect full parsing or retained trait defaults.

- Higher-capability static review: PASS after correcting `in`/`and`/`or` token
  kinds and ordinary unterminated-triple parity.
- Pure-Simple admission: 674 compiled, 0 cached, 0 failed; linked candidate.
- Canonical frontend smoke: PASS.
- Live release slope: `average_growth=6543`, threshold `<=25000`, clean
  `termination=requested seq=10`.

The first live invocation enabled phase profiling, whose adjacent stderr
records hid marker 1 from the line-oriented checker. The canonical rerun used
`SIMPLE_COMPILER_PHASE_PROFILE=0` and passed; this is an invocation/log framing
issue, not a second compiler failure.

## Acceptance

1. Add a bounded cumulative-surface probe or repair the registry/lexer
   ownership failure demonstrated near source 400.
2. Re-run one full Stage 4 traversal; require all surfaces, Phase-3 lowering,
   link success, and a fresh full CLI artifact.
3. Only then proceed to current RV64 web/DB and filesystem toolchain QEMU proof.
