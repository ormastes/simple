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

One incremental full-CLI run then used the admitted candidate with a 64 GiB
virtual-memory cap and the host's 64,000 MiB RSS guard. It reached
`seq=401 path=src/compiler/mir_opt/_OptimizationPasses/io_passes.spl` at
7,448,044 aggregate registry entries. The guard terminated PID 709133 at
64,928 MiB RSS; no artifact was produced.

This is effectively the original source-400 memory boundary despite the lower
registry slope. Token payload strings were therefore measurable but not the
dominant RSS owner. Do not repeat the full run until a focused probe identifies
and reduces the remaining per-token/state-copy or retained-surface allocation.

## First-10 allocation-byte discriminator

A temporary, default-off diagnostic candidate routed only `rt_alloc`/`rt_free`
through the existing runtime memtracker and recorded registry count, tracked
live bytes, and max RSS around the surface parse. The probe stopped at release
marker 10 under a 10 GiB cap. Temporary instrumentation was then removed.

Aggregate deltas across the first ten real closure sources:

| phase | registry | tracked `rt_alloc` bytes | max-RSS KiB |
|---|---:|---:|---:|
| parser initialization | 1,191 | 5,304 | 768 |
| `parse_module_body(true)` | 48,914 | 3,676,080 | 571,936 |
| `flat_ast_to_module` | 8,229 | 186,408 | 512 |
| surface extraction + `ast_reset` | 1,715 | 199,848 | 256 |

`parse_module_body(true)` is the demonstrated dominant owner. Direct
flat-AST-to-surface conversion and per-file `source.chars()` initialization are
not the next fix from this evidence. No second full run is allowed until a
focused probe or ownership repair reduces the surface parse-body delta.

## Raw body skip and retained-slice attribution

An admitted raw indented-body skipper preserves the reference lexer as a
fail-closed fallback for ambiguous punctuation, escaped newlines, and malformed
strings. Higher-capability static review and the canonical frontend smoke pass.
Across the same first ten sources it reduced the parse-body measurements to
33,854 registry entries, 688,704 tracked live bytes, and 92,828 KiB max RSS.

Guarding the disabled lexer-state snapshot at its caller further reduced
tracked live bytes to 357,680, but max RSS remained 91,652 KiB. Both results
remain above the 65,536 KiB focused acceptance limit, so neither permits a
slope or full Stage 4 run.

A final temporary aggregate probe then measured all nonempty `CoreLexer`
`char_slice` operations across those ten sources: 1,093 calls, 7,684 returned
characters, maximum span 34, and 1,085 retained registry entries. This is about
one retained result per call and is too small to explain either the 33,854
parse-body entries or 91,652 KiB RSS. Higher-capability review therefore
exonerated `char_slice` and blocked a speculative keyword fast path. The probe
was removed after collection.

The three focused repair/attribution cycles are exhausted. The next fresh
session should instrument array capacity/reallocation ownership inside surface
parsing; it must not repeat the accepted probes or run a full traversal first.

## Array-capacity ownership repair

Rust-owner evidence identified three full-source `val src` value copies in the
raw body skip, `scan_number`, and `scan_ident` paths. Their maximum allocation
is exactly `file characters * 8` bytes. The baseline first-ten probe measured
15,768,851 slots, 126,141,096 capacity bytes, maximum capacity 176,000, and
126,486,440 peak bytes.

The repair uses direct lexer-field indexing instead of those copies. In the
post-repair first-ten head-10 probe this measured 107,419 slots, 849,640
capacity bytes, maximum capacity 512, and 1,156,904 peak bytes: a 99.3 percent
capacity reduction. Operational HWM growth is `0 KiB`, within the `<= 65,536
KiB` gate. This does not claim zero parse memory: the pre-HWM is 919,524 KiB.
The candidate frontend smoke passed.

The bootstrap candidate does not expose `test`, so a focused pure-Simple test
runner was compiled separately. Its cached closure exposed and fixed one real
entry-closure error: the private sdoctest config parser used a bare positional
`ends_with(inner, "]")` instead of the canonical `inner.ends_with("]")`.

The hosted noncanonical link policy then required current C provider objects.
The third and final bounded cycle compiled and preflighted real providers from
`runtime_legacy_core.c`, `runtime_native.c`, and `runtime_fork.c`, with the Rust
whole archive ordered first to preserve Rust array ownership. The manual link
then exposed only the fork provider's transitive memtrack dependencies:
`g_memtrack_enabled`, `spl_memtrack_record`, and `spl_memtrack_unrecord`.
The three-cycle guard stopped the session there. The raw SSpec did not execute,
so that attempt did not authorize a commit or push. The later exact-file T0
probes and high review accept the scoped parser/C-surface slice for a
feature-branch commit and push only; formal BDD and the repository-wide full
CLI remain blocked.

Fresh-session resume:

1. Reuse the fresh retained Simple objects under
   `build/stage4-surface-raw-skip/native-objects-B72qAN` and the current
   provider objects under
   `build/stage4-surface-nocopy-final/test-runtime-providers/`.
2. Compile current `src/runtime/runtime_memtrack.c` once with the same PIC,
   include, ABI, function-section, and data-section flags.
3. Preflight its three strong memtrack definitions and the full undefined /
   defined union.
4. Link once in this order: Simple objects, compiler backfill, whole Rust
   `libsimple_native_all.a`, legacy/native/fork/memtrack providers, system
   libraries, with GC sections.
5. Use the linker map plus address disassembly to prove Rust still owns
   `rt_array_push_grow`, `rt_array_push`, `rt_array_new`, and `rt_array_copy`.
6. Run `surface_skip_raw_spec.spl` exactly once and stop on its result.

The pure-Simple candidate compile still takes about 7--8.5 minutes, a
regression constraint rather than a resolved result. A follow-up should assess
a `source_char_at` helper for the direct-indexing hot path; do not claim that
optimization is implemented or verified.

## Acceptance

1. Attribute and repair the remaining array/retained-surface ownership, then
   require first-ten parse-body max RSS `<= 65,536 KiB`.
2. Re-run one full Stage 4 traversal; require all surfaces, Phase-3 lowering,
   link success, and a fresh full CLI artifact.
3. Only then proceed to current RV64 web/DB and filesystem toolchain QEMU proof.
## 2026-07-24 full-CLI raw-skip handoff

- A canonical no-stub Stage4 full-CLI attempt stopped after 14 surface files at
  valid `src/app/cli/arch_check.spl:317`: `unexpected ':'`.
- Root cause: inside `CoreLexer.skip_surface_indented_body`, a newline while
  parenthesis depth was positive left `line_start` true because indentation
  handling only runs at depth zero. When `)` returned depth to zero, the
  following same-line `:` was misread as a zero-indent peer.
- Owner fixes: clear `line_start` while `depth > 0` in the raw skipper; at EOF,
  set `CoreLexer.cur_start = self.pos` in `CoreLexer.scan_token()` so
  fast/reference snapshots share the same token-origin state.
- Exact `arch_check.spl` T0 now PASS: both paths report no errors, produce the
  same 23 declarations, and have identical numeric/text snapshots.
- The retained regression in
  `test/01_unit/compiler/parser/surface_skip_raw_spec.spl` is correct. Formal
  BDD acceptance still awaits a current full CLI; the Rust-seed child run
  remains non-acceptance evidence (`no BDD examples executed`).
- Retained evidence: `build/stage4-full-cli-surface-nocopy-20260724/build.log`,
  `build/probes/arch_check_surface_probe.log`,
  `build/probes/arch_check_surface_skip_trace_t0.log`,
  `build/probes/arch_check_surface_probe_after_eof_origin_fix.log`, and
  `build/probes/surface_skip_raw_seed_child_cycle1.log`.
- Resume by rebuilding a clean bootstrap-entry candidate containing these
  fixes, then run canonical frontend admission and one fresh-cache full-CLI
  attempt. Do not re-add tracing.

## 2026-07-24 bounded full-CLI follow-up

- The rebuilt bootstrap-entry candidate passed canonical frontend admission:
  `build/stage4-surface-line-start-eof-final/simple`, SHA-256
  `aacb995d373ce0945dd180da0dcaf7780718e6942d4c18682d13e4ebd5c9083b`.
- Full-CLI cycle 2 exposed three unsupported bare
  `when not BOOTSTRAP_NO_C:` import wrappers. They guarded imports only while
  dependent declarations remained unconditional, so they provided no working
  conditional behavior. The wrappers were removed and their imports retained
  at module scope.
- Exact pre/post T0 evidence is retained in
  `build/probes/c_backend_surface_probe_before.log` and
  `build/probes/c_backend_surface_probe_after.log`. Before the cleanup, all
  three files failed identically in fast/reference modes at the `when` colon.
  Afterward, all parse without errors and have identical declarations and
  numeric/text snapshots; the required C imports are present.
- Full-CLI cycle 3 passed the former blocker and stopped later at
  `src/compiler/10.frontend/core/__init__.spl:111`: the surface parser rejects
  existing `pub mod ast` declarations with `expected declaration after
  visibility modifier`.
- The three-cycle cap is exhausted. Do not retry this build in the current
  session. Formal BDD acceptance for `surface_skip_raw_spec.spl` still awaits a
  current full CLI. Retain
  `build/stage4-full-cli-c-guard-cleanup-cycle3/build.log` as the resume point.
