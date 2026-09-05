# Board-Vulkan SSpec manuals: docgen stub + non-execution scope note

**Date:** 2026-08-11
**Lane:** S3 (spipe docgen for `test/01_unit/os/vulkan/`)
**Status:** Open — informational/documentation-quality, not a product defect

## What was run

```
bin/simple src/app/spipe_docgen/main.spl \
  test/01_unit/os/vulkan/*.spl \
  --output doc/06_spec --no-index
```

Scoped to exactly the 10 files under `test/01_unit/os/vulkan/` (no directory
glob at the tool level — `spipe-docgen` takes explicit file args, so the
blast radius was exactly these 10 outputs under
`doc/06_spec/01_unit/os/vulkan/`). `--no-index` avoided touching the
repo-wide `doc/06_spec/INDEX.md`. Ran on the deployed Rust-seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, no self-hosted build was
available in this session) — text-processing risk is low but this is not the
canonical pure-Simple toolchain.

Result: `Generated 10/10 docs (9 complete, 1 stub)`.

## Finding 1 — `cross_arch_boundary_substitution_spec.spl` produced a stub manual

`docgen` reported this file `AUTO ... auto-generated from test structure`
(no docstring found), even though the source has a rich user-voice narrative
at lines 9-20+. The narrative is written as a `#`-comment block wrapping
`"""`:

```
# """
# As the board-Vulkan conformance owner, I need the boundary comparison
...
```

`spipe-docgen`'s parser looks for a real top-level triple-quoted string
literal `"""..."""`, not a comment-prefixed block that merely contains the
`"""` token inside `#` lines. Every other file in the directory uses a real
string-literal docstring and generated a complete manual (9/10). This one
file needs its docstring converted from comment-wrapped to a real `"""..."""`
literal to generate correctly — **this is a fix in that spec file, owned by
another active lane; not applied here per scope instructions.**

## Finding 2 — manual honesty assessment (the part that matters)

Read against what the harness actually proves, the *individual* generated
manuals for `readback_boundary_gate_spec.md` and
`cmdstream_boundary_intel_gen12_spec.md` are **not misleading** — the
docstrings that seeded them already contain explicit "Compatibility and
Limitations" sections stating the real gap (readback: `unavailable` because
`vulkan_venus_session_not_implemented:qemu_only:board_gap_open`; cmdstream:
"synthetic (clearly labelled, not captured)" reference stream, candidate side
`ProviderStatus.unavailable` "until an Intel Gen12 encoder exists"). Docgen
copies the docstring verbatim, so these limitation statements survive into
`doc/06_spec/01_unit/os/vulkan/*.md`.

Two things a reader could still get wrong that are worth calling out
precisely (not spec bugs — reading risks in the aggregate):

1. **No generated INDEX/rollup ties these two facts together.** A reader who
   opens only `provider_inventory_spec.md` (genuine `dpkg -S`) or
   `device_enumeration_boundary_spec.md` (genuine `vulkaninfo` subprocess)
   without also reading `readback_boundary_gate_spec.md` and
   `cmdstream_boundary_intel_gen12_spec.md` could reasonably conclude "the
   harness runs real Vulkan checks" without registering that the two highest-
   stakes boundaries (pixel readback, GPU command stream) are the ones that
   are NOT executed against real hardware/Mesa today. If a rollup/summary
   manual is added later for this feature, it must state per-boundary
   execution status in one table (real subprocess vs. caller-supplied bytes
   vs. declared-synthetic) rather than relying on a reader opening all 10
   files.
2. **`readback_boundary_gate_spec.spl`'s own body never demonstrates the
   `readback_candidate(receipt, image, image)` bytes coming from anywhere
   except the test's own `matching_image()` helper** — i.e., the positive
   ("accepts a fully valid receipt") case is proven only against a
   caller-supplied fixture, which the docstring itself is honest about
   ("constructing bad `ExecutionReceipt` values directly ... over hand-built
   receipts and image byte strings"). No spec-docstring change is needed
   here; the existing wording already discloses this. Flagging only so a
   future summary/rollup doesn't drop the qualifier.

No wording change is required in `readback_boundary_gate_spec.spl` or
`cmdstream_boundary_intel_gen12_spec.spl` — their docstrings already state
the limitation precisely. The wording that DOES need a fix is the missing
real docstring in `cross_arch_boundary_substitution_spec.spl` (Finding 1).

## Scorer results (`sspec-maintain scan`, ranked by `raw=`, NOT the clamped
headline 49/100 every file shows)

Run: `bin/simple src/app/sspec_maintain/main.spl scan test/01_unit/os/vulkan`

| raw= | file | blockers |
|---|---|---|
| 77 | board_vulkan_counterpart_plan_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | cmdstream_boundary_intel_gen12_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | device_enumeration_boundary_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | nvidia_independent_reference_gate_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | provider_inventory_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | readback_boundary_gate_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 77 | spirv_boundary_glslang_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 74 | cross_arch_boundary_substitution_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 74 | headless_readback_capture_lavapipe_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |
| 66 | cts_corpus_spirv_binary_spec.spl | SSDOC-ORA-001, SSDOC-TRC-003 |

Every file in the directory hits the same two blockers, which clamp the
headline to 49/100 uniformly (so the headline cannot rank them — this is
exactly the documented gotcha in `.claude/rules/testing.md`): `SSDOC-ORA-001`
("no real executed assertion or compiler oracle" — the scorer's own oracle
detector does not recognize this suite's `assert_equal`/`assert_true`
idiom over hand-built receipts as a "compiler oracle"; this looks like a
scorer-side false positive given the specs do execute real assertions, not
a defect in the specs themselves) and `SSDOC-TRC-003` ("declared
requirement(s) have no scenario binding" — each file's `# @req REQ-*` header
comment is not being bound to a specific `it` scenario by the scorer's
convention-based grep, which the spec authors could address by referencing
the req ID inside an `it` description or a `# @cover`-adjacent binding
comment if the project wants a clean traceability score).

By `raw=`, the ranking from most-modern to least is: 7 files tied at 77,
then `cross_arch_boundary_substitution_spec.spl` and
`headless_readback_capture_lavapipe_spec.spl` at 74, and
`cts_corpus_spirv_binary_spec.spl` lowest at 66 (worth a closer look by its
owning lane).

## Artifacts

- Generated manuals: `doc/06_spec/01_unit/os/vulkan/*.md` (10 files, scoped
  write, `INDEX.md` untouched via `--no-index`)
- Docgen log: session scratchpad `docgen.log`
- Scorer log: session scratchpad `sspec_scan.log`
