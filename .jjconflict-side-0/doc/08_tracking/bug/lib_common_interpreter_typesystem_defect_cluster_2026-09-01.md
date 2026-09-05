# `test/01_unit/lib/common/` triage: interpreter type-system defect cluster

Date: 2026-09-01
Status: OPEN (multiple distinct defects, filed together per the triage task's
instruction not to attempt risky compiler-internals fixes)
Severity: Medium-High — affects dozens of spec files across `lib/common`

## Context

During a full triage pass of `test/01_unit/lib/common/` (965 spec files),
after excluding the ~250 pre-existing `Cannot resolve module: common.*`
failures already owned by another parallel session, roughly 55 files failed
with genuine assertion/semantic errors. Several of those share one of a small
number of interpreter-level defect signatures rather than being independent
bugs in each spec's target code. Each is reproducible via:

```bash
bin/simple test <path>
```

Filing per CLAUDE.md guidance: "The deep interpreter type-system errors ...
are likely compiler-internals defects rather than test bugs — if so, file
them with a minimal reproduction rather than attempting a risky compiler
fix." Grouped here by signature rather than one record per file, since they
are very likely one root cause each behind several call sites.

## Cluster 1: `semantic: nil is forbidden by the non-optional return contract of 'X'`

Reproduces in (non-exhaustive):
- `test/01_unit/lib/common/compress_facade_harness_spec.spl` (`from_ymd`,
  `parse_iso8601`)
- `test/01_unit/lib/common/date_calculate_coverage_spec.spl` (`add_days`)
- `test/01_unit/lib/common/date_format_coverage_spec.spl` (`from_ymd`)
- `test/01_unit/lib/common/html_entities_coverage_spec.spl` (`new`)
- `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` (`join`)

All hit the runtime's non-optional-return contract check returning `nil` from
a function declared to return a non-optional type, across unrelated modules
(`date`, `html_entities`, `sdn`, `text.join`). Given the breadth (5+
independent modules, none obviously related to each other) this looks like an
interpreter-level issue with how the contract check interacts with some
common pattern (e.g. an early-return branch, or a specific arg shape) rather
than 5 independent authoring bugs — needs a compiler-side investigation to
confirm/deny a shared cause.

## Cluster 2: enum values treated as tuples (or vice versa)

```
semantic: invalid operation: tuple index access on non-tuple type enum
semantic: invalid operation: cannot index value of type enum
semantic: invalid assignment: cannot index assign value of type enum
```

Reproduces in:
- `test/01_unit/lib/common/option_ce_spec.spl`
- `test/01_unit/lib/common/parsers_json_core_spec.spl`
- `test/01_unit/lib/common/parsers_json_ops_spec.spl` (25 of 64 examples)
- `test/01_unit/lib/common/xz_lzma2_spec.spl`

An enum value (e.g. from a JSON-value ADT) is being indexed with `.0`/`[i]`
syntax as though it were a tuple, or index-assigned as though it were an
array — across the JSON parser, the `xz`/`lzma2` codec, and `Option`
combinator specs. Same shape appears in `test/01_unit/lib/common/
module_import_spec.spl` as `semantic: type mismatch: cannot convert enum to
int` (all 21 examples fail) and in `date_calculate_coverage_spec.spl` as
`semantic: type mismatch: cannot convert tuple to int`. This is consistent
with an interpreter bug in enum-variant payload access/dispatch, not
independent bugs in JSON parsing, compression, and date arithmetic code.

## Cluster 3: `unknown static method X on class Y`

- `test/01_unit/lib/common/immut/ref_spec.spl`: `unknown static method new on
  class EnvironmentStack`
- `test/01_unit/lib/common/mock_phase3_spec.spl`: `unknown static method
  create on class MockFunction`

Possibly the same class-name-collision family as
`doc/08_tracking/bug/fs_file_class_collision_wrong_static_method_2026-09-01.md`
(two classes sharing a name, interpreter picks the wrong one by name) rather
than a genuinely missing method — not confirmed; needs the same
duplicate-definition check (`grep -rn 'class EnvironmentStack\|class
MockFunction' src/lib`) that found the `File` collision.

## Cluster 4: undefined variable in generated/desugared code

- `test/01_unit/lib/common/contracts/execution/
  simpleos_executable_admission_v1_spec.spl`: `semantic: variable idx3 not
  found`
- `test/01_unit/lib/common/feature_validation/codegen_spec.spl`: same

`idx3` reads like a compiler-internal desugaring temporary (loop-index
naming convention), suggesting a codegen/lowering bug rather than a spec
authoring bug — the variable name is not something spec or product source
would plausibly write directly.

## Cluster 5: LZ4 empty-input handling

- `test/01_unit/lib/common/compress/lz4_empty_frame_roundtrip_spec.spl` (3 of
  4 examples)
- `test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl` (all
  3 examples)

```
semantic: called unwrap on Err: CompressionError::CorruptStream(lz4 empty data block)
```

Unlike the clusters above, this looks like a real, narrowly-scoped product
bug in the LZ4 codec (`src/lib/common/compress/**`) rather than an
interpreter defect: it fails specifically and only on empty/zero-length
input, a classic boundary case the codec's decoder likely doesn't special-case
(zero-length frame or block). Worth a follow-up fix in `lz4` decode, separate
from the interpreter clusters above — flagged here rather than fixed because
locating the exact LZ4 decode function was out of the time budget for this
triage pass.

## Not fixed here

None of the specs above were modified; all are left RED and reported as
genuine failures, per `.claude/rules/testing.md` ("a known-failing spec
documents a real defect"). Each cluster needs its own compiler-side (or, for
cluster 5, codec-side) investigation before a fix is attempted.
