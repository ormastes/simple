# Conversion import binding

Executable specification: [conversion_import_binding_spec.spl](../../../../../test/01_unit/lib/common/conversion_import_binding_spec.spl).

This manual traces the nine actual library assertions. The executable imports canonical functions explicitly; raw conversion behavior remains distinct. All matchers are built-in `to_equal` assertions, with no placeholder or empty case.

| Requirement | Scenario | Expected behavior |
| --- | --- | --- |
| REQ-CONV-001 | routes malformed continuation to the question-mark utility | `[C3,41]` produces `?A` |
| REQ-CONV-001 | routes overlong encoding to the question-mark utility | `[C0,AF]` produces `??` |
| REQ-CONV-001 | routes surrogate bytes to the question-mark utility | `[ED,A0,80]` produces `???` |
| REQ-CONV-001 | routes out-of-range lead bytes to the question-mark utility | `[FF,BF,BF,BF]` produces `????` |
| REQ-CONV-002 | routes newline to the restricted CBOR helper | newline produces an empty byte array |
| REQ-CONV-003 | keeps explicit utility alias equal to its canonical owner on a new malformed sequence | both calls produce `?(?` for `[E2,28,A1]` |
| REQ-CONV-004 | keeps the separately imported raw decoder distinct | raw decoding produces replacement characters around `(` |
| REQ-CONV-003 | keeps explicit CBOR alias equal to its canonical owner on tab | both calls reject tab with an empty array |
| REQ-CONV-004 | keeps the separately imported raw encoder distinct | raw encoding produces one byte with value 9 |

Retained execution observed 9/9 runtime passes, exact trusted counters and canonical owner bindings. Intended frozen-source admission remains HOLD because the fixture resolved dependencies into the shared repository. Three conversion-owner pre/post hashes match; other dependency preimages are unqualified. This manual does not claim complete source confinement, pure runtime parity or native products. See [the evidence report](../../../../08_tracking/bug/conversion_import_binding_runtime_evidence_2026_10_13.md).

The landing copy changes only the tested fixture's stale header comment. Its executable body is unchanged; the passing cases were not rerun.
