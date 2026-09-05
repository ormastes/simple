<!-- codex-research -->
# Local Research: Spec-to-SSpec / Spec-to-SPipe Toolchain

Date: 2026-08-03
Status: Reviewed companion to `doc/01_research/domain/spec_to_spipe_toolchain.md`

Interpretation: “cyper” means openCypher and “arias” means aliases.

## Conclusion

The current tree has no canonical `src/app/spec_to_spipe` or
`src/app/spec_to_sspec` implementation. Useful behavior is divided among a
modern SSpec-to-manual renderer, narrow legacy extractors, overlapping document
models, hand-maintained conformance inventories, and handwritten register
definitions. The selected architecture should therefore add one lossless
importer, reuse current parser/docgen owners, and retain `spec-to-sspec` only as
a compatibility dispatcher.

## Verified implementation inventory

### SPipe documentation owner

`src/app/spipe_docgen/spipe_docgen/` parses already-authored executable SSpec.
Its `SspecDoc` retains raw source and extracted metadata, doc blocks, scenarios,
evidence, and visibility. It is the correct downstream manual integration seam,
not an external-standard importer. Top-level similarly named files are
compatibility re-exports rather than a second implementation.

### Narrow migration tools

`src/compiler_rust/lib/std/src/tooling/migrate_spec_to_spl.spl` accepts seven
hard-coded inputs, recognizes selected second-level headings and fenced Simple
blocks, comments extracted code, and emits skipped/TODO skeletons. It has no
exact source ledger or tolerant lossless tree. Its `--dry-run` path prints a
banner but still reaches write logic, and its focused test does not establish
import correctness.

`src/compiler_rust/lib/std/src/tooling/extract_tests.spl` recognizes the same
narrow Markdown shape, emits legacy `assert_compiles()` placeholders, and keeps
file/batch operations as explicit stubs.

The older `src/app/doc/spec_gen/` and `src/app/spec_gen/` paths are overlapping
legacy architectures. Historical reports accurately recorded missing bodies,
but some parser, symbol, I/O, and traversal bodies now exist. The current claim
must therefore be “historically incomplete and still weakly verified,” not
“all current operations are stubs.” Consolidation still requires differential
tests before retirement.

### Existing parser foundation to reuse

`src/lib/common/structural/parse/contracts.spl` already defines byte-backed
`SourceSnapshot`, byte `SourceSpan`, `SourceAnchor`, `TextEdit`, diagnostics,
mapping masks, and malformed-input receipts. The CPU reference parser provides
deterministic one-pass recovery for unrecognized byte runs. Phase 0 must extend
these contracts or justify compatible adapters; creating an unrelated source
and mapping subsystem would duplicate a canonical pure-Simple owner.

### CLI gap

The command table registers legacy `spec-gen` and modern `spipe-docgen`, but no
`spec-to-spipe` command. No shared RegisterIR or Simple CMSIS-SVD, SystemRDL, or
IP-XACT adapter was found.

## Verified corpus risks

The current vacuity census reports 12,804 unique specs after twin collapse,
146,688 examples, 22,039 fully vacuous examples in 5,095 files, and 2,704
`describe` blocks with no executable example. These counts come from
`doc/08_tracking/bug/vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md`;
older census totals should not be substituted without reconciliation.

`doc/09_report/html_css_sspec_traceability_2026-07-29.md` remains RED: broad
name inventory is not behavioral evidence, runtime evidence is blocked, and
manuals are stale. This supports importing pinned WHATWG/CSSWG sources and WPT
manifests before synthesizing prose tests.

No non-vendored openCypher implementation, fixture, or test exists under the
audited source/test/tool trees. The TCK is a new adapter pilot, not a migration
of existing production code.

The RV64 compliance spec labels its F/D sections as presence placeholders that
inspect a hard-coded MISA value; a separate floating-point suite contains real
arithmetic behavior. Imported RISC-V claims must cite a pinned manual and
official architectural-test bindings rather than promote presence checks.

The top-level bitfield feature spec validates planned strings and paths, while a
smaller runtime compatibility spec exercises real field reads/writes and
adjacent-field preservation. Some lower-level specs source-grep implementation
strings. The production migration targets are:

- `src/os/kernel/types/bitfield.spl`: stale native-bitfield note plus manual x86
  PTE, capability, and PCI packing;
- `src/os/drivers/nvme/nvme_types.spl`: handwritten offsets, masks, shifts, CC,
  and CSTS definitions;
- `src/lib/hardware/riscv_common/csr_defs.spl`: handwritten CSR/MSTATUS/MIE
  addresses and fields.

## Conformance classification needed by census

Every existing or generated case should be classified as behavioral,
structural, compile-fail, real compile-pass, evidence-only, vacuous,
source-grep, or placeholder. Only the first five count as implemented
conformance. A migration may improve presentation without upgrading the class.

## Design consequences

1. Freeze manifest and shared IR before adapter parallelism.
2. Reuse structural parser contracts and canonical `spipe_docgen` integration.
3. Make exact byte disposition and source-ledger agreement release gates.
4. Import official executable suites before deriving weaker prose tests.
5. Preserve malformed input as error-bearing source nodes.
6. Keep compatibility commands and legacy paths until differential parity.
7. Use a census to prioritize vacuous cases, browser claims, RISC-V claims, and
   handwritten bitfields; do not equate keyword presence with conformance.

## Domain research corrections and constraints

The concurrent domain draft is directionally sound but needs these dated
corrections before it becomes a version authority:

- RFCXML is the definitive published-RFC format, but the live RFC Production
  Center vocabulary supersedes RFC 7991. Pin the retrieved vocabulary/schema
  and distinguish final RPC XML from author/prep-tool input. RFC 9720 and RFC
  9920 govern definitive XML and its updates.
- ABNF is RFC 5234 as updated by RFC 7405, including case-sensitive `%s`
  literals.
- openCypher TCK is a suitable Cucumber pilot, but its repository describes the
  content as experimental/unsupported while the language evolves toward
  ISO/IEC 39075 GQL. Pin the commit and treat current ISO WG3 BNF separately
  from legacy openCypher grammar.
- A WPT manifest inventories tests; it is not a clause-to-test coverage oracle.
  Maintain a separate source-clause binding ledger and pin the WHATWG
  `html/source` commit.
- RISC-V bindings should name the Architectural Certification Tests framework,
  DUT/UDB configuration, Sail reference-model version, ratified extension
  versions, and source/test hashes. Passing tests alone is not full compliance.
- OpenAPI 3.2.0 prose is normative while its official JSON Schemas are
  informational. Import prose, dialect/schema, examples, and executable tests;
  do not substitute schema validation for all normative requirements.
- Pin register-format versions and license policy: CMSIS-SVD documentation is
  1.3.9, SystemRDL is 2.0, and active IP-XACT is IEEE 1685-2022. Scope IP-XACT
  initially to memory maps/registers and fail closed on other/vendor constructs.
  Vendor SVD fixtures need per-pack license review.

### Primary authoritative sources (reviewed 2026-08-03)

- IETF RFCXML vocabulary: <https://authors.ietf.org/rfcxml-vocabulary>
- RFC 9720, RFC 9920, and RFC 7405: <https://www.rfc-editor.org/info/rfc9720/>,
  <https://www.rfc-editor.org/info/rfc9920/>,
  <https://www.rfc-editor.org/info/rfc7405>
- openCypher repository/TCK: <https://github.com/opencypher/openCypher>,
  <https://github.com/opencypher/openCypher/tree/master/tck>
- WPT and WHATWG HTML source: <https://github.com/web-platform-tests/wpt>,
  <https://github.com/whatwg/html/blob/main/source>
- RISC-V tests/specifications: <https://github.com/riscv/riscv-arch-test>,
  <https://docs.riscv.org/reference/home/index.html>
- OpenAPI, JSON Schema, and AsyncAPI: <https://spec.openapis.org/oas/v3.2.0.html>,
  <https://json-schema.org/specification-links>,
  <https://www.asyncapi.com/docs/reference/specification/v3.1.0>
- CMSIS-SVD, SystemRDL, and IP-XACT:
  <https://arm-software.github.io/CMSIS_5/SVD/html/svd_revisionHistory.html>,
  <https://www.accellera.org/downloads/standards/systemrdl>,
  <https://standards.ieee.org/ieee/1685/10583/>,
  <https://www.accellera.org/downloads/standards/ip-xact>

## Sidecar review

Two read-only local audit lanes independently reviewed source implementations
and documentation/test corpus evidence. Their findings were merged and checked
by the primary agent. A separate domain lane reviewed primary-source freshness;
its corrections and authoritative links are recorded above without overwriting
the concurrent domain draft.
