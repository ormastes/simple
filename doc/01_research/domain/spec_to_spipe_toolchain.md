<!-- codex-research -->
# Domain Research: Spec-to-SSpec / Spec-to-SPipe Toolchain

Date: 2026-08-03
Status: Reviewed against primary sources
Companion: `doc/01_research/local/spec_to_spipe_toolchain.md`

## Executive conclusion

Internet specifications are not one input language. A scalable importer needs
lossless parsers for a small set of format families, thin version-pinned
semantic adapters, direct bindings to official executable suites, and one
source ledger that accounts for every byte and every applicable requirement.

The canonical product name should be `spec-to-spipe`; `spec-to-sspec` is a
compatibility command because executable SSpec is one artifact within the wider
SPipe provenance, manual, evidence, and verification workflow.

An emitted `_spec.spl` file is not proof of conversion. Completion requires:

- immutable source identity and license policy;
- exact byte disposition and lossless recovery records;
- explicit conformance disposition for every applicable requirement;
- non-vacuous production evidence;
- deterministic SPipe/manual/source-ledger generation; and
- semantic version differences, not only text differences.

## External evidence by source family

### Document and web standards

WHATWG HTML is maintained as a monolithic source document, while CSSWG commonly
uses Bikeshed. ReSpec and Bikeshed carry structural metadata that affects
normativity, references, generated IDs, and informative sections. The importer
must preserve raw source and build-oriented markup before interpreting rendered
HTML. A browser adapter should pin both specification and test-suite revisions.

WPT has a canonical manifest and multiple test forms. The manifest is an
inventory and execution-discovery source; it is not itself a clause-to-test
coverage oracle. A separate binding ledger must connect source clauses to WPT
cases and record unsupported or missing coverage.

Primary sources:

- [WHATWG HTML source](https://github.com/whatwg/html/blob/main/source)
- [Web Platform Tests](https://github.com/web-platform-tests/wpt)
- [WPT manifest command](https://web-platform-tests.org/running-tests/command-line-arguments.html)
- [Bikeshed](https://speced.github.io/bikeshed/)
- [ReSpec](https://respec.org/docs/)

### RFCXML, grammar, and registries

RFCXML v3 is the preferred authoring form and canonical published-RFC format.
The live vocabulary reference explicitly supersedes RFC 7991, so an adapter
must pin the retrieved vocabulary/schema rather than hard-code RFC 7991 as the
current authority. Definitive published XML and author/prep-tool XML must remain
distinguishable.

ABNF uses RFC 5234 plus RFC 7405 case-sensitive string updates. IANA registries
should be imported from their machine-readable resources with registry identity
and retrieval hash retained.

Primary sources:

- [RFCXML vocabulary](https://authors.ietf.org/rfcxml-vocabulary)
- [RFCXML overview](https://authors.ietf.org/rfcxml-overview)
- [RFC 9720](https://www.rfc-editor.org/info/rfc9720)
- [RFC 9920](https://www.rfc-editor.org/info/rfc9920)
- [RFC 5234](https://www.rfc-editor.org/info/rfc5234)
- [RFC 7405](https://www.rfc-editor.org/info/rfc7405)
- [IANA protocol registries](https://www.iana.org/protocols)

### Structured API and schema formats

OpenAPI 3.2.0 states that specification prose is normative and its published
JSON Schema is informational. Therefore schema validation is a strong oracle
for structure but cannot replace normative-clause extraction. JSON/YAML source
order, comments where representable, references, dialect, version, and unknown
extension fields must survive import.

AsyncAPI 3.1.0 is a protocol-agnostic JSON/YAML specification with reference
objects and multiple schema formats. JSON Schema needs explicit vocabulary and
dialect registration rather than a generic keyword parser.

Primary sources:

- [OpenAPI 3.2.0](https://spec.openapis.org/oas/v3.2.0.html)
- [OpenAPI schema status](https://spec.openapis.org/oas/)
- [JSON Schema specification links](https://json-schema.org/specification-links)
- [AsyncAPI 3.1.0](https://www.asyncapi.com/docs/reference/specification/v3.1.0)
- [AsyncAPI 3.1.0 release notes](https://www.asyncapi.com/blog/release-notes-3.1.0)

### Executable conformance suites

Official executable suites outrank tests synthesized from prose. Their native
metadata and harness semantics should map into `ConformanceCaseIR`; the importer
should not blindly translate every upstream test program into Simple.

openCypher TCK uses Cucumber/Gherkin scenarios and ordered steps, which makes it
a strong first executable-suite pilot. The repository also warns that project
content is experimental/unsupported while graph-query standardization evolves,
so imports must pin a commit and distinguish legacy openCypher grammar from
ISO/IEC 39075 GQL artifacts.

Test262 links directly from the ECMAScript specification and carries harness
and per-test metadata. WPT, Test262, WebAssembly spec tests, Vulkan CTS, and
RISC-V architectural tests should remain runnable through upstream runners or
interoperability harnesses when native translation would weaken their oracle.

Primary sources:

- [openCypher repository](https://github.com/opencypher/openCypher)
- [openCypher TCK](https://github.com/opencypher/openCypher/tree/master/tck)
- [Cucumber Gherkin reference](https://cucumber.io/docs/gherkin/reference/)
- [ECMAScript specification](https://tc39.es/ecma262/)
- [Test262](https://github.com/tc39/test262)
- [WebAssembly specification](https://github.com/WebAssembly/spec)
- [RISC-V Architectural Certification Tests](https://github.com/riscv-non-isa/riscv-arch-test)

### Registers and bitfields

CMSIS-SVD 1.3.9 describes peripheral/register/field structure and arrays in
XML. SystemRDL 2.0 models register behavior for software, RTL, documentation,
and verification. Active IP-XACT is IEEE 1685-2022 and has broader packaging
semantics than registers alone; the initial adapter should accept only the
memory-map/register subset and fail closed on other or vendor constructs.

The normalized register model must separate numeric bit position from byte
order and preserve access effects, reset masks, arrays, aliases, enumerations,
reserved ranges, and provenance. Vendor device packs require per-source license
review even when their format is public.

Primary sources:

- [CMSIS-SVD 1.3.9 history](https://arm-software.github.io/CMSIS_5/SVD/html/svd_revisionHistory.html)
- [SystemRDL 2.0](https://www.accellera.org/downloads/standards/systemrdl)
- [IP-XACT standards](https://www.accellera.org/downloads/standards/ip-xact)
- [IEEE 1685-2022](https://standards.ieee.org/ieee/1685/10583/)

## Required shared contracts

### Immutable source and coverage

Every import records URI, version/edition, revision, raw bytes, SHA-256,
encoding/newlines, media type, license, and redistribution policy. Normalized
characters map to raw byte ranges. The verifier proves the disjoint accounting:

```text
parsed + passthrough + mapped rewrite + excluded + malformed = total bytes
```

Preprocessing is a hash-pinned overlay, never an in-place mutation. Display
rewrites retain original text, mapped span, deterministic rule ID, and reason.

### Tolerant, never silent

Shared parsers preserve malformed constructs as nested `ErrorNode` values with
raw spans, recover only at stable delimiters, retain partial semantic facts, and
emit adapter-rule diagnostics. Strict mode rejects recovery. Compatibility mode
accepts only recovery rules listed in the pinned manifest.

`skip`, `blocked`, `unsupported`, and `ignore` remain distinct. Runtime ignore
may be emitted, but the source ledger and manual still show the source clause.

### Semantic and conformance identity

Stable identity preference is upstream ID, registry identifier, structural
path, adapter semantic key, then content/neighborhood fingerprint. Normative
classification combines explicit structure, schemas, official cases, modal
language, algorithm structure, and adapter rules. Heuristic language never
becomes passing evidence without an approved oracle.

### Version differences

Diffs operate at raw, document, requirement, grammar/schema/API, conformance,
and generated-artifact layers. Register differences additionally classify
offset, width, range, signedness, access/reset/endian, enum, alias, reserved
range, array, and stride changes for source, binary, and behavioral impact.

## Recommended implementation sequence

1. Freeze shared source/IR/manifest/verifier contracts and reuse the repository
   structural parser contracts.
2. Prove raw snapshots, source maps, exact coverage, round trip, recovery,
   determinism, non-vacuity, deliberate-red behavior, and license policy.
3. Integrate one canonical SPipe/manual/source-ledger emitter.
4. Implement semantic/version and RegisterIR differences.
5. Pilot four distinct inputs: existing Simple Markdown, openCypher TCK,
   RFCXML plus ABNF, and CMSIS-SVD plus the NVMe CC overlay.
6. Only then parallelize broader web, language-suite, API/schema, document, and
   register adapters.

The detailed ownership and merge gates are in
`doc/03_plan/agent_tasks/spec_to_spipe.md`; the target architecture is in
`doc/04_architecture/app/spec_to_spipe.md`.

## Risks and rejected shortcuts

- Rendered HTML alone loses source/build metadata and exact lexical forms.
- A MUST search misses structural norms and creates false tests.
- Schema validation alone does not prove all normative OpenAPI behavior.
- A WPT manifest alone does not prove clause coverage.
- Re-serializing a conventional DOM does not prove byte preservation.
- Passing generated placeholders or source-grep assertions are not conformance.
- “Latest” living-standard imports are not reproducible without a commit.
- Committing complete proprietary standards can violate redistribution terms.
- A Rust/C/Python bootstrap oracle cannot replace the pure-Simple canonical
  importer or self-hosted validation lane.

## Research disposition

The architecture and phased plan are supported. Implementation remains a
follow-on roadmap: no adapter or full lossless importer is claimed complete by
this research document.

