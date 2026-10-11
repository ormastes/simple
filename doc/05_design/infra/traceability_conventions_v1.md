# Snapshot-bound conventional association resolution

Status: component implemented; native26/0 and Astra scoped review PASS. Full qualification WARN. All20REQ/40AC/WP0–WP7 remain required. Authority:
report7.1–7.2,6.3,10.1–10.3. This is the pure WP2 conventional kernel, not an
extractor, authenticated policy loader, incremental cache, override evaluator,
CLI integration or completed AC003/005/006. No arbitrary prose or imports prove
test ownership or execution. Conventional links confer structural association.

## Inputs and owners

The kernel receives existing bounded TraceGraphV1 facts, typed policy id/version,
registered mapping rules, explicit scoped exclusions and supplied generator-manifest bindings. Both snapshot and input
manifest must be complete. Policy id/version must match graph manifest identities.
These are supplied facts, not authentication; the future trusted owner must bind
and authenticate them before admission. The result never confers eligibility.

Rules: id, group_id, kind, source_root, target_root, source_suffix, target_suffix.
Registered roots are repository-relative directory prefixes ending in slash;
suffixes are nonempty UTF8 filename suffixes without slash/NUL. Preserve exact
bytes/case/Unicode. Slice only matched root/suffix boundaries. No basename search,
numeric-prefix stripping, new-root exclusion or heuristic nearest match.

| kind | logical source | recognized target | semantic claims |
|---|---|---|---|
| unit | source_file with file locator | one test_suite artifact containing unit definitions at that path | each unit definition targets source_file |
| integration | component with manifest/file locator | one test_suite with integration definitions | each integration definition targets component |
| component | component with manifest/file locator | one test_suite with component definitions | each component definition targets component |
| manual | test_suite with file locator | one generated_document with file locator and exactly one matching generator-manifest binding | generated_document generated_from test_suite |

A test definition is recognized here only from the validated typed registry plus
scenario locator and its actual test_kind; no test content is parsed by this
kernel. Actual extraction/byte binding remains required. Acceptance definitions
are never relabeled unit/supporting. Parameter identities remain distinct and
inherit validated roles. Several cases in one suite are one candidate artifact;
emit their separate associations without executing or counting them as coverage.
Layout/companion-document mappings and policy wire contracts remain required
future work, not silently approximated by these four kinds.

One group has one kind. All matching rules in that group are alternatives for
the same source association. Count distinct recognized target paths across them.
Zero produces a missing/unrecognized diagnostic; two or more produce ambiguity
and no claims for that group. Several rules corroborating the same unique target
retain each rule origin. Do not pick the first candidate. Two same-kind artifact
identities at one path or multiple source file locators produce ambiguity rather
than identity selection. Independent groups may add distinct structural links.

Exclusions: group_id, root, reason. Group must exist, root is canonical and reason
nonempty. Explicit source exclusion can remove that group's expectation; retain
an exclusion dependency. An excluded target is not recognized as an alternative.
Source facts with no applicable registered mapping or exclusion produce a visible
unregistered diagnostic. There is no implicit vendor/new-root skip in the kernel.

## Output and dependency records

TraceConventionResolutionV1 binds snapshot_id/input_set_id/policy_id/rules_version
and contains claims, diagnostics and lookups. Claim: from_id, relation, to_id,
rule_id, source_path, target_path. Diagnostic: reuse TraceDiagnosticV1 with exact
snapshot/rule/entity/path, no fabricated source span; deterministic repair text.
Evaluation complete means the bounded inventory was fully evaluated, even with
semantic violations. It is not qualification or authenticated admission.

Lookup: kind, entity_id, group_id, rule_id, path, found, candidate_ids. Keep
artifact membership (including conflicts), role-qualified definition membership,
exact positive/negative expected-target queries, mapping-group membership and
exclusion queries. Full input-set/rule identities bind them. Creating a formerly
missing candidate or a second alternative changes those records. Actual cache
invalidation and incremental/full equality still require WP3 implementation.

## Budgets and deterministic processing

First validate all hard limits and preflight graph records/text through its
existing owner. Policy rules/exclusions have bounded counts and text/field bytes.
Bound the conservative node-count × rule-count work before graph/index allocation;
also charge actual rule checks, candidate expansion and case emission. Never
return partial Ok after resource exhaustion. Defaults: rules256, exclusions4096,
work100000, claims/diagnostics/lookups100000 each, policy/result text1MiB and
fields4096. Hard maxima: rules4096, exclusions65536, work100M, records1M,
policy/result text16MiB, fields1MiB; graph retains its own strict/codec limits.

After preflight, validate graph semantics once and build path/kind, role/scenario
and identity indexes once. Deduplicate locator associations by indexed identity,
not quadratic scans. Inner checks consult those indexes; never rescan graph
nodes, definitions or locators for each rule. A constant validation plus indexing
pass is intentional. Local temporary candidates are bounded by rules/work.
Result count and text charges precede result key/message allocation and append.
Sort complete claim/diagnostic/lookup records by shared explicit byte-order owner;
candidate IDs are sorted/deduplicated. No ambient IO, process, clock or cache.
Realistic fixture timing/RSS and full selected NFRs remain unqualified.

## TDD and review

Write executable source before mapping logic. This new public API has no prior
runtime dispatch seam: an actual native-construction failure for its missing
module is construction RED, not assertion RED or executed examples. Retain that
failure and do not insert a production dummy to fabricate runtime counts.
Then run real modern SSpec payload/diagnostic/dependency assertions against the
implemented kernel. Include unique/missing/second candidate, wrong role/identity,
corroboration, exact roots/Unicode, registered exclusions, policy mismatch,
incomplete inventory, budgets and deterministic input permutations. Astra reviews
design, source/oracles and frozen logs. No unchanged green specs are rerun.

## Generator manifests and closed dependencies (Astra design correction)

Manual derivation also requires a supplied `TraceConventionGeneratorBindingV1`: id, suite_id, document_id, rule_id, generator_id, manifest_path and manifest_sha256. The referenced rule must be manual; endpoints must be an existing test_suite/generated_document; the manifest path must name a captured policy input with exactly the declared SHA256. These facts remain untrusted data and do not authenticate a generator or prove execution. Zero matching bindings produces `missing_generator_binding`; several distinct bindings produce `ambiguous_generator_binding`; neither emits a claim. Missing or contradictory references refuse the supplied input. Bindings are indexed once by rule/suite/document.

Rule IDs and binding IDs are unique. Lookup kinds are closed: source, artifact, role, target, group, exclusion, generator_binding and generator_manifest. Artifact membership and role-qualified case membership are separate so a present suite with no matching unit/integration/component definitions remains a negative role query. Candidate IDs are sorted, deduplicated and charged for count, field/text bytes and work before copying or sorting. Exclusion checks, candidate expansion and generator binding queries charge the same bounded work owner. Binding count defaults4096/hard65536.

## Registered domains and reviewed evaluation order

A policy selects whole source-kind domains: unit groups evaluate source_file facts; integration/component groups evaluate component facts; manual groups evaluate test_suite facts. A unit-only policy does not impose manual obligations on its target suites. Within each selected domain every unregistered root remains visible, including vendor and newly numbered roots, unless an explicit registered exclusion applies. The full feature must validate its complete policy domains separately; this component does not make eligibility claims.

One policy index maps source kinds to their groups, and groups to their rules. No per-node scan of every group occurs. Logical work includes index rows, every node traversal, selected group traversal, rule checks, exclusion checks, candidate ID expansion, generator queries and claim/diagnostic emission. The conservative preflight reserves index rows plus nodes plus twice nodes×rules. Actual charges may refuse additional candidate/output work; no partial Ok is returned. On the minimal unit fixture, exactly28 logical units pass and27 refuse.

Generator membership is queried for every non-excluded, role-qualified manual artifact before alternative cardinality. An unbound lookalike retains a negative binding lookup and diagnostic, but cannot make a valid bound alternative ambiguous. Two bound paths or conflicting identities/bindings refuse selection. Artifact and role membership remain independent: a wrong-role artifact is present while its target query is negative. Exclusion candidate identities are exact registered roots within the supplied lookup group, not graph-node IDs. Lookup construction, including duplicates, conservatively charges attempted work/text before deduplication.

Graph preflight occurs before policy/graph indexes; its semantic validator invokes the same preflight again as a constant validation pass. This is bounded in-memory validation, not repeated filesystem scanning. Generator fields are supplied manifest-derived facts; the future extractor must establish their actual byte semantics and trusted policy owner must authenticate them. Matching a declared digest alone establishes neither of those prerequisites.
