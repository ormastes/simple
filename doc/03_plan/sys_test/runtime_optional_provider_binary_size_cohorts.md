# Runtime Optional-Provider Binary-Size Cohort Test Plan

## Scope

- Require an admitted pure-Simple Stage4 receipt; old seed results are diagnostic only.
- Compare release-small NoGC hello with a same-host, same-toolchain C hello using the same required startup wrapper, runtime archive, linker options, section GC, and strip policy.
- Require the C entry to call `puts` for the same stdout bytes and bind the expected stdout to the cohort receipt.
- Compare checksum-equivalent Simple and Python interpreter startup and max RSS using a separate interpreter binary identity.
- Require empty collector/init and optional-provider load traces.
- Require 30 samples per lane for development and 100 for release.

## Static and Mutation Evidence

`test/01_unit/scripts/runtime_binary_size_startup_cohort_test.shs` proves the
clean evidence path and rejects collector retention, provider loading,
pre-Stage4/seed authority, insufficient samples, binary drift, and captured
link evidence tampering, expected stdout drift, and interpreter/sample-binary hash drift without running heavy
cohorts. On Linux it creates a real LLD reproduction archive and the BS7
checker replays both links.

## Native Evidence

`test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl` runs
the production checker's clean and mutation-red fixture and checks fail-closed
behavior when admission inputs are missing. Those executable examples use
synthetic Stage4/startup receipts and establish checker behavior only. A release
PASS still requires retained Stage4-native cohort receipts. The shell fixture
passed before the final C `puts` source switch; that latest source awaits the
next bounded mutation run. A direct Stage4 SPipe attempt stopped at flat AST declaration
parse errors in reached library files before either example ran, so the SPipe
wrapper still has no executed PASS.

## Literal-print qualification

| Requirement | Evidence | Acceptance |
| --- | --- | --- |
| NFR-002, REQ-014 | Admitted current-source Stage4 hello output, unstripped retained-section map, captured LLD archive/receipt, stripped ELF, paired replayed C `puts` ELF, BS7 receipt | Exact `hello` output; no literal boxing/formatting/cache retention; only the program object differs in the C link; Simple <=15,360 bytes and <=105% of matched-startup C |
| NFR-004, NFR-007 | Same-host Simple/Python startup and RSS samples | 30 development or 100 release samples per lane; BS7 p50/p95 and RSS gates pass |
| NFR-005, REQ-007 | NoGC inventory and optional-provider trace | Both inventories empty |

The 5,152-byte direct-writer C probe is a runtime-path diagnostic. It cannot
replace a Stage4 Simple binary in any row. Do not mark this plan PASS until
the current-source compiler, exact link closure, and paired cohort are
admitted. The applicable scenarios and manual are
`test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl` and
`doc/06_spec/05_perf/compiler/runtime_optional_provider_binary_size_spec.md`.
