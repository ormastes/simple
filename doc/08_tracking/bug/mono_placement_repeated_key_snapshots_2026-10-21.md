# Monomorphization placement repeats a fixed specialization-key snapshot — 2026-10-21

**Status:** SOURCE FIX CANDIDATE / EXECUTABLE QUALIFICATION PENDING

**DB registration:** PENDING. No admitted runtime was available to execute
`bin/simple bug-add`; this source report is the retained record.

## Reproduction and observation

At source `55ba9dc6dbea8db49a81dfc7fdc9274efc68a8df`, inspect
`src/compiler/40.mono/monomorphize_integration.spl`, `process_modules`, final
placement loop. `self.specialized_functions.keys()` runs once per module even
though `drain_worklist()` has already completed and placement does not mutate
that dictionary. Several logical module keys can alias the same physical owner.

For M modules reaching placement and S finalized specializations, this performs
M key snapshots and copies M*S key entries. One shared post-drain inventory
reduces that particular operation to one snapshot and S copied entries.
These counts follow from the source loop; no allocator or RSS measurement was
performed. This report does not establish a leak or explain the entire build's
memory usage. Other inventories and retained HIR/dictionaries remain present.

## Candidate fix and invariants

Move only the typed `specialized_keys` declaration immediately before the final
module-placement loop, after the worklist fixed point and failure check.
Preserve module order, dictionary-key order, exact alias-membership tests,
callable-symbol registration, symbol counters, template pruning, and rewritten
table removal. No deep frees, dictionary clearing, sorting, or rebucketing.

The production beforeimage SHA256 is
`83f01ae8b0e3133cfb2bbbdb4194de169f872f041fc98ec9c74fea61ddfff4bc`;
the candidate SHA256 is
`7af5f8d691e851769862f33739ef32d45c4d4bf7c2f70484d5cfdcd0e4dd5ec0`.
Observed release `380200890ff030b34c68ff38f362b482e1276769` has the same
production beforeimage. This identifies source applicability, not runtime lineage.

## Verification required before closure

The existing `test/01_unit/compiler/mono/mono_specialization_owner_spec.spl`
is extended with real `process_modules` fixtures covering deferred worklist
discovery, multiple instances/modules, physical aliases, negative owners, exact
placement order, symbol rows/counters, pruning, zero requests, and zero modules.
Executable tests are UNRUN. Source whitespace and isolated release-index patch
applicability checks passed; those do not establish semantic qualification.

The build owner must run the focused spec and relevant mono regression specs
on an admitted full checkout, pin runtime path/hash/stage/provenance, and retain
results before closure. Measure allocations or RSS separately before claiming
an observed memory improvement. No new bootstrap was started for this report.
