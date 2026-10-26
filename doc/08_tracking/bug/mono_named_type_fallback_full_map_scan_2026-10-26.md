# Monomorphization named-type fallback repeatedly scans all declarations

Status: OPEN — source optimization passes narrow semantics regression; native performance validation pending.

The unchanged recovery03 worker18034 sample at roughly11m20 reports1428/2226
samples in `MonomorphizationPass.named_type_name_in` and538 in `str_ends_with`.
Evidence: review workspace
`build/verify/provisional-p3-minimal-cli-ssa-guard-recovery-20261026-03/logs/worker-18034-post-hir.sample.txt`.
This is a CPU profile observation, not a benchmark proving a speedup or a
memory-limit violation. The active source/producer/cache remains unchanged.

On an exact module+symbol miss the old fallback allocates the complete
`named_symbol_names.keys()` list, suffix-checks every key, and counts name
transitions for matching symbol IDs. Repeated misses therefore repeatedly
walk every declared type, although only one symbol-ID suffix is relevant.

The draft adds a pass-local derived suffix-to-qualified-keys index. The first
fallback builds it once; key-count growth invalidates it. Warm fallback reads
only the matching bucket and obtains values from the authoritative map, so
same-key name updates do not stale a cached name. Bucket order follows the
original dictionary traversal, preserving ambiguity and unusual empty-name
transition behavior. Exact module lookup remains first and does not build the
index. No ordering, type owner or mangling policy changes are intended.

Owned writer audit includes regular record_named_type, archive registration
scratch-copy and fact-row replay, plus archive scratch-pass whole-map restore.
Scratch collectors start with an invalid index; whole-map assignment explicitly
resets the derived state even if replacement size matches. No owned deletion
or remove/clear path was found. Any future same-size key replacement/deletion
must explicitly invalidate this index; count alone cannot detect that mutation.
Manual fixtures that seed maps before first use and append/update afterward
are supported. The index is neither serialized nor transported in archive
facts, nor included in the archive digest/receipt schema.

Expected work changes from a global declaration scan on every fallback to one
index build per key-set size plus the matching symbol-ID bucket per query.
The source profile motivates the change; a later exact native run must measure
its actual effect. No Rust/runtime/P2 rebuild is part of this fix.

The narrow semantics regression covers exact local priority, same-name providers,
ambiguity/absence, unrelated-ID exclusion, live overwrite, map growth,
same-size replacement invalidation, empty/noncanonical-key compatibility,
archive scratch-pass hydration and registration scratch-copy. Existing pending
performance PRs4825(SSA),4798(SCV),4764(HIR cache),4761(MIR promotion) address
other paths. Pending monoPR4820 has no named-type lookup edits.

Validation2026-10-26: retained-gen13 interpreter, canonical transcribed guard,
correct root-relative `test/01_unit/compiler/mono/named_type_suffix_index_spec.spl`:
10total10passed0failed0skipped0dropped; completeexit0, quiescent1, enforced
3145728KiB cap, peak999712KiB. Exact source/spec/seed/runtime hashes matched
before/after. Evidence is retained in review workspace
`build/verify/mono-named-type-suffix-index-20261026-01/`.
Astra reviewed the exact source/test before this sole run. These results verify
behavior, not a measured native speedup or current retained-P2 producer change.
The new fields preserve existing field prefixes but change aggregate size;
no ABI stability or full native qualification is claimed.

## release_phase3 backport — 2026-10-26

Donor: merged release/1.0.0 PR4856 at
`3e9a648dcf896a51c5a1c5486b458aaaa4ab81f2`. Target starts at
`eea6ec3fcf46060676904a837947557d4fdf89b5`.
The bounded target lookup/writer review found no equivalent suffix index.
The only three-way conflict was adjacent release-only module-scoped fields;
those unrelated fields were excluded, retaining the target layout and adding
only the two derived index fields. Other target mono logic remains intact.

Owned named-symbol writers append or update values; archive scratch hydration's
whole-map assignment resets the index. Registration creates a fresh scratch
collector before per-key copying. Same-key value updates read live values from
the original map. Bucket order retains the original dictionary traversal,
including its unusual empty-name transition rule. Index lifetime is pass-local;
it adds key references/bucket arrays, rebuild allocations on map growth, and two
aggregate fields. No ABI or memory reduction is inferred from field prefixes.

The ten donor cases are retained byte-for-byte. The donor PR reports one
retained-gen13 run on source9894ac22de1:10/10, exit0/quiescent1, cap3145728KiB,
peak999712KiB. Its relative evidence location above does not identify a complete
portable producer/runtime/tool hash receipt in this checkout. Those historical
results are attributed donor evidence, not independently recertified here and
not a run on this adapted phase3 source. All current compiler checks, SSpecs,
optimizer CLI and paired p50/p95 wall/RSS measurements remain UNRUN without a
qualified general self-hosted runner. No seed fallback or heavy jobs were used.
This is an early source backport only, not measured optimization acceptance.
Live83be/8cd source/cache/build ownership is unchanged.
