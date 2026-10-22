# Generated SCV snapshots rediscovered as workaround source owners

Canonical bug: `scv_generated_snapshot_workaround_discovery_2026_10_13`.
Bug DB reconciliation is pending a qualified writer. This report does not
manufacture database state or qualify a native performance repair.

The retained f2 Phase4 web attempt ended with exit 1 and no executable after
579.903 seconds. Its first workaround-refresh diagnostic names an old generated
file under `build/scv/snapshots/`. Subsequent source loading independently failed
because that attempt's input capsule lacked `os.crypto.aes128_gcm`. The missing
dependency is an input-closure problem, not an unsupported-host classification.

After termination, Git status contained 40,832 paths. The existing workaround
source predicate accepted 27,611 generated snapshot paths: 13,807 from the old
snapshot and 13,804 from the new one. Neither examined snapshot inventory had
nested `build` rows. These observations establish generated-source discovery,
not nested snapshot copying, and are not start-time counts or latency attribution.
The recorded inner compiler-driver span was approximately 2.046 seconds; the
whole preceding delay has not been attributed to this bug alone.

`workaround_status_paths` checks duplicate destinations and rename/copy sources
with repeated array membership scans. The proposed repair uses the same
first-seen dictionary idiom already present in `workaround_tracked_paths` and
excludes only the repository-relative reserved `build/scv/snapshots/` namespace.
An absolute path containing `build` must not disqualify legitimate project
sources. Malformed paths remain errors before namespace filtering.

The authentic baseline regression executed one assertion against the full real
owner and failed as expected: one case, zero passes, one failure. The collector
and native command exited 1, with final Job membership zero, unchanged pins,
617 confined source reads, and no outside reads. Its 4.394-second harness wall
time and 238,032-KiB sampled peak do not measure native build improvement.

Evidence: `build/native_probe/workaround-snapshot-discovery-20261012/` contains
the sealed original owner, private candidate diff, tests, provenance and baseline
receipt. The candidate passed six focused cases with 23 actual assertions against
the full owner, with 617 confined source reads, no outside reads, unchanged pins,
exit 0 and final Job membership zero. It is applied locally, including the
regression spec. Assertions cover exact namespace boundaries, both rename sides,
stable first occurrence, invalid/truncated NUL records, unsafe rename sources
and a larger authored-path batch. The candidate harness took 5.743 seconds with
a sampled peak of 238,444 KiB. The unequal baseline and candidate suites do not
establish a native speed or RSS improvement. Native correctness, latency and
memory qualification remain pending; no production performance repair is
promoted by this report. Source application is recorded in
`build/native_probe/workaround-snapshot-discovery-20261012/ROOT_SOURCE_APPLIED.json`.

Persisted-index limitation: preparation also visits existing index links without
the source-candidate filter. A historical generated link requires a qualified
fullscan/index migration; the proposed discovery change alone does not prove it
is removed. The actual failing Phase4 capsule's 153-byte index contained no such
link, so this limitation does not invalidate the retained reproducer. Preserve
transaction and ownership checks when repairing the migration separately.
