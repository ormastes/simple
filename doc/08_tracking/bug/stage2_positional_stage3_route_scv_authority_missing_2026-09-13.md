# Stage 2 passes sanity, then fails the positional pure-Simple Stage-3 route with `scv-authority-missing`

- Status: OPEN (2026-09-13) — **site 6**, the blocker immediately after site 5
- Found: bootstrap lane BOOT-6, `work/bootstrap-full-4-2026-09-12` at `b5e0c16549f`
- Severity: **the current `--stop-after-stage2` admission blocker on Linux aarch64.**
  Unlike sites 1-5 it is NOT a compile defect: the compiler compiles.

## The verdict, verbatim

Stage-2 sanity is now green — this is the first PASS in the BOOT-3/4/5/6 chain:

```
status=pass
frontend_smoke_status=0
frontend_smoke_bootstrap0_raw_status=0
frontend_smoke_bootstrap1_ran=true
frontend_smoke_bootstrap1_raw_status=0
frontend_smoke_bootstrap_mode_status=0
sha_stable_status=0
checks_run=5
```

The run still stops, one step later:

```
bootstrap_stage2_struct_receiver=PASS
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
[ERROR] phase 1 FAILED
error: in-process native-build: persistent package index admission failed:
       scv-authority-missing; run explicit cold initialization with
       SIMPLE_PACKAGE_INDEX_COLD_INIT=1
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Note what is different from site 5's shape: the failure is named plainly by the
receiver log, and the harness's own diagnosis step correctly reports `stage
stage2 failed (exit 3) and said why`. Nothing is masked here.

Candidate preserved at
`build/bootstrap-boot6a/stage2-rejected/aarch64-unknown-linux-gnu/simple`,
sha256 `0a9f6e5fe803bc0743cfe833...`, 152199008 bytes.

## Where it comes from

`src/compiler/80.driver/cache/package_index_route.spl:100-103`:

```
if (snapshot_root == "" or expected_revision == "" or
        expected_tree == "" or expected_inventory == ""):
    return PackageIndexRouteV1(false, "scv-authority-missing", [], [], [], [])
```

So at least one of `snapshot_root` / `expected_revision` / `expected_tree` /
`expected_inventory` reaches this frame EMPTY in the Stage-3-route child. The
reason string deliberately does not say which of the four, and there is no trace
that narrows it — that is the first thing to add.

Two things worth checking before theorising, in this order:

1. Whether the Stage-3-route child is launched with `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`
   at all. The error text recommends exactly that variable, and BOOT-5's and
   BOOT-6's hand-run probes DID set it (`disc5.sh`, `disc6.sh`), which is
   plausibly why neither ever saw this failure outside the harness.
2. Whether one of those four inputs is empty for a real reason (never produced
   by this run) or is a lost binding — this lane has just proven that this
   binary's codegen loses payloads bound by a pattern match
   (`result_bound_text_payload_lost_in_stage2_native_codegen_2026-09-13.md`),
   and four empty texts arriving together is exactly that shape. Distinguish by
   printing the four lengths at the call site, not by argument.

## Relationship to site 5

`stage2_sanity_bootstrap1_backend_object_path_status_1_2026-09-13.md` is FIXED
and this record is the proof: with the publish fix in, BOTH sanity passes are
green and the run advances past sanity for the first time. This is forward
progress, measured, not claimed.
