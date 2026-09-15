# Stage 2 passes sanity, then fails the positional pure-Simple Stage-3 route with `scv-authority-missing`

- Status: **CLOSED / FIXED (2026-09-13, proven by BOOT-7)** — `check-bootstrap-stage2-struct-receiver.shs` exports `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` next to its fresh per-probe `SIMPLE_NATIVE_BUILD_CACHE_DIR`. The proof is BOOT-7's full `--stop-after-stage2` run (`build/bootstrap-boot7a`, 06:00:22-06:48:59, candidate sha256 `3ad6fc2a0ac80727...`): `scv-authority-missing` appears **nowhere** in any log of that run, and the positional Stage-3 route now advances past package-index admission into phase 2 of the in-process native build, where it fails for an unrelated reason tracked as site 7 (`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md`).
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

1. **MEASURED, and the answer is no.** The child is launched by
   `scripts/check/check-bootstrap-stage2-struct-receiver.shs` (the `error:
   stage2 failed the positional pure-Simple Stage-3 route` line is its :166).
   `grep -c SIMPLE_PACKAGE_INDEX_COLD_INIT` on that file is **0** — the variable
   the error text itself recommends appears nowhere in it — while the same env
   block DOES set `SIMPLE_NATIVE_BUILD_CACHE_DIR="$stage2_probe_dir/stage3-route-cache"`,
   a FRESH directory, so nothing is warm and no index has ever been collected
   there. Both BOOT-5's `disc5.sh` and BOOT-6's `disc6.sh` set
   `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, which is why neither lane ever saw this
   failure outside the harness.

   This is the shape of `621a4d6b2ab` ("give Stage 2 a PATH so it can find
   llc") exactly: a child under a curated env list that lacks one name it needs.
   Adding the variable is NOT done here — out of this lane's scope, and it
   should be established first whether cold init is the right answer or whether
   the four empty inputs have an independent cause (check 2 below).
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
