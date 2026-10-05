# Seed global interface cache rebuild latency

Status: OPEN performance limitation; no cache correctness weakening proposed.
Related: native_object_cache_ignores_dependency_interface_change_2026-08-17.
This report distinguishes the Rust seed's conservative global key from that
older report's destructive shell cache wipe and under-invalidation fixture.

## Observed live evidence

Packet: runtime/windows-restart-20261004/p2-singlethread60cd7f-cranelift20.
Source60cd7f90105f2083a050f68e66439eb1559768ba; Rust seed283f863a490d0d6a1359deaefc6506a0023c3357ef079537830fcca63333572f,
recorded producer sourceabfb80f901cb8b15ab5bc6f686603dde39eb2006.
The request enables incremental compilation,20threads, default cache lane,
and reuses C:/dev/simple-p2-composite-cache-cranelift-20261004 without cleaning.

The active existing namespace is scope-f7f1c2ce9c436bcf. Its marker was written
2026-10-05T07:06:16Z. The preceding completed manifest remains dated06:08:09Z:

    producer=371bcda62ebdc342;opt=a4c3de9a99718523;ec=44bc103b1f8540ed;t=ff635c52df03f32d;ls=0000000000000000;layout=960e72fec46e3702;instr=558f3fd350ea8cef

Read-only bounded enumeration found3476 then3499object files in that namespace,
with current object publication at07:33:50Z. A subsequent UTC-ticks comparison
found1153 .o files written since the active process start07:05:33Z. These are
new or rewritten object publications, not1153 asserted cache misses. At the
process observation PID24932 had32734.421875CPU seconds and1066954752RSS bytes.
No final incremental receipt was present. Exact hit/miss totals and the new
manifest comparison remain PENDING; do not report zero hits from inference.

No frontend or hir directory exists directly beneath this cache root. A bounded
search of the Rust driver/compiler source found no SIMPLE_FRONTEND_CACHE or
SIMPLE_HIR_CACHE readers. The packet explicitly selects SIMPLE_NATIVE_BUILD_RUST=1;
exporting the pure-Simple frontend/HIR switches does not implement persistence
in this seed path. Object publications prove the current delay is not solely
frontend preparation before cache lookup.

## Source mechanism (exact producer revision abfb80f901)

src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:

-1736 and1785: executable-byte fingerprint plus lane select the scope directory.
  Source root/output root/thread count are not namespace inputs.
-1068: the complete import map is rebuilt before object lookup.
-1246: every eligible object key combines its local source/codegen key with
  the global build fingerprint.
-1944,1948,1951: global layout fingerprint includes all function arities,
  method defaults and function return types, in addition to shared layouts,
  enum identities, imports and symbol resolution inputs.
-1404-1417: changed-component diagnosis and hit/rebuild receipt occur after
  dirty-module compilation, explaining the missing live reason/counts.

The source81bfe2-to60cd7f delta adds native_build_hir_shard_policy_v1 and two
record-owner methods. Therefore broad global-interface invalidation is the
source-supported explanation for extensive recompilation; the exact new
fingerprint/reason must still be confirmed from the terminal manifest/receipt.
The old namespace is preserved, not bypassed by a new source-directory scope.

## Minimal future improvement and safety gate

First expose the already computed dirty-set count and changed fingerprint
component before compilation (existing native-rust trace contains the dirty
set). This improves diagnosis without changing cache identities. Future packet
tracing can enable that existing diagnostic; do not restart this live build.

Reducing rebuild work requires dependency-safe per-module interface fingerprints
including actual imported layouts, overload/name-resolution sets, defaults,
traits and enum identities. Merely removing signatures from the global key is
unsafe. Persisting frontend/import metadata is a separate design, not provided
by the current environment flags. No such redesign is selected or implemented.

Regression requirements: unchanged repeat reuses eligible objects; unrelated
private body change rebuilds only affected objects; imported signature, field
layout, enum, trait/default changes invalidate all actual dependents; adding an
ambiguous resolution candidate invalidates consumers. Compare native outputs,
peak RSS and elapsed/CPU time. These new qualification cases are UNRUN.
