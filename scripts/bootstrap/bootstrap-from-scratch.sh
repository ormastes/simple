#!/bin/sh

# THIS SCRIPT IS THE ONLY SANCTIONED WAY TO RUN THE BOOTSTRAP STAGES.
#
#   Do NOT hand-type the stage native-build lines below. Between 2026-08-22 and
#   2026-08-23 roughly 26 runs were driven by a hand-typed
#   `native-build --source src/app --entry-closure --entry
#   src/app/cli/bootstrap_main.spl`, mislabelled "phase 1". All were unusable:
#   with no --cache-dir the cache could not hit (SIMPLE_CACHE_SCOPE has nothing
#   to partition; 23,718 log lines, zero cache hits), and with only one --source
#   root the run livelocked (counter frozen at 389/688 for 2,700s;
#   module_surface_registry_index.spl parsed 73 times) and was misread as
#   slowness. Every flag on the Stage-2/Stage-3 invocations is load-bearing.
#
#   PHASE 1 IS NOT A NATIVE-BUILD. Phase 1 is the Rust seed, built by cargo
#   (--profile bootstrap) and preserved as the phase-1 lineage snapshot. The
#   FIRST native-build of the whole bootstrap is STAGE 2. A command containing
#   `native-build` is Stage 2 or later, by definition.
#
#   --strategy=adhoc is a FAILURE POLICY (fail-fast), not a lighter build; see
#   the folded bootstrap-cache-policy library below. There is no reduced-closure
#   stage-1 path in this repo.
#
#   Running bare exits 64 with `reason-receipt-required`. That is not breakage:
#   use `--strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<dir>`
#   (the trust-root exception), or plan a receipt as the error message says.
#
#   Record: doc/08_tracking/bug/phase1_mislabelled_as_native_build_2026-08-23.md
#   Phase table: doc/07_guide/tooling/bootstrap_phase_verification.md
#   Guard: scripts/check/check-sanctioned-bootstrap-invocation.shs

# PHASE-GATING PRINCIPLE (authoritative doc:
# doc/07_guide/tooling/bootstrap_phase_verification.md)
#
#   Each phase's test gate exists to verify that the capabilities the NEXT phase
#   depends on are correctly implemented. It is a prerequisite check, not
#   exhaustive coverage, and it deliberately excludes optional / feature-surface
#   tests that no later phase consumes.
#
# Consequences for every gate invoked from this driver:
#   * the verdict line names counts AND scope, e.g.
#       PASS - N phase-gate spec(s) run, 0 failed (M out-of-scope deferred, see <record>)
#     so a reader can see it checked a subset and exactly which one;
#   * excluded-but-incomplete work is recorded as a TODO and explicitly disabled
#     or made to assert -- never left silently half-working;
#   * a gate that examined zero items reports ERROR, never PASS;
#   * optional-feature failures are held as TODOs, not fixed inside the phase:
#     disabled with a skip or an assert PLUS a TODO, recorded in the gate's scope
#     declaration -- never deleted, never anonymous in spec files. Skip is the
#     authorised mechanism for this case only; CLAUDE.md's prohibition on
#     skipping failing tests without approval governs everything else.
#
# COMPANION RULE -- rust simple (the Rust seed, src/compiler_rust/**):
#   Do not implement optional features unless requested, or needed to build
#   phase 2. The phase-2 exception requires a demonstrable phase-2 build failure
#   that the feature resolves; whoever invokes it records what broke. Simple is
#   the default implementation language (CLAUDE.md). The seed is bootstrap-only
#   tooling: every optional feature in it must be maintained in two languages and
#   eventually replicated on the self-hosted path, enlarging the very bootstrap
#   problem this driver exists to shrink. Applies to new work only.
#
# One sentence covering both: the bootstrap path contains exactly what the next
# step requires -- tests verify what the NEXT phase depends on, and the seed
# carries what the NEXT phase needs and nothing else.
#
# Measured scope at origin/main 2026-08-23 (do not re-derive): 21,228 spec files
# total; compiler/interpreter/loader scope 2,106 (test/01_unit/compiler 2,063 +
# test/02_integration/compiler 43 + test/01_unit/app/cli 69 +
# test/01_unit/app/compile 4). Stage-1 build closure is 689 modules of 15,221
# .spl files because --entry-closure follows imports from the entry, so
# --source src does not widen it beyond --source src/app. Categorically
# ineligible for any gate, in every tree: test/01_unit/bugs/, test/fixtures/,
# test/tmp_repro/.
#

# =============================================================================
# FOLDED HELPER LIBRARY AND SUBCOMMANDS
#
# scripts/bootstrap/ holds exactly two entrypoints: this POSIX script and
# bootstrap-windows.cmd. Everything that used to be a sibling helper script is
# folded in below and reachable as a SUBCOMMAND (first argument) or, for the
# pure function libraries, by sourcing this file with BOOTSTRAP_LIB_ONLY=1:
#
#   BOOTSTRAP_LIB_ONLY=1 . scripts/bootstrap/bootstrap-from-scratch.sh
#
# Subcommands (see `--help`):
#   preserve-phase-binary  progress-watch  planner-admission-v2
#   stage2-sanity-diagnostic  rollback-deploy  stage4-tooling-matrix
#   stage4-tools-only  resume-stage3  windows-entry
# =============================================================================

# --- folded: bootstrap-cache-policy.shs -------------------------------------
# Pure cache-policy predicates shared by the bootstrap wrapper and its tests.

bootstrap_cache_force_clear_one_binary() {
  cache_execution_profile=$1
  cache_bootstrap_mode=$2
  [ "${cache_bootstrap_mode}" = "one-binary" ] &&
    [ "${cache_execution_profile}" != "incremental-unlimited" ]
}

# Strategy validation is kept pure so the stage engine remains usable when the
# optional coordinated supervisor is unavailable.
bootstrap_strategy_validate() {
  case "$1" in
    adhoc|normal|full) return 0 ;;
    *) return 1 ;;
  esac
}

bootstrap_strategy_failure_policy() {
  case "$1" in
    adhoc) printf '%s\n' fail-fast ;;
    normal) printf '%s\n' phase-isolated ;;
    full) printf '%s\n' inventory-to-end ;;
    *) return 1 ;;
  esac
}

# --- folded: bootstrap-authority-wiring.shs ---------------------------------
# Production bootstrap authority wiring shared by bootstrap-from-scratch and
# focused behavioral tests. All mutation entrypoints require an owned lock.

# Fingerprint helpers use mktemp internally. Keep that scratch traffic on the
# bootstrap output filesystem: a full /tmp must not make an otherwise healthy
# authority build fail, and pre/post/commit observations must share one routing
# contract. On failure retain both a small machine-readable manifest and the
# helper's stderr without adding anything to successful fingerprint stdout.
bootstrap_authority_seed_inputs_fingerprint() {
  [ "$#" -eq 9 ] || return 64
  bootstrap_fingerprint_phase=$1
  bootstrap_fingerprint_tmp=$2
  bootstrap_fingerprint_manifest=$3
  bootstrap_fingerprint_error=$4
  shift 4
  case "${bootstrap_fingerprint_phase}" in
    pre|post|commit) ;;
    *) return 64 ;;
  esac
  mkdir -p "${bootstrap_fingerprint_tmp}" \
    "$(dirname -- "${bootstrap_fingerprint_manifest}")" || return 1
  bootstrap_fingerprint_error_pending="${bootstrap_fingerprint_error}.raw.$$"
  if TMPDIR="${bootstrap_fingerprint_tmp}" \
    bootstrap_stage3_seed_inputs_fingerprint "$@" \
      2>"${bootstrap_fingerprint_error_pending}"; then
    rm -f "${bootstrap_fingerprint_manifest}" \
      "${bootstrap_fingerprint_error}" \
      "${bootstrap_fingerprint_error_pending}"
    return 0
  else
    bootstrap_fingerprint_status=$?
  fi
  {
    printf 'phase=%s\n' "${bootstrap_fingerprint_phase}"
    cat "${bootstrap_fingerprint_error_pending}"
  } >"${bootstrap_fingerprint_error}.tmp.$$" &&
    mv -f "${bootstrap_fingerprint_error}.tmp.$$" \
      "${bootstrap_fingerprint_error}"
  rm -f "${bootstrap_fingerprint_error_pending}"
  {
    printf 'schema=simple-bootstrap-fingerprint-error-v1\n'
    printf 'phase=%s\n' "${bootstrap_fingerprint_phase}"
    printf 'status=%s\n' "${bootstrap_fingerprint_status}"
    printf 'tmpdir=%s\n' "${bootstrap_fingerprint_tmp}"
    printf 'error=%s\n' "${bootstrap_fingerprint_error}"
  } >"${bootstrap_fingerprint_manifest}.tmp.$$" &&
    mv -f "${bootstrap_fingerprint_manifest}.tmp.$$" \
      "${bootstrap_fingerprint_manifest}"
  return "${bootstrap_fingerprint_status}"
}

bootstrap_authority_require_owned_lock() {
  [ "$#" -eq 1 ] || return 64
  portable_lock_handle_is_owned "$1"
}

bootstrap_authority_materialize_legacy_file() {
  [ "$#" -eq 2 ] || return 64
  bootstrap_authority_handle=$1
  bootstrap_authority_file=$2
  bootstrap_authority_require_owned_lock "${bootstrap_authority_handle}" || return 77
  [ -L "${bootstrap_authority_file}" ] || return 0
  [ -f "${bootstrap_authority_file}" ] || return 1
  bootstrap_authority_materialized="${bootstrap_authority_file}.materialized.$$"
  cp -pL "${bootstrap_authority_file}" \
    "${bootstrap_authority_materialized}" || return 1
  mv -f "${bootstrap_authority_materialized}" \
    "${bootstrap_authority_file}"
}

bootstrap_authority_recover_or_refuse() {
  [ "$#" -eq 5 ] || return 64
  bootstrap_authority_full=$1
  bootstrap_authority_root=$2
  bootstrap_authority_marker=$3
  bootstrap_authority_compatibility=$4
  bootstrap_authority_handle=$5
  [ -e "${bootstrap_authority_marker}.transaction" ] || return 0
  [ "${bootstrap_authority_full}" -eq 1 ] || return 78
  bootstrap_authority_require_owned_lock "${bootstrap_authority_handle}" || return 77
  bootstrap_stage3_recover_seed_transaction "${bootstrap_authority_root}" \
    "${bootstrap_authority_marker}" "${bootstrap_authority_compatibility}"
}

bootstrap_authority_migrate_complete_legacy() {
  [ "$#" -eq 11 ] || return 64
  bootstrap_authority_legacy=$1
  bootstrap_authority_root=$2
  bootstrap_authority_marker=$3
  bootstrap_authority_compatibility=$4
  bootstrap_authority_inputs=$5
  bootstrap_authority_seed_name=$6
  bootstrap_authority_native_name=$7
  bootstrap_authority_backfill_name=$8
  bootstrap_authority_nonce=$9
  bootstrap_authority_handle=${10}
  bootstrap_authority_observed=${11}
  [ ! -e "${bootstrap_authority_marker}.transaction" ] || return 78
  [ ! -f "${bootstrap_authority_marker}" ] || return 0
  bootstrap_authority_require_owned_lock "${bootstrap_authority_handle}" || return 77
  bootstrap_stage3_verify_seed_stamp \
    "${bootstrap_authority_legacy}/${bootstrap_authority_seed_name}.inputs.sha256" \
    "${bootstrap_authority_inputs}" \
    "${bootstrap_authority_legacy}/${bootstrap_authority_seed_name}" \
    "${bootstrap_authority_legacy}/${bootstrap_authority_native_name}" \
    "${bootstrap_authority_legacy}/${bootstrap_authority_backfill_name}" || return 1
  bootstrap_stage3_prepare_seed_generation "${bootstrap_authority_legacy}" \
    "${bootstrap_authority_root}" "${bootstrap_authority_inputs}" \
    "${bootstrap_authority_seed_name}" "${bootstrap_authority_native_name}" \
    "${bootstrap_authority_backfill_name}" "${bootstrap_authority_nonce}" || return 1
  bootstrap_stage3_publish_seed_generation \
    "${BOOTSTRAP_STAGE3_PREPARED_STAGING}" \
    "${BOOTSTRAP_STAGE3_PREPARED_GENERATION}" "${bootstrap_authority_marker}" \
    "${bootstrap_authority_inputs}" "${BOOTSTRAP_STAGE3_PREPARED_HASH}" \
    "${bootstrap_authority_observed}" \
    "${bootstrap_authority_compatibility}" || return 1
  bootstrap_stage3_resolve_committed_seed "${bootstrap_authority_root}" \
    "${bootstrap_authority_marker}"
}

bootstrap_authority_pin_stage4() {
  [ "$#" -eq 4 ] || return 64
  bootstrap_stage3_pin_private_authority "$@" || return 1
  BOOTSTRAP_STAGE4_RUNTIME_PATH=${BOOTSTRAP_STAGE3_PRIVATE_RUNTIME}
  BOOTSTRAP_STAGE4_SEED=${BOOTSTRAP_STAGE3_PRIVATE_SEED}
  BOOTSTRAP_STAGE4_NATIVE_ALL=${BOOTSTRAP_STAGE3_PRIVATE_NATIVE_ALL}
  BOOTSTRAP_STAGE4_BACKFILL=${BOOTSTRAP_STAGE3_PRIVATE_BACKFILL}
}

# --- folded: native-cache-clear.shs -----------------------------------------
# native-cache-clear.shs — sourceable helper for clearing a native-build cache
# lane WITHOUT throwing away the content-keyed frontend parse cache.
#
# WHY THIS EXISTS
# `prepare_native_cache()` in scripts/bootstrap/bootstrap-from-scratch.sh wipes
# the whole lane dir (`build/bootstrap/native_cache/<lane>/`) whenever
# `bootstrap_wide_inputs_hash` moves. That dir contains `frontend/` (the
# per-module parse cache, src/compiler/10.frontend/frontend_parse_cache.spl) and
# `hir/`, so the wipe also destroys every `.fpc` entry. A build that dies late
# and is started again therefore reparses the entire closure from cold — the
# repeated ~4672s of work observed across run17's three attempts.
#
# WHY PRESERVING `frontend/` IS SOUND
# The frontend cache is independently and completely keyed; it does not rely on
# this directory being wiped for its correctness. An entry is only read back
# when BOTH match:
#   * the filename, which is sha256 of the module source bytes
#     (frontend_parse_cache_key), so a source edit cannot hit a stale entry; and
#   * the entry header, which folds FRONTEND_CACHE_ENTRY_VERSION,
#     FLAT_POOL_CODEC_VERSION and the driver-published scope key
#     (native_build_cache_scope_key = lane;backend;cpu;features;opt;compiler),
#     where `compiler` is native_build_compiler_identity() — the compiler
#     executable hash PLUS the src/compiler/** source fingerprint, the runtime
#     provider fingerprint and the runtime bundle.
# Every axis `bootstrap_wide_inputs_hash` protects (platform, backend, mode,
# seed inputs, src/compiler/** contents) is therefore already inside the entry
# header. A mismatch on any of them is a header mismatch, which the cache treats
# as a MISS that reparses — it fails closed by construction. Wiping the
# directory as well buys no additional safety and is exactly what makes a
# retried build start cold.
#
# WHAT IS NOT PRESERVED
# `hir/` and every object/scope dir are removed exactly as before. The HIR cache
# is keyed over a whole-closure digest and is owned by a different lane; this
# helper deliberately does not change its behaviour.
#
# Cross-lane isolation is untouched: this only ever operates INSIDE one
# already-selected per-lane directory, so one lane can still never see another
# lane's entries, and the `.cache_scope` ownership marker
# (scripts/check/check-cache-scope-ownership.shs) is re-stamped by the caller.
#
# Guarded by scripts/check/check-frontend-cache-survives-context-change.shs.

# Clear a native cache lane dir for a BUILD-CONTEXT change, keeping `frontend/`.
#
# Returns 0 when it cleared an existing directory, 2 when there was nothing to
# clear (missing/empty argument or absent directory) so a caller can tell
# "cleared" from "nothing was there" instead of reading a vacuous success.
native_cache_clear_context_change() {
    nccc_dir=$1
    [ -n "${nccc_dir}" ] || return 2
    [ -d "${nccc_dir}" ] || return 2
    for nccc_entry in "${nccc_dir}"/* "${nccc_dir}"/.[!.]*; do
        [ -e "${nccc_entry}" ] || continue
        case "${nccc_entry##*/}" in
            frontend) continue ;;
        esac
        rm -rf "${nccc_entry}" || return 1
    done
    return 0
}

# Full wipe, including `frontend/`. Used for the paths that express explicit
# operator intent to start from nothing (--fresh-cache, clean-release profile,
# one-binary mode), where honouring the request matters more than warm caches.
native_cache_clear_all() {
    ncca_dir=$1
    [ -n "${ncca_dir}" ] || return 2
    [ -d "${ncca_dir}" ] || return 2
    rm -rf "${ncca_dir}/" || return 1
    return 0
}

# --- folded: resume-stage4-from-admitted.sh ---------------------------------
# Sourced by bootstrap-from-scratch.sh after canonical receipt validation and
# portable output-lock acquisition. It must never start a compiler itself.

resume_stage4_continuation_lock=
resume_stage4_before=
resume_stage4_receipt=
resume_stage4_work=

resume_stage4_release_continuation_lock() {
  [ -z "${resume_stage4_work:-}" ] || rm -f "${resume_stage4_work}" "${resume_stage4_work}.part" "${resume_stage4_work}.tmp.$$"
  resume_stage4_continuation_lock=
}

resume_stage4_snapshot() {
  destination=$1 output=$2 platform=$3
  work="${destination}.work.$$"; resume_stage4_work=$work
  rm -f "$work"
  for protected in "$output/stage2/$platform" "$output/stage3/$platform"; do
    [ -d "$protected" ] && [ ! -L "$protected" ] || return 1
    bootstrap_stage3_directory_snapshot "$work.part" "$protected" || return 1
    printf 'directory=%s\n' "$protected" >>"$work"
    cat "$work.part" >>"$work"
    rm -f "$work.part"
  done
  mv "$work" "$destination"
  resume_stage4_work=
}

resume_stage4_prepare() {
  output=$(bootstrap_stage3_canonical_path "$1") || return 1
  root=$2 platform=$3 planner_receipt=$(bootstrap_stage3_canonical_file "$4") || return 1
  bootstrap_planner_v2_verify "$planner_receipt" "$root" || {
    echo "error: Stage 4 planner admission v2 did not verify" >&2; return 1;
  }
  [ "$(bootstrap_planner_v2_field target "$planner_receipt")" = "//bootstrap:stage4" ] || return 1
  [ "$output" = "$1" ] && [ -d "$output" ] && [ ! -L "$output" ] || return 1
  manifest="$output/stage3/$platform/provenance.env"
  candidate="$output/stage3/$platform/simple"
  case "$platform" in *windows*) candidate="${candidate}.exe" ;; esac
  manifest=$(bootstrap_stage3_canonical_file "$manifest") || return 1
  candidate=$(bootstrap_stage3_canonical_file "$candidate") || return 1
  bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate" || {
    echo "error: admitted Stage 3 provenance did not verify" >&2; return 1;
  }
  [ "$(bootstrap_stage3_manifest_value backend "$manifest")" = "$backend" ] || return 1
  [ "$(bootstrap_stage3_manifest_value mode "$manifest")" = "$bootstrap_mode" ] || return 1
  bootstrap_runtime_authority_path=$(bootstrap_stage3_canonical_path \
    "$(bootstrap_stage3_manifest_value runtime_path "$manifest")") || return 1
  SIMPLE_RUNTIME_PATH=$bootstrap_runtime_authority_path
  export SIMPLE_RUNTIME_PATH
  full="$output/full/$platform/simple"
  case "$platform" in *windows*) full="${full}.exe" ;; esac
  [ ! -e "$full" ] && [ ! -L "$full" ] &&
    [ ! -e "${full}.provenance.env" ] && [ ! -L "${full}.provenance.env" ] || {
    echo "error: Stage 4 resume output collision" >&2; return 1;
  }
  lock=${bootstrap_lock_handle:?canonical bootstrap output lock is required}
  [ -f "$lock" ] && [ ! -L "$lock" ] && portable_lock_handle_is_owned "$lock" || {
    echo "error: admitted Stage 4 continuation lock is not parent-owned" >&2; return 1;
  }
  resume_stage4_continuation_lock=$lock; bootstrap_lock=$lock
  resume_stage4_before="$output/stage4-continuation-before.sha256"
  [ ! -e "$resume_stage4_before" ] && [ ! -L "$resume_stage4_before" ] || return 1
  resume_stage4_snapshot "$resume_stage4_before" "$output" "$platform" || return 1
  receipt="$output/stage4-continuation.env"; resume_stage4_receipt=$receipt
  [ ! -e "$receipt" ] && [ ! -L "$receipt" ] || return 1
  umask 077
  {
    echo schema=simple-bootstrap-stage4-continuation-v1
    echo status=prepared
    echo planner_receipt_path="$planner_receipt"
    echo planner_receipt_sha256="$(bootstrap_stage3_hash_file "$planner_receipt")"
    echo stage3_provenance_path="$manifest"
    echo stage3_provenance_sha256="$(bootstrap_stage3_hash_file "$manifest")"
    echo parent_compiler_path="$candidate"
    echo parent_compiler_sha256="$(bootstrap_stage3_hash_file "$candidate")"
    echo bootstrap_lock_path="$lock"
    echo bootstrap_lock_owner_pid="$$"
    echo immutable_snapshot_path="$resume_stage4_before"
    echo immutable_snapshot_sha256="$(bootstrap_stage3_hash_file "$resume_stage4_before")"
  } >"${receipt}.tmp.$$"
  mv "${receipt}.tmp.$$" "$receipt"
  STAGE4_CONTINUATION_RECEIPT=$receipt
  export STAGE4_CONTINUATION_RECEIPT
}

resume_stage4_verify_immutable() {
  [ -n "${resume_stage4_before:-}" ] || return 0
  after="${resume_stage4_before%.sha256}-after.sha256"
  resume_stage4_snapshot "$after" "$output_dir" "$PLATFORM" || return 1
  cmp -s "$resume_stage4_before" "$after" || {
    echo "error: Stage 2/3 changed during Stage 4 continuation" >&2; return 1;
  }
}

resume_stage4_finalize() {
  [ -n "${resume_stage4_before:-}" ] || return 0
  resume_stage4_verify_immutable || return 1
  after="${resume_stage4_before%.sha256}-after.sha256"
  deploy_receipt="$repo_root/bin/release/$PLATFORM/bootstrap-deploy-receipt.env"
  [ -f "$full_bin" ] && [ ! -L "$full_bin" ] &&
    [ -f "${full_bin}.provenance.env" ] && [ ! -L "${full_bin}.provenance.env" ] &&
    [ -f "$deploy_receipt" ] && [ ! -L "$deploy_receipt" ] || return 1
  tmp="${resume_stage4_receipt}.tmp.$$"; resume_stage4_work=$tmp
  sed 's/^status=prepared$/status=pass/' "$resume_stage4_receipt" >"$tmp" || return 1
  {
    echo immutable_status=pass
    echo immutable_after_path="$after"
    echo immutable_after_sha256="$(bootstrap_stage3_hash_file "$after")"
    echo stage4_output_sha256="$(bootstrap_stage3_hash_file "$full_bin")"
    echo stage4_provenance_sha256="$(bootstrap_stage3_hash_file "${full_bin}.provenance.env")"
    echo deploy_receipt_sha256="$(bootstrap_stage3_hash_file "$deploy_receipt")"
  } >>"$tmp" || return 1
  mv "$tmp" "$resume_stage4_receipt"; resume_stage4_work=
}

# --- folded: preserve-phase-binary.shs -----------------------------------------
bootstrap_folded_preserve_phase_binary() {
# preserve-phase-binary.shs — immutable lineage snapshots of phase compiler binaries.
#
# Usage:
#   preserve-phase-binary.shs <binary> <phase>      # phase = phase1|phase2|phase3
#       Copies <binary> into build/phase_snapshots/<lineage>_<phase>_<epoch>/simple,
#       where <lineage> is read from the LINEAGE file of the NEWEST snapshot dir of
#       the parent phase (phase1 starts a fresh epoch). Writes a LINEAGE file,
#       chmods the binary and dir read-only, and NEVER overwrites an existing dir.
#   preserve-phase-binary.shs --gc <days>
#       Deletes snapshot generations older than <days> days that contain NO
#       PINNED.* marker file. Tasks pin a snapshot by `touch <dir>/PINNED.<task>`
#       (the dir itself stays writable enough for markers via chmod u+w on demand:
#       use `chmod u+w <dir>` before touching, `chmod u-w` after — or simply rely
#       on gc honouring any PINNED.* present).
#   Env: PHASE_SNAPSHOT_ROOT overrides the snapshot root (for tests).
set -u
root="${PHASE_SNAPSHOT_ROOT:-$(cd "$(dirname -- "$0")/../.." && pwd)/build/phase_snapshots}"
mkdir -p "${root}" || exit 1

if [ "${1:-}" = "--gc" ]; then
  days="${2:?usage: --gc <days>}"
  now=$(date +%s)
  cutoff=$((now - days * 86400))
  for d in "${root}"/phase1_*; do
    [ -d "$d" ] || continue
    # pinned?
    set -- "$d"/PINNED.*
    [ -e "$1" ] && { echo "gc: keep (pinned) ${d##*/}"; continue; }
    mtime=$(stat -c %Y "$d" 2>/dev/null || stat -f %m "$d") || continue
    if [ "${mtime}" -lt "${cutoff}" ]; then
      chmod -R u+w "$d" && rm -rf "$d" && echo "gc: removed ${d##*/}"
    else
      echo "gc: keep (recent) ${d##*/}"
    fi
  done
  exit 0
fi

bin="${1:?usage: preserve-phase-binary.shs <binary> <phase>}"
phase="${2:?usage: preserve-phase-binary.shs <binary> <phase>}"
[ -x "${bin}" ] || { echo "error: not an executable: ${bin}" >&2; exit 1; }
epoch=$(date +%s)

case "${phase}" in
  phase1) lineage="phase1_${epoch}" ;;
  phase2|phase3)
    [ "${phase}" = phase2 ] && parent=phase1 || parent=phase2
    if [ "${phase}" = phase2 ]; then
      parent_dir=$(ls -1dt "${root}"/phase1_[0-9]*/ 2>/dev/null | head -1)
    else
      parent_dir=$(ls -1dt "${root}"/phase1_[0-9]*_phase2_[0-9]*/ 2>/dev/null | head -1)
    fi
    parent_dir=${parent_dir%/}
    [ -n "${parent_dir}" ] && [ -f "${parent_dir}/LINEAGE" ] || {
      echo "error: no ${parent} snapshot with LINEAGE found for ${phase}" >&2; exit 1; }
    lineage="$(cat "${parent_dir}/LINEAGE")_${phase}_${epoch}"
    ;;
  *) echo "error: phase must be phase1|phase2|phase3" >&2; exit 1 ;;
esac

dest="${root}/${lineage}"
if [ -e "${dest}" ]; then
  echo "error: refusing to overwrite existing snapshot ${dest}" >&2
  exit 1
fi
mkdir "${dest}" || exit 1
cp -p "${bin}" "${dest}/simple" || { rm -rf "${dest}"; exit 1; }
printf '%s\n' "${lineage}" > "${dest}/LINEAGE"
chmod a-w "${dest}/simple" "${dest}/LINEAGE"
chmod a-w "${dest}"
echo "preserved: ${dest}/simple"
}

# --- folded: bootstrap-progress-watch.shs -----------------------------------------
bootstrap_folded_progress_watch() {
set -eu
# Structured event tokens are data, never pathname patterns.
set -f

usage() {
  cat <<'EOF'
Usage: bootstrap-from-scratch.sh progress-watch --pid=N --progress-log=PATH [options]

Write low-overhead, machine-checkable bootstrap liveness samples.

Options:
  --pid=N                 Process to observe (required)
  --progress-log=PATH     Append-only output log (required)
  --state-file=PATH       Optional milestone/main_log key-value state file
  --event-file=PATH       Optional append-only structured build-progress events
  --interval=N            Seconds between samples (default: 30)
  --expected-start=TEXT   Reject PID reuse when ps start text differs
  --once                  Emit one sample and exit
  --help                  Show this help

CPU/RSS are aggregated over the observed process and ALL its descendants, not
the observed process alone -- --pid is typically a wrapper shell that sleeps
while its child builds. CPU is instantaneous (/proc utime+stime deltas between
samples), never a lifetime average.

status is `alive`, `alive-no-progress`, `exited`, or `stale`.
`alive-no-progress` is REPORTED, never acted on: it means the tree burned
<BOOTSTRAP_WATCH_STALL_CPU_PCT (default 3) percent CPU with no main-log growth
and no build_progress change for BOOTSTRAP_WATCH_STALL_SAMPLES (default 4)
consecutive samples. This watcher never kills anything.
EOF
}

watch_pid=
progress_log=
state_file=
event_file=
interval=30
expected_start=
once=0

for arg in "$@"; do
  case "$arg" in
    --pid=*) watch_pid=${arg#*=} ;;
    --progress-log=*) progress_log=${arg#*=} ;;
    --state-file=*) state_file=${arg#*=} ;;
    --event-file=*) event_file=${arg#*=} ;;
    --interval=*) interval=${arg#*=} ;;
    --expected-start=*) expected_start=${arg#*=} ;;
    --once) once=1 ;;
    --help|-h) usage; exit 0 ;;
    *) echo "error: unknown option '$arg'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$watch_pid" in ''|*[!0-9]*) echo "error: --pid requires a numeric PID" >&2; exit 2 ;; esac
case "$interval" in ''|*[!0-9]*|0) echo "error: --interval requires a positive integer" >&2; exit 2 ;; esac
[ -n "$progress_log" ] || { echo "error: --progress-log is required" >&2; exit 2; }
mkdir -p "$(dirname -- "$progress_log")"

clk_tck=$(getconf CLK_TCK 2>/dev/null || echo 100)
case "$clk_tck" in ''|*[!0-9]*) clk_tck=100 ;; esac
page_kb=$(( $(getconf PAGESIZE 2>/dev/null || echo 4096) / 1024 ))
[ "$page_kb" -gt 0 ] 2>/dev/null || page_kb=4
# A tree is "quiet" below this instantaneous CPU percent. Deliberately not 0:
# a genuinely wedged tree still shows a fraction of a percent from timers and
# sampling jitter.
stall_cpu_pct=${BOOTSTRAP_WATCH_STALL_CPU_PCT:-3}
# Consecutive quiet-AND-no-log-growth samples before we will say so. At the
# default 30s interval that is 4 samples / ~2 minutes. Kept high on purpose:
# three sessions killed HEALTHY builds on 2026-08-17 because a silent stage was
# indistinguishable from a hung one, one of them already at 62/62. A FALSE
# "hung" verdict is more expensive than a late true one.
stall_samples=${BOOTSTRAP_WATCH_STALL_SAMPLES:-4}
case "$stall_samples" in ''|*[!0-9]*|0) stall_samples=4 ;; esac

process_start=$(ps -o lstart= -p "$watch_pid" 2>/dev/null | sed 's/^ *//;s/ *$//' || true)
if [ -n "$expected_start" ] && [ "$process_start" != "$expected_start" ]; then
  printf 'event=sample status=stale pid=%s expected_start=%s actual_start=%s\n' \
    "$watch_pid" "$expected_start" "${process_start:-absent}" >>"$progress_log"
  exit 3
fi

# Instantaneous CPU for the whole descendant TREE, from /proc/<pid>/stat
# utime+stime DELTAS between samples.
#
# Two defects are fixed here at once, and both were "the monitor reports a
# number that is not about the work":
#
# 1. WRONG SUBJECT. The wrapper passes its own `$$` as --pid, but that shell
#    SLEEPS while its child does the build. Sampling only the root reported
#    cpu_pct=0.0 / rss=2984KB for a stage-3 compile genuinely running at 98.8%
#    CPU and 6.9GB RSS (measured 2026-08-17). We therefore aggregate across
#    every descendant, and additionally name the single heaviest one so a human
#    reading the log can see WHAT is working.
#
# 2. WRONG STATISTIC. `ps` pcpu is a LIFETIME AVERAGE, so a process that pegs
#    the CPU and then idles reads mid-range and the verdict depends on poll
#    timing. `scripts/resource/kill_simple_monitor.shs` hit and fixed exactly
#    this (commit bd3016a32a7); this reuses that approach -- tick deltas over
#    the real elapsed interval, with `starttime` checked so a RECYCLED pid can
#    never inherit a stranger's prior sample.
#
# Emits: "<cpu_pct|unknown> <tree_rss_kb> <nproc> <top_pid> <top_rss_kb> <top_comm> <tree_rss_pgroup_kb> <pgroup_processes> <scan_misses> <root_rss_kb>".
# root_rss_kb and tree_rss_kb come from the same /proc snapshot, so a leaf
# process cannot report two different RSS values merely because it changed
# residency between independent reads.
# cpu_pct is `unknown` when no prior tick baseline exists. Callers MUST treat
# `unknown` as "no evidence", never as 0 and never as idle.
cpu_state_file="${progress_log}.treestate"

process_tree_metrics() {
  metrics_root=$1
  metrics_exclude=$2
  awk -v root="$metrics_root" -v exclude="$metrics_exclude" \
      -v state="$cpu_state_file" -v clk="$clk_tck" -v now="$(date +%s)" \
      -v pagekb="$page_kb" '
    function load(pid,   path, line, rest, n, a, cm) {
      path = "/proc/" pid "/stat"
      line = ""
      if ((getline line < path) <= 0) { close(path); return 0 }
      close(path)
      cm = line
      sub(/^[0-9]+ \(/, "", cm); sub(/\).*$/, "", cm)
      # comm (field 2) is parenthesised and may itself contain ") ", so strip
      # through the LAST ") " -- otherwise every later field shifts.
      rest = line
      sub(/^.*\) /, "", rest)
      n = split(rest, a, " ")
      if (n < 22) return 0
      # a[1] is field 3 (state), so field N is a[N-2]:
      # ppid(4)=a[2] pgrp(5)=a[3] utime(14)=a[12] stime(15)=a[13]
      # starttime(22)=a[20] rss(24)=a[22]
      parent[pid] = a[2]
      pgrp[pid]   = a[3]
      ticks[pid]  = a[12] + a[13]
      start[pid]  = a[20]
      rsspg[pid]  = a[22]
      comm[pid]   = cm
      return 1
    }
    BEGIN {
      n = 0
      misses = 0
      while (("ls -1 /proc 2>/dev/null" | getline p) > 0) {
        if (p !~ /^[0-9]+$/) continue
        if (load(p)) { pids[++n] = p } else { misses++ }
      }
      close("ls -1 /proc 2>/dev/null")

      included[root] = 1
      excluded[exclude] = 1
      changed = 1
      while (changed) {
        changed = 0
        for (i = 1; i <= n; i++) {
          pid = pids[i]
          if (included[parent[pid]] && !included[pid]) { included[pid] = 1; changed = 1 }
          if (excluded[parent[pid]] && !excluded[pid]) { excluded[pid] = 1; changed = 1 }
        }
      }

      prev_when = ""
      while ((getline line < state) > 0) {
        split(line, s, " ")
        if (s[1] == "when") { prev_when = s[2]; continue }
        prev_start[s[1]] = s[2]; prev_ticks[s[1]] = s[3]
      }
      close(state)

      printf "when %s\n", now > state
      total_rss = 0; nproc = 0; dticks = 0; root_rss = 0
      pg_rss = 0; pg_nproc = 0
      root_pg = (root in pgrp) ? pgrp[root] : ""
      top_pid = "none"; top_rss = 0; top_comm = "none"
      # SECOND, INDEPENDENT BASIS. `included[]` above walks the PARENT CHAIN
      # only, so a worker that outlives its intermediate parent (re-parented to
      # init/a subreaper) silently leaves the tree, and any pid whose
      # /proc/<pid>/stat read failed drops its WHOLE subtree with it -- both
      # vanish from total_rss with no signal at all. That is how a 67.4 GB
      # stage-3 compile logged tree_rss_kb=34753460 (34.7 GB): the reported
      # total was smaller than a single live process. The process GROUP does
      # not move when a parent dies, so summing it too makes the loss visible.
      # tree_rss_kb keeps its parent-chain meaning; read tree_rss_pgroup_kb
      # alongside it, and treat pgroup >> chain as "the chain lost a subtree".
      for (i = 1; i <= n; i++) {
        pid = pids[i]
        if (excluded[pid] || root_pg == "" || pgrp[pid] != root_pg) continue
        pg_nproc++
        pg_rss += rsspg[pid]
      }
      for (i = 1; i <= n; i++) {
        pid = pids[i]
        if (!included[pid] || excluded[pid]) continue
        nproc++
        total_rss += rsspg[pid]
        if (pid == root) root_rss = rsspg[pid] * pagekb
        if (rsspg[pid] > top_rss) { top_rss = rsspg[pid]; top_pid = pid; top_comm = comm[pid] }
        printf "%s %s %s\n", pid, start[pid], ticks[pid] > state
        if (pid in prev_ticks && prev_start[pid] == start[pid]) {
          d = ticks[pid] - prev_ticks[pid]
          if (d > 0) dticks += d
        } else {
          # New pid (or a recycled one we refuse to compare). Count its whole
          # lifetime: a worker that spawned inside this interval did that work
          # inside this interval. Erring toward "busy" is the safe direction --
          # it can only delay a stall verdict, never fabricate one.
          dticks += ticks[pid]
        }
      }
      close(state)

      if (prev_when == "" || now - prev_when < 1) { cpu = "unknown" }
      else { cpu = sprintf("%.1f", dticks * 100.0 / (clk * (now - prev_when))) }
      printf "%s %d %d %s %d %s %d %d %d %d\n", cpu, total_rss * pagekb, nproc, \
        top_pid, top_rss * pagekb, top_comm, pg_rss * pagekb, pg_nproc, misses, root_rss
    }
  '
}

load_progress_event() {
  phase=unknown
  unit_kind=unknown
  done=unknown
  total=unknown
  remaining=unknown
  tasks_done=unknown
  tasks_total=unknown
  tasks_remaining=unknown
  failed=unknown
  cached=unknown
  current=unknown
  terminal=unknown
  [ -n "$event_file" ] && [ -f "$event_file" ] || return 0
  progress_line=$(tail -n 1 "$event_file" 2>/dev/null || true)
  case "$progress_line" in event=build_progress\ *) ;; *) return 0 ;; esac
  for progress_token in $progress_line; do
    progress_key=${progress_token%%=*}
    progress_value=${progress_token#*=}
    case "$progress_key" in
      phase) [ -n "$progress_value" ] && phase=$progress_value ;;
      unit_kind) [ -n "$progress_value" ] && unit_kind=$progress_value ;;
      current) [ -n "$progress_value" ] && current=$progress_value ;;
      done|total|remaining|tasks_done|tasks_total|tasks_remaining|failed|cached)
        case "$progress_value" in unknown) ;; ''|*[!0-9]*) continue ;; esac
        case "$progress_key" in
          done) done=$progress_value ;;
          total) total=$progress_value ;;
          remaining) remaining=$progress_value ;;
          tasks_done) tasks_done=$progress_value ;;
          tasks_total) tasks_total=$progress_value ;;
          tasks_remaining) tasks_remaining=$progress_value ;;
          failed) failed=$progress_value ;;
          cached) cached=$progress_value ;;
        esac
        ;;
      terminal)
        case "$progress_value" in running|succeeded|failed|exited) terminal=$progress_value ;; esac
        ;;
    esac
  done
  case "$done:$total" in
    *[!0-9:]*|:*|*:) ;;
    *)
      remaining=$((total - done))
      [ "$remaining" -ge 0 ] || remaining=0
      ;;
  esac
  case "$tasks_done:$tasks_total" in
    *[!0-9:]*|:*|*:) ;;
    *)
      tasks_remaining=$((tasks_total - tasks_done))
      [ "$tasks_remaining" -ge 0 ] || tasks_remaining=0
      ;;
  esac
}

started_at=$(date +%s)
stall_streak=0
prev_log_bytes=
prev_progress_sig=
rm -f "$cpu_state_file" 2>/dev/null || true
# Prime the tick baseline so the FIRST heartbeat already carries a real CPU
# number. Without this the first sample is always `unknown` -- and that is
# exactly the sample a human stares at when deciding whether to kill a build.
# It also makes `--once` structurally capable of measuring something.
process_tree_metrics "$watch_pid" "$$" >/dev/null 2>&1 || true
sleep 1
while :; do
  now=$(date +%s)
  milestone=unknown
  main_log=
  if [ -n "$state_file" ] && [ -f "$state_file" ]; then
    milestone=$(sed -n 's/^milestone=//p' "$state_file" | tail -1)
    main_log=$(sed -n 's/^main_log=//p' "$state_file" | tail -1)
    [ -n "$milestone" ] || milestone=unknown
  fi
  load_progress_event

  if ! kill -0 "$watch_pid" 2>/dev/null; then
    case "$terminal" in running|unknown) terminal=exited ;; esac
    printf 'event=sample timestamp=%s status=exited pid=%s elapsed_s=%s milestone=%s phase=%s unit_kind=%s done=%s total=%s remaining=%s tasks_done=%s tasks_total=%s tasks_remaining=%s failed=%s cached=%s current=%s terminal=%s\n' \
      "$now" "$watch_pid" "$((now - started_at))" "$milestone" \
      "$phase" "$unit_kind" "$done" "$total" "$remaining" \
      "$tasks_done" "$tasks_total" "$tasks_remaining" "$failed" \
      "$cached" "$current" "$terminal" >>"$progress_log"
    rm -f "$cpu_state_file" 2>/dev/null || true
    exit 0
  fi

  current_start=$(ps -o lstart= -p "$watch_pid" 2>/dev/null | sed 's/^ *//;s/ *$//' || true)
  if [ -n "$process_start" ] && [ "$current_start" != "$process_start" ]; then
    printf 'event=sample timestamp=%s status=stale pid=%s elapsed_s=%s milestone=%s\n' \
      "$now" "$watch_pid" "$((now - started_at))" "$milestone" >>"$progress_log"
    rm -f "$cpu_state_file" 2>/dev/null || true
    exit 3
  fi

  metrics=$(ps -o etime= -p "$watch_pid" 2>/dev/null | awk 'NF {print $1; exit}')
  set -- $metrics
  process_elapsed=${1:-unknown}
  # rss_kb is the ROOT process only, and for a wrapper shell that is ~3MB of
  # sleeping shell. Kept for continuity, but it is NOT the build's footprint --
  # tree_rss_kb is. Do not read rss_kb as "how big is the build".
  tree_metrics=$(process_tree_metrics "$watch_pid" "$$")
  set -- $tree_metrics
  tree_cpu_pct=${1:-unknown}
  tree_rss_kb=${2:-unknown}
  tree_processes=${3:-unknown}
  top_pid=${4:-none}
  top_rss_kb=${5:-unknown}
  top_comm=${6:-none}
  tree_rss_pgroup_kb=${7:-unknown}
  tree_pgroup_processes=${8:-unknown}
  tree_scan_misses=${9:-unknown}
  # `process_tree_metrics` emits the root RSS as its final field.  Keep the
  # legacy root field total on hosts where /proc is unavailable: otherwise
  # `set -u` aborts the watcher before it can record even an `unknown` sample.
  rss_kb=${10:-unknown}
  # cpu_pct now means "instantaneous CPU of the work", i.e. the whole tree. It
  # used to mean the root pid's lifetime average, which for the wrapper shell
  # was a constant 0.0 no matter what the build was doing.
  cpu_pct=$tree_cpu_pct
  log_bytes=absent
  if [ -n "$main_log" ] && [ -f "$main_log" ]; then
    log_bytes=$(ls -ln "$main_log" 2>/dev/null | awk 'NF {print $5; exit}')
    [ -n "$log_bytes" ] || log_bytes=unknown
  fi

  # Stall classification. All THREE independent progress signals must be silent,
  # and for $stall_samples consecutive samples, before we will say anything
  # other than plain `alive`. An `unknown` CPU reading (no baseline, or a
  # too-short interval) is no evidence and RESETS the streak.
  progress_sig="$milestone|$phase|$done|$total|$tasks_done|$current"
  quiet=0
  case "$tree_cpu_pct" in
    unknown) ;;
    *) awk -v c="$tree_cpu_pct" -v t="$stall_cpu_pct" 'BEGIN{exit !(c<t)}' && quiet=1 ;;
  esac
  if [ "$quiet" -eq 1 ] && [ -n "$prev_log_bytes" ] &&
     [ "$log_bytes" = "$prev_log_bytes" ] && [ "$progress_sig" = "$prev_progress_sig" ]; then
    stall_streak=$((stall_streak + 1))
  else
    stall_streak=0
  fi
  prev_log_bytes=$log_bytes
  prev_progress_sig=$progress_sig
  status=alive
  [ "$stall_streak" -lt "$stall_samples" ] || status=alive-no-progress

  printf 'event=sample timestamp=%s status=%s pid=%s elapsed_s=%s process_elapsed=%s cpu_pct=%s rss_kb=%s tree_cpu_pct=%s tree_rss_kb=%s tree_processes=%s top_pid=%s top_rss_kb=%s top_comm=%s tree_rss_pgroup_kb=%s tree_pgroup_processes=%s tree_scan_misses=%s stall_streak=%s milestone=%s main_log_bytes=%s phase=%s unit_kind=%s done=%s total=%s remaining=%s tasks_done=%s tasks_total=%s tasks_remaining=%s failed=%s cached=%s current=%s terminal=%s\n' \
    "$now" "$status" "$watch_pid" "$((now - started_at))" "$process_elapsed" \
    "$cpu_pct" "$rss_kb" "$tree_cpu_pct" "$tree_rss_kb" \
    "$tree_processes" "$top_pid" "$top_rss_kb" "$top_comm" \
    "$tree_rss_pgroup_kb" "$tree_pgroup_processes" "$tree_scan_misses" "$stall_streak" \
    "$milestone" "$log_bytes" "$phase" "$unit_kind" \
    "$done" "$total" "$remaining" "$tasks_done" "$tasks_total" \
    "$tasks_remaining" "$failed" "$cached" "$current" "$terminal" \
    >>"$progress_log"

  if [ "$once" -ne 0 ]; then
    rm -f "$cpu_state_file" 2>/dev/null || true
    exit 0
  fi
  sleep "$interval"
done
}

# --- folded: produce-bootstrap-planner-admission-v2.shs -----------------------------------------
bootstrap_folded_planner_admission_v2() {
# Canonical producer for planner admission v2.
#
# This is the missing half of the admission design: the verifier in
# scripts/check/lib/bootstrap-planner-admission-bound.shs checks structure,
# pinned paths, and re-derived argv/env digests, but until this script existed
# nothing ever EMITTED a receipt that could satisfy it, so the admission path
# was not fail-closed — it was closed, and no bootstrap could start. See
# doc/08_tracking/bug/bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17.md
#
# Non-circular by construction, in order:
#   1. take a pre-exec lock so nothing measured can change under us
#   2. verify the parent authority (stage2 compiler + sanity + provenance) —
#      fail closed, never the Rust seed, never an unverified binary
#   3. hash parent, runtime snapshot, planner source + closure, git state
#   4. build the planner with the parent compiler
#   5. EXECUTE it under the canonical argv/env and hash what was actually run
#   6. run the negative smoke check and record its transcript
#   7. re-measure everything and only then emit the 29-field receipt
#
# Verdict is the last line of stdout:
#   bootstrap-admission: produced <receipt>            exit 0
#   bootstrap-admission-error: <typed-reason>          exit 64
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
root=$(CDPATH= cd -- "$root/.." && pwd -P)
. "$root/scripts/check/lib/bootstrap-planner-admission-bound.shs"
. "$root/scripts/check/lib/bootstrap-stage3/authority.shs"
. "$root/scripts/check/lib/bootstrap-stage3/command-snapshot.shs"
. "$root/scripts/check/lib/bootstrap-stage3/sanity.shs"

adm_fail() {
    echo "bootstrap-admission-error: $1" >&2
    echo "bootstrap-admission-error: $1"
    exit 64
}

usage() {
    echo "usage: $0 --target=<//bootstrap:stageN> --reason=<typed-reason> --parent-compiler=<path> [--bootstrap-output=<path>] [--runtime-dir=<path>] [--out=<path>]" >&2
    echo "       $0 --selftest" >&2
}

selftest=0
adm_target=''
adm_reason=''
adm_parent=''
adm_runtime=''
adm_out=''
adm_root=$root
adm_bootstrap_output=''

while [ "$#" -gt 0 ]; do
    case "$1" in
        --selftest) selftest=1 ;;
        --target=*) adm_target=${1#*=} ;;
        --reason=*) adm_reason=${1#*=} ;;
        --parent-compiler=*) adm_parent=${1#*=} ;;
        --bootstrap-output=*) adm_bootstrap_output=${1#*=} ;;
        --runtime-dir=*) adm_runtime=${1#*=} ;;
        --out=*) adm_out=${1#*=} ;;
        --root=*) adm_root=${1#*=} ;;
        --help|-h) usage; exit 0 ;;
        *) usage; exit 2 ;;
    esac
    shift
done

if [ "$selftest" -eq 1 ]; then
    sh "$root/scripts/check/check-bootstrap-planner-admission-producer.shs"
    exit $?
fi

[ -n "$adm_target" ] && [ -n "$adm_reason" ] && [ -n "$adm_parent" ] || { usage; exit 2; }

adm_root=$(bootstrap_planner_v2_canonical_dir "$adm_root") || adm_fail root-not-canonical
bootstrap_planner_v2_reason_allowed "$adm_target" "$adm_reason" || adm_fail typed-reason-not-allowed-for-target

physical_cwd=$(pwd -P) || adm_fail cwd-not-canonical
if [ -z "$adm_bootstrap_output" ]; then
    adm_bootstrap_output="$adm_root/build/bootstrap"
fi
case "$adm_bootstrap_output" in /*) ;; *) adm_bootstrap_output="$physical_cwd/$adm_bootstrap_output" ;; esac
adm_bootstrap_output=$(bootstrap_planner_v2_canonical_dir "$adm_bootstrap_output") || adm_fail bootstrap-output-missing
case "$adm_bootstrap_output" in "$adm_root"/build/*) ;; *) adm_fail bootstrap-output-outside-build-root ;; esac

case "$adm_parent" in /*) ;; *) adm_parent="$physical_cwd/$adm_parent" ;; esac
if [ -z "$adm_runtime" ]; then adm_runtime="$adm_root/src/runtime"; fi
case "$adm_runtime" in /*) ;; *) adm_runtime="$physical_cwd/$adm_runtime" ;; esac

# --- 2. parent authority -----------------------------------------------------
# The parent must be a stage2 artifact carrying sanity + provenance evidence.
# A Rust seed, a hand-placed binary, or a stage2 dir with no evidence is
# refused: the whole point of v2 is that admission descends from an admitted
# parent, so an unverifiable parent must not produce an authoritative receipt.
stage2_root="$adm_bootstrap_output/stage2"
case "$adm_parent" in
    "$stage2_root"/*) ;;
    *) adm_fail parent-compiler-not-under-build-bootstrap-stage2 ;;
esac
parent_file=$(bootstrap_planner_v2_canonical_file "$adm_parent") || adm_fail parent-compiler-missing-or-not-canonical
parent_dir=$(dirname -- "$parent_file")
sanity_file="$parent_dir/stage2-sanity.receipt"
prov_file="$parent_dir/stage2-provenance.receipt"
bootstrap_planner_v2_canonical_file "$sanity_file" >/dev/null 2>&1 || adm_fail parent-stage2-sanity-unavailable
bootstrap_planner_v2_canonical_file "$prov_file" >/dev/null 2>&1 || adm_fail parent-stage2-provenance-unavailable

parent_field() {
    pf_file=$1 pf_key=$2
    [ "$(grep -c "^${pf_key}=" "$pf_file" 2>/dev/null || true)" -eq 1 ] || return 1
    sed -n "s/^${pf_key}=//p" "$pf_file"
}
parent_sha=$(bootstrap_planner_v2_hash_file "$parent_file")
[ "$(parent_field "$sanity_file" schema || true)" = simple-bootstrap-stage2-parent-sanity-v1 ] || adm_fail parent-stage2-sanity-schema-mismatch
[ "$(grep -c '^stage2-sanity: pass$' "$sanity_file" 2>/dev/null || true)" -eq 1 ] || adm_fail parent-stage2-sanity-not-pass
[ "$(parent_field "$sanity_file" candidate_sha256 || true)" = "$parent_sha" ] || adm_fail parent-stage2-sanity-candidate-mismatch
[ "$(parent_field "$prov_file" schema || true)" = simple-bootstrap-stage2-parent-provenance-v1 ] || adm_fail parent-stage2-provenance-schema-mismatch
[ "$(grep -c '^stage2-provenance: pure-simple$' "$prov_file" 2>/dev/null || true)" -eq 1 ] || adm_fail parent-stage2-provenance-not-pure-simple
[ "$(parent_field "$prov_file" authority || true)" = explicit-full-bootstrap-stage2-trust-root ] || adm_fail parent-stage2-provenance-authority-mismatch
[ "$(parent_field "$prov_file" candidate_sha256 || true)" = "$parent_sha" ] || adm_fail parent-stage2-provenance-candidate-mismatch
admission_file=$(parent_field "$sanity_file" admission_receipt_path || true)
[ -n "$admission_file" ] && [ "$admission_file" = "$(parent_field "$prov_file" admission_receipt_path || true)" ] || adm_fail parent-stage2-admission-path-mismatch
admission_file=$(bootstrap_planner_v2_canonical_file "$admission_file") || adm_fail parent-stage2-admission-unavailable
case "$admission_file" in "$adm_bootstrap_output"/*) ;; *) adm_fail parent-stage2-admission-outside-bootstrap ;; esac
admission_sha=$(bootstrap_planner_v2_hash_file "$admission_file")
[ "$(parent_field "$sanity_file" admission_receipt_sha256 || true)" = "$admission_sha" ] || adm_fail parent-stage2-sanity-admission-mismatch
[ "$(parent_field "$prov_file" admission_receipt_sha256 || true)" = "$admission_sha" ] || adm_fail parent-stage2-provenance-admission-mismatch
admission_candidate=$(parent_field "$admission_file" candidate_path || true)
admission_source=$(parent_field "$admission_file" source_snapshot_path || true)
admission_runtime=$(parent_field "$admission_file" runtime_snapshot_path || true)
admission_tool=$(parent_field "$admission_file" tool_authority_path || true)
admission_args_sha=$(parent_field "$admission_file" build_args_sha256 || true)
admission_sanity=$(parent_field "$admission_file" sanity_evidence_path || true)
admission_receiver=$(parent_field "$admission_file" receiver_evidence_path || true)
bootstrap_stage3_verify_stage2_admission_receipt \
    "$admission_file" "$admission_candidate" "$admission_source" \
    "$admission_runtime" "$admission_tool" "$admission_args_sha" \
    "$admission_sanity" "$admission_receiver" || adm_fail parent-stage2-admission-invalid
[ "$(bootstrap_planner_v2_hash_file "$admission_candidate")" = "$parent_sha" ] || adm_fail parent-stage2-admission-candidate-mismatch

planner_source="$adm_root/src/app/cli/bootstrap_reason_planner.spl"
bootstrap_planner_v2_canonical_file "$planner_source" >/dev/null || adm_fail planner-source-missing
bootstrap_planner_v2_canonical_dir "$adm_runtime" >/dev/null || adm_fail runtime-dir-missing
case "$adm_runtime" in "$adm_root"/*) ;; *) adm_fail runtime-dir-outside-root ;; esac

# --- 1. pre-exec lock --------------------------------------------------------
lock_dir="$adm_root/build/bootstrap/admission/.lock"
mkdir -p "$adm_root/build/bootstrap/admission"
mkdir "$lock_dir" 2>/dev/null || adm_fail admission-lock-held
trap 'rmdir "$lock_dir" 2>/dev/null || true' EXIT HUP INT TERM

# --- 3. measure --------------------------------------------------------------
sanity_sha=$(bootstrap_planner_v2_hash_file "$sanity_file")
prov_sha=$(bootstrap_planner_v2_hash_file "$prov_file")
planner_source_sha=$(bootstrap_planner_v2_hash_file "$planner_source")

stage=$(mktemp -d "${TMPDIR:-/tmp}/simple-admission.XXXXXX")
trap 'rm -rf -- "$stage"; rmdir "$lock_dir" 2>/dev/null || true' EXIT HUP INT TERM

# Runtime snapshot: sorted relative-path + sha256 over every runtime file, so
# the digest names content rather than a directory mtime.
( cd "$adm_runtime" && find . -type f ! -path './vendor/*' -print0 |
    LC_ALL=C sort -z |
    xargs -0 -r sha256sum -- ) >"$stage/runtime.snapshot"
runtime_sha=$(bootstrap_planner_v2_hash_file "$stage/runtime.snapshot")

# Source closure: the planner imports no modules (only externs), so its closure
# is itself plus the runtime extern surface it names. Recorded explicitly.
{
    printf 'closure-schema: simple-planner-source-closure-v1\n'
    printf '%s  %s\n' "$planner_source_sha" "src/app/cli/bootstrap_reason_planner.spl"
    grep -n '^extern fn ' "$planner_source" || true
} >"$stage/planner-source-closure.snapshot"
closure_sha=$(bootstrap_planner_v2_hash_file "$stage/planner-source-closure.snapshot")

{
    printf 'git-head: %s\n' "$(cd "$adm_root" && git rev-parse HEAD 2>/dev/null || echo unknown)"
    printf 'git-dirty-paths:\n'
    ( cd "$adm_root" && git status --porcelain 2>/dev/null || true )
} >"$stage/git-state.txt"

scope_key=$(printf '%s:%s\n' "$runtime_sha" "$closure_sha" | sha256sum | awk '{print $1}')
adm_dir=$(bootstrap_planner_v2_admission_dir "$adm_root" "$scope_key")
rm -rf -- "$adm_dir"
mkdir -p "$adm_dir"
adm_dir=$(bootstrap_planner_v2_canonical_dir "$adm_dir") || adm_fail admission-dir-not-canonical
cp -- "$stage/runtime.snapshot" "$adm_dir/runtime.snapshot"
cp -- "$stage/planner-source-closure.snapshot" "$adm_dir/planner-source-closure.snapshot"
cp -- "$stage/git-state.txt" "$adm_dir/git-state.txt"
git_sha=$(bootstrap_planner_v2_hash_file "$adm_dir/git-state.txt")

# --- 4. build the planner with the parent compiler ---------------------------
# --entry-closure: compile ONLY the modules reachable from the planner entry.
# Without it the parent compiles the entire stdlib, including the baremetal boot
# stubs under src/lib/nogc_async_mut_noalloc/baremetal/, whose inline-asm operand
# placeholders the stale parent cannot lower -- an assembler error in code the
# one-file planner never calls. The closure is exactly what the closure snapshot
# already records, so narrowing the compile set does not narrow the receipt.
#
# The build runs with cwd = "$stage" (a fresh mktemp dir) so the parent resolves
# its relative `build/simple-core/libsimple_runtime.a` inside the staging dir and
# builds that archive from the runtime tree that was just snapshotted. The
# repo-root archive is a shared artifact that a concurrent lane can leave stale
# at any moment; admission must not depend on, or mutate, it.
build_planner_out="$adm_dir/planner"
if ! ( cd "$stage" && SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH="$adm_runtime" "$parent_file" \
        native-build --source "$adm_root/src/app/cli" --source "$adm_root/src/lib" \
        --entry-closure --entry "$planner_source" -o "$build_planner_out" ) >"$adm_dir/planner-build.log" 2>&1; then
    adm_fail planner-build-failed
fi
[ -x "$adm_dir/planner" ] || adm_fail planner-build-produced-no-executable
planner_sha=$(bootstrap_planner_v2_hash_file "$adm_dir/planner")

# --- 5. execute under the canonical argv/env --------------------------------
# The digests below are hashed from the argv/env actually used for this exec,
# which the verifier re-derives from the receipt fields. Both sides read the
# same two functions in the bound library, so they cannot drift apart.
auth_path="$adm_dir/authorization.receipt"
argv_text=$(bootstrap_planner_v2_canonical_argv_text \
    "$adm_dir/planner" "$adm_reason" "$adm_target" \
    "$parent_sha" "$runtime_sha" "$closure_sha" "$planner_sha" "$auth_path")
env_text=$(bootstrap_planner_v2_canonical_env_text "$adm_runtime")
argv_sha=$(bootstrap_planner_v2_hash_text "$argv_text")
env_sha=$(bootstrap_planner_v2_hash_text "$env_text")

planner_rc=0
env -i LC_ALL=C LANG=C TZ=UTC PATH=/usr/bin:/bin SOURCE_DATE_EPOCH=0 \
    SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH="$adm_runtime" \
    "$adm_dir/planner" \
    "--bootstrap-reason=$adm_reason" \
    "--bootstrap-target=$adm_target" \
    "--parent-compiler-sha256=$parent_sha" \
    "--runtime-snapshot-sha256=$runtime_sha" \
    "--planner-source-closure-sha256=$closure_sha" \
    "--planner-sha256=$planner_sha" \
    "--bootstrap-receipt=$auth_path" >"$adm_dir/planner-stdout.txt" 2>&1 || planner_rc=$?
[ "$planner_rc" -eq 0 ] || adm_fail planner-execution-nonzero-exit
bootstrap_planner_v2_canonical_file "$auth_path" >/dev/null || adm_fail planner-emitted-no-authorization

expected_auth=$(bootstrap_planner_v2_authorization_text \
    "$adm_target" "$adm_reason" "$parent_sha" "$runtime_sha" "$closure_sha" "$planner_sha")
[ "$(cat -- "$auth_path")" = "$expected_auth" ] || adm_fail authorization-text-mismatch

# --- 6. negative smoke check -------------------------------------------------
# An admitted planner must REFUSE an untyped reason. A planner that accepts
# anything is not a policy gate, so we prove refusal before trusting its pass.
smoke_rc=0
env -i LC_ALL=C LANG=C TZ=UTC PATH=/usr/bin:/bin SOURCE_DATE_EPOCH=0 \
    SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH="$adm_runtime" \
    "$adm_dir/planner" \
    '--bootstrap-reason=none' \
    "--bootstrap-target=$adm_target" \
    "--parent-compiler-sha256=$parent_sha" \
    "--runtime-snapshot-sha256=$runtime_sha" \
    "--planner-source-closure-sha256=$closure_sha" \
    "--planner-sha256=$planner_sha" \
    "--bootstrap-receipt=$stage/smoke.receipt" >"$stage/smoke.out" 2>&1 || smoke_rc=$?
[ "$smoke_rc" -ne 0 ] || adm_fail planner-smoke-accepted-untyped-reason
[ ! -e "$stage/smoke.receipt" ] || adm_fail planner-smoke-wrote-receipt-on-refusal
{
    printf 'smoke-schema: simple-planner-smoke-v1\n'
    printf 'untyped-reason-exit: %s\n' "$smoke_rc"
    printf 'untyped-reason-wrote-receipt: no\n'
    cat -- "$stage/smoke.out"
} >"$adm_dir/planner-smoke.txt"
smoke_sha=$(bootstrap_planner_v2_hash_file "$adm_dir/planner-smoke.txt")
auth_sha=$(bootstrap_planner_v2_hash_file "$auth_path")

# --- 7. re-measure, then emit ------------------------------------------------
# The lock has been held throughout; re-hashing proves it, so the receipt
# describes one consistent instant rather than a drifting tree.
[ "$(bootstrap_planner_v2_hash_file "$parent_file")" = "$parent_sha" ] || adm_fail parent-compiler-changed-during-admission
[ "$(bootstrap_planner_v2_hash_file "$planner_source")" = "$planner_source_sha" ] || adm_fail planner-source-changed-during-admission
[ "$(bootstrap_planner_v2_hash_file "$adm_dir/planner")" = "$planner_sha" ] || adm_fail planner-changed-during-admission
[ "$(bootstrap_planner_v2_hash_file "$adm_dir/runtime.snapshot")" = "$runtime_sha" ] || adm_fail runtime-snapshot-changed-during-admission

if [ -z "$adm_out" ]; then adm_out="$adm_dir/planner-admission-v2.env"; fi
case "$adm_out" in /*) ;; *) adm_out="$PWD/$adm_out" ;; esac
platform=$(uname -m 2>/dev/null || echo unknown)

{
    printf 'schema=simple-bootstrap-planner-admission-v2\n'
    printf 'status=pass\n'
    printf 'platform=%s\n' "$platform"
    printf 'target=%s\n' "$adm_target"
    printf 'reason=%s\n' "$adm_reason"
    printf 'parent_compiler_path=%s\n' "$parent_file"
    printf 'parent_compiler_sha256=%s\n' "$parent_sha"
    printf 'parent_stage2_sanity_path=%s\n' "$sanity_file"
    printf 'parent_stage2_sanity_sha256=%s\n' "$sanity_sha"
    printf 'parent_stage2_provenance_path=%s\n' "$prov_file"
    printf 'parent_stage2_provenance_sha256=%s\n' "$prov_sha"
    printf 'runtime_dir=%s\n' "$adm_runtime"
    printf 'runtime_snapshot_path=%s\n' "$adm_dir/runtime.snapshot"
    printf 'runtime_snapshot_sha256=%s\n' "$runtime_sha"
    printf 'planner_source_path=%s\n' "$planner_source"
    printf 'planner_source_sha256=%s\n' "$planner_source_sha"
    printf 'planner_source_closure_snapshot_path=%s\n' "$adm_dir/planner-source-closure.snapshot"
    printf 'planner_source_closure_snapshot_sha256=%s\n' "$closure_sha"
    printf 'git_state_path=%s\n' "$adm_dir/git-state.txt"
    printf 'git_state_sha256=%s\n' "$git_sha"
    printf 'build_argv_sha256=%s\n' "$argv_sha"
    printf 'build_env_sha256=%s\n' "$env_sha"
    printf 'cache_scope_key=%s\n' "$scope_key"
    printf 'planner_path=%s\n' "$adm_dir/planner"
    printf 'planner_sha256=%s\n' "$planner_sha"
    printf 'planner_smoke_path=%s\n' "$adm_dir/planner-smoke.txt"
    printf 'planner_smoke_sha256=%s\n' "$smoke_sha"
    printf 'authorization_receipt_path=%s\n' "$auth_path"
    printf 'authorization_receipt_sha256=%s\n' "$auth_sha"
} >"$adm_out"

bootstrap_planner_v2_verify "$adm_out" "$adm_root" || adm_fail produced-receipt-fails-own-verifier
echo "bootstrap-admission: produced $adm_out"
}

# --- folded: check-stage2-sanity-diagnostic.shs -----------------------------------------
bootstrap_folded_stage2_sanity_diagnostic() {
# Guards the defect in
# doc/08_tracking/bug/simpleos_stage2_bootstrap_sanity_exit2_without_diagnostic_2026-08-20.md :
# the Stage-2 bootstrap sanity gate failed with a non-zero exit and NO
# diagnostic, so the canonical stage diagnosis reported UNDIAGNOSABLE.
#
# A non-zero exit is not the property under test — every fixture below already
# exited non-zero when the bug was live. What is under test is that the failure
# NAMES what failed. Each negative fixture therefore asserts BOTH the non-zero
# exit AND that a 'stage2-sanity-error:' line was emitted mentioning the
# offending field.
#
# Exit status convention:
#   PASS — <n> fixture(s) checked, ... exit 0
#   FAIL — ...                        exit 1
#   ERROR — nothing was checked (...) exit 2
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)

gate_error() {
  printf 'ERROR — nothing was checked (%s)\n' "$1" >&2
  exit 2
}

[ "${1:---selftest}" = --selftest ] ||
  gate_error "usage: check-stage2-sanity-diagnostic.shs [--selftest]"

sanity_lib="$root/scripts/check/lib/bootstrap-stage3/sanity.shs"
[ -f "$sanity_lib" ] || gate_error "sanity library not found: $sanity_lib"

facade="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
[ -f "$facade" ] || gate_error "provenance facade not found: $facade"
BOOTSTRAP_STAGE3_FACADE_PATH="$facade"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "$facade"

work=$(mktemp -d) || gate_error "could not create a temporary work directory"
trap 'rm -rf "$work"' EXIT INT TERM

mkdir -p "$work/repo" "$work/env-home" "$work/env-tmp"

candidate="$work/simple"
cat >"$candidate" <<'CANDIDATE_EOF'
#!/bin/sh
case "$1" in
  --version) printf 'simple-bootstrap 1.0.0-RC\n' ;;
  run) printf "error: unknown command 'run'\n" >&2; exit 1 ;;
  *) exit 1 ;;
esac
CANDIDATE_EOF
chmod +x "$candidate"

candidate_frontend_smoke() { printf 'frontend-ok\n'; }

frontend_log="$work/frontend.log"
candidate_frontend_smoke "$candidate" >"$frontend_log"
unsupported_status=0
unsupported=$("$candidate" run fixture 2>&1) || unsupported_status=$?
[ "$unsupported_status" = 1 ] ||
  gate_error "fixture candidate did not reject 'run' with status 1"
candidate_sha=$(bootstrap_stage3_hash_file "$candidate") ||
  gate_error "fixture candidate could not be hashed"

good="$work/sanity.env"
{
  echo "schema=simple-bootstrap-sanity-evidence-v1"
  echo "status=pass"
  echo "candidate_sha256_before=$candidate_sha"
  echo "version_status=0"
  echo "version_output=simple-bootstrap 1.0.0-RC"
  echo "unsupported_status=1"
  echo "unsupported_output_sha256=$(printf '%s' "$unsupported" | bootstrap_stage3_hash_stream)"
  echo "frontend_smoke_status=0"
  echo "frontend_smoke_bootstrap_mode_status=0"
  echo "frontend_smoke_output_sha256=$(bootstrap_stage3_hash_file "$frontend_log")"
  echo "candidate_sha256_after=$candidate_sha"
} >"$good"

checked=0
failures=""

run_verify() {
  verify_status=0
  verify_err="$work/verify.err.$$"
  bootstrap_stage3_verify_sanity_evidence "$1" "$candidate" "$work/repo" \
    cranelift "$work/env-home" "$work/env-tmp" "/usr/bin:/bin" \
    >/dev/null 2>"$verify_err" || verify_status=$?
  verify_output=$(cat "$verify_err")
  rm -f "$verify_err"
}

# Positive fixture: intact evidence must verify and stay silent.
checked=$((checked + 1))
run_verify "$good"
if [ "$verify_status" != 0 ]; then
  failures="$failures intact-evidence-rejected(status=$verify_status,msg=$verify_output)"
fi

# Negative fixtures: each must produce BOTH a non-zero exit AND a diagnostic
# naming the offending field. The `expect` string is the substring that makes
# the message actionable.
expect_diagnosed() {
  fixture_name=$1
  fixture_file=$2
  fixture_expect=$3
  checked=$((checked + 1))
  run_verify "$fixture_file"
  if [ "$verify_status" = 0 ]; then
    failures="$failures $fixture_name:accepted-bad-evidence"
    return 0
  fi
  case "$verify_output" in
    *stage2-sanity-error:*) ;;
    *) failures="$failures $fixture_name:silent-failure"; return 0 ;;
  esac
  case "$verify_output" in
    *"$fixture_expect"*) ;;
    *) failures="$failures $fixture_name:unactionable-message" ;;
  esac
}

# This is the exact shape of the filed bug: a stale expected version string.
sed 's/^version_output=.*/version_output=simple-bootstrap 1.0.0-beta/' \
  "$good" >"$work/stale-version.env"
expect_diagnosed stale-version "$work/stale-version.env" "version_output"

sed 's/^status=pass$/status=fail/' "$good" >"$work/status.env"
expect_diagnosed status-not-pass "$work/status.env" "status"

grep -v '^candidate_sha256_after=' "$good" >"$work/missing-field.env"
expect_diagnosed missing-field "$work/missing-field.env" "candidate_sha256_after"

sed 's/^candidate_sha256_before=.*/candidate_sha256_before=0000000000000000000000000000000000000000000000000000000000000000/' \
  "$good" >"$work/candidate-sha.env"
expect_diagnosed candidate-sha "$work/candidate-sha.env" "candidate_sha256_before"

sed 's/^frontend_smoke_output_sha256=.*/frontend_smoke_output_sha256=not-a-sha/' \
  "$good" >"$work/frontend-sha.env"
expect_diagnosed frontend-sha "$work/frontend-sha.env" "frontend_smoke_output_sha256"

expect_diagnosed absent-evidence "$work/does-not-exist.env" "missing or is a symlink"

[ "$checked" -gt 0 ] || gate_error "no fixture was executed"

if [ -n "$failures" ]; then
  printf 'FAIL — %s fixture(s) checked,%s\n' "$checked" "$failures"
  exit 1
fi
printf 'PASS — %s fixture(s) checked, every sanity failure emitted an actionable diagnostic\n' "$checked"
}

# --- folded: rollback-bootstrap-deploy.shs -----------------------------------------
bootstrap_folded_rollback_deploy() {
set -eu

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)"
cd "${repo_root}"
if [ "$#" -gt 0 ]; then
  platform=$1
else
  host_os=$(uname -s)
  host_arch=$(uname -m)
  case "${host_os}:${host_arch}" in
    Linux:x86_64) platform=x86_64-unknown-linux-gnu ;;
    Linux:aarch64|Linux:arm64) platform=aarch64-unknown-linux-gnu ;;
    Darwin:x86_64) platform=x86_64-apple-darwin ;;
    Darwin:arm64|Darwin:aarch64) platform=aarch64-apple-darwin ;;
    FreeBSD:x86_64|FreeBSD:amd64) platform=x86_64-unknown-freebsd-elf ;;
    FreeBSD:aarch64|FreeBSD:arm64) platform=aarch64-unknown-freebsd-elf ;;
    MINGW*:x86_64|MSYS*:x86_64) platform=x86_64-pc-windows-gnu ;;
    *) echo "error: unsupported host; pass the canonical platform triple" >&2; exit 2 ;;
  esac
fi
case "${platform}" in '.'|'..'|*[!A-Za-z0-9._-]*|'') echo "error: invalid platform" >&2; exit 2;; esac
deploy_dir="bin/release/${platform}"
receipt="${deploy_dir}/bootstrap-deploy-receipt.env"
rollback_receipt="${deploy_dir}/bootstrap-rollback-receipt.env"
lock="${deploy_dir}/.bootstrap-deploy.lock"
[ ! -L "bin" ] && [ ! -L "bin/release" ] && [ ! -L "${deploy_dir}" ] || { echo "error: symlinked deployment path" >&2; exit 2; }
mkdir "${lock}" 2>/dev/null || { echo "error: deployment is locked" >&2; exit 2; }
trap 'rm -rf "${lock}"' EXIT
trap 'exit 130' HUP INT TERM

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then sha256 -q "$1"
  else echo "error: no SHA-256 tool" >&2; return 1; fi
}
value() { sed -n "s/^$1=//p" "${receipt}" | awk 'NR==1 { value=$0 } END { if (NR==1) print value }'; }
bounded_smoke() {
  smoke_out="${deploy_dir}/.rollback-smoke-out.$$"
  "$1" -c 'print(1+1)' >"${smoke_out}" 2>/dev/null &
  smoke_pid=$!
  (sleep 30; kill "${smoke_pid}" 2>/dev/null || true; sleep 2; kill -KILL "${smoke_pid}" 2>/dev/null || true) &
  watchdog_pid=$!
  smoke_status=0
  wait "${smoke_pid}" || smoke_status=$?
  kill "${watchdog_pid}" 2>/dev/null || true
  wait "${watchdog_pid}" 2>/dev/null || true
  cat "${smoke_out}"
  rm -f "${smoke_out}"
  return "${smoke_status}"
}
fail_receipt() {
  { echo "schema=bootstrap-rollback-receipt-v1"; echo "platform=${platform}"; echo "rollback_status=fail"; echo "reason=$1"; echo "platform_acceptance_claimed=false"; } > "${rollback_receipt}.tmp.$$"
  mv "${rollback_receipt}.tmp.$$" "${rollback_receipt}"
  echo "error: rollback failed: $1" >&2
  exit 1
}

[ -f "${receipt}" ] && [ ! -L "${receipt}" ] || fail_receipt receipt
[ "$(value schema)" = "bootstrap-deploy-receipt-v1" ] || fail_receipt schema
[ "$(value platform)" = "${platform}" ] || fail_receipt platform
current="$(value current_path)"; backup="$(value backup_path)"
[ "${current}" = "${deploy_dir}/simple" ] || [ "${current}" = "${deploy_dir}/simple.exe" ] || fail_receipt current_path
[ "${backup}" = "${current}.pre_deploy" ] || fail_receipt backup_path
[ -f "${current}" ] && [ ! -L "${current}" ] || fail_receipt current_file
[ -f "${backup}" ] && [ ! -L "${backup}" ] || fail_receipt backup_file
expected_current_hash="$(value current_sha256)"
expected_backup_hash="$(value backup_sha256)"
[ "$(hash_file "${current}")" = "${expected_current_hash}" ] || fail_receipt current_hash
[ "$(hash_file "${backup}")" = "${expected_backup_hash}" ] || fail_receipt backup_hash

candidate="${current}.rollback_candidate.$$"
old="${current}.rollback_old.$$"
install -m755 "${backup}" "${candidate}"
[ "$(hash_file "${candidate}")" = "${expected_backup_hash}" ] || { rm -f "${candidate}"; fail_receipt candidate_hash; }
marker='enum construction: unregistered enum'
if ! { grep -a -q "${marker}" "${candidate}" 2>/dev/null && [ "$(bounded_smoke "${candidate}" 2>/dev/null)" = "2" ]; }; then
  rm -f "${candidate}"
  fail_receipt rollback_smoke
fi
install -m755 "${current}" "${old}"
rm -f "${receipt}" "${rollback_receipt}"
mv "${candidate}" "${current}"
if [ "$(uname -s)" != "Windows_NT" ] && ! "${repo_root}/scripts/setup/setup.shs"; then
  mv "${old}" "${current}" || fail_receipt restore_failed
  fail_receipt setup
fi
backup_tmp="${backup}.tmp.$$"
install -m755 "${old}" "${backup_tmp}"
mv "${backup_tmp}" "${backup}"
rm -f "${old}"
{
  echo "schema=bootstrap-rollback-receipt-v1"
  echo "platform=${platform}"
  echo "current_path=${current}"
  echo "current_sha256=$(hash_file "${current}")"
  echo "backup_path=${backup}"
  echo "backup_sha256=$(hash_file "${backup}")"
  echo "timestamp_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "rollback_status=pass"
  echo "platform_acceptance_claimed=false"
} > "${rollback_receipt}.tmp.$$"
mv "${rollback_receipt}.tmp.$$" "${rollback_receipt}"
echo "rollback_status=pass"
echo "rollback_receipt=${rollback_receipt}"
}

# --- folded: stage4-tooling-matrix.shs -----------------------------------------
bootstrap_folded_stage4_tooling_matrix() {
# Durable Stage-4 tools-only matrix. It consumes admitted Stage-3 artifacts;
# it never builds or admits a compiler.
set -u

die() {
  echo "stage4-tooling-matrix: $*" >&2
  exit 2
}

hash_file() {
  sha256sum "$1" | awk '{print $1}'
}

hash_text() {
  sha256sum | awk '{print $1}'
}

absolute_file() {
  absolute_input=$1
  absolute_dir=$(CDPATH= cd -- "$(dirname -- "$absolute_input")" && pwd -P) || return 1
  printf '%s/%s\n' "$absolute_dir" "$(basename -- "$absolute_input")"
}

field() {
  field_key=$1
  field_file=$2
  sed -n "s/^${field_key}=//p" "$field_file" | head -n 1
}

env_keys_once() {
  keys_file=$1
  shift
  [ -f "$keys_file" ] && [ ! -L "$keys_file" ] || return 1
  for keys_key in "$@"; do
    [ "$(awk -F= -v key="$keys_key" '$1 == key { count++ } END { print count + 0 }' "$keys_file")" -eq 1 ] || return 1
  done
}

exact_env_schema() {
  schema_file=$1
  shift
  schema_expected=$#
  env_keys_once "$schema_file" "$@" || return 1
  schema_actual=$(wc -l <"$schema_file" | tr -d ' ')
  [ "$schema_actual" -eq "$schema_expected" ] || return 1
}

matrix_id=
compiler_manifest=
cli_journal=
mcp_journal=
lsp_journal=
linker=cc
scope=full
resume=0
source_root=$(pwd -P)
timeout_seconds=${STAGE4_MATRIX_TIMEOUT_SECONDS:-1800}

for arg in "$@"; do
  case "$arg" in
    --matrix-id=*) matrix_id=${arg#*=} ;;
    --compiler-manifest=*) compiler_manifest=${arg#*=} ;;
    --cli-journal=*) cli_journal=${arg#*=} ;;
    --mcp-journal=*) mcp_journal=${arg#*=} ;;
    --lsp-journal=*) lsp_journal=${arg#*=} ;;
    --linker=*) linker=${arg#*=} ;;
    --scope=*) scope=${arg#*=} ;;
    --source-root=*) source_root=${arg#*=} ;;
    --timeout-seconds=*) timeout_seconds=${arg#*=} ;;
    --resume) resume=1 ;;
    *) die "unknown option: $arg" ;;
  esac
done

case "$matrix_id" in
  ''|*/*|*..*|*[!A-Za-z0-9_-]*) die "matrix id must be a contained identifier" ;;
esac
case "$scope" in full|link-only) ;; *) die "scope must be full or link-only" ;; esac
case "$timeout_seconds" in ''|*[!0-9]*|0) die "timeout must be a positive integer" ;; esac
[ -d "$source_root" ] || die "source root is not a directory"
source_root=$(CDPATH= cd -- "$source_root" && pwd -P) || exit 2
cd "$source_root" || exit 2

[ -f "$compiler_manifest" ] || die "compiler manifest is required"
[ -f "$cli_journal" ] || cli_journal_missing=1
[ -f "$mcp_journal" ] || mcp_journal_missing=1
[ -f "$lsp_journal" ] || lsp_journal_missing=1
compiler_manifest=$(absolute_file "$compiler_manifest") || die "cannot resolve compiler manifest"
[ ! -f "$cli_journal" ] || cli_journal=$(absolute_file "$cli_journal")
[ ! -f "$mcp_journal" ] || mcp_journal=$(absolute_file "$mcp_journal")
[ ! -f "$lsp_journal" ] || lsp_journal=$(absolute_file "$lsp_journal")

runner="$source_root/scripts/bootstrap/bootstrap-from-scratch.sh"
link_wrapper="$runner"
[ -x "$link_wrapper" ] || die "tools-only linker is not executable"
linker_path=$(command -v "$linker" 2>/dev/null) || die "linker is unavailable: $linker"
linker_path=$(absolute_file "$linker_path") || die "cannot resolve linker"

work_rel="build/mini_builds/stage4_tooling_$matrix_id"
work_root="$source_root/$work_rel"
state="$work_root/state"
logs="$work_root/logs"
homes="$work_root/homes"
tmps="$work_root/tmps"
summary="$work_root/summary.env"
matrix="$work_root/matrix.tsv"
config="$work_root/config.env"

if [ -e "$work_root" ] && [ -n "$(find "$work_root" -mindepth 1 -maxdepth 1 -print -quit 2>/dev/null)" ] && [ "$resume" -ne 1 ]; then
  die "matrix evidence already exists; use --resume"
fi
if [ "$resume" -eq 1 ] && { [ ! -f "$matrix" ] || [ ! -f "$config" ]; }; then
  die "resume requires an existing matrix and config"
fi
mkdir -p "$state" "$logs" "$homes" "$tmps" || die "cannot create matrix evidence"

file_hash_or_missing() {
  if [ -f "$1" ]; then hash_file "$1"; else printf 'MISSING\n'; fi
}

tree_hash_or_missing() {
  tree_path=$1
  if [ ! -d "$tree_path" ]; then
    printf 'MISSING\n'
    return 0
  fi
  find "$tree_path" -type f -print | LC_ALL=C sort | while IFS= read -r tree_file; do
    printf '%s\t%s\n' "${tree_file#"$source_root"/}" "$(hash_file "$tree_file")"
  done | hash_text
}

git_head_or_missing() {
  git -C "$source_root" rev-parse HEAD 2>/dev/null || printf 'MISSING\n'
}

git_tracked_dirty_hash() {
  git -C "$source_root" status --porcelain=v1 --untracked-files=no 2>/dev/null | LC_ALL=C sort | hash_text
}

config_tmp="$work_root/config.expected.$$"
matrix_tmp="$work_root/matrix.expected.$$"
trap 'rm -f "$config_tmp" "$matrix_tmp"' EXIT INT TERM HUP
{
  echo "schema=Stage4ToolingMatrixConfigV1"
  echo "matrix_id=$matrix_id"
  echo "scope=$scope"
  echo "source_root=$source_root"
  echo "compiler_manifest_path=$compiler_manifest"
  echo "compiler_manifest_hash=$(hash_file "$compiler_manifest")"
  echo "compiler_source_hash=$(field source_hash "$compiler_manifest")"
  echo "compiler_producer_hash=$(field producer_hash "$compiler_manifest")"
  echo "compiler_backend=$(field backend "$compiler_manifest")"
  echo "compiler_target=$(field target "$compiler_manifest")"
  echo "compiler_identity=$(field compiler_identity "$compiler_manifest")"
  echo "compiler_abi=$(field compiler_abi "$compiler_manifest")"
  echo "runtime_abi=$(field runtime_abi "$compiler_manifest")"
  echo "cli_journal_path=$cli_journal"
  echo "cli_journal_hash=$(file_hash_or_missing "$cli_journal")"
  echo "mcp_journal_path=$mcp_journal"
  echo "mcp_journal_hash=$(file_hash_or_missing "$mcp_journal")"
  echo "lsp_journal_path=$lsp_journal"
  echo "lsp_journal_hash=$(file_hash_or_missing "$lsp_journal")"
  echo "runner_hash=$(hash_file "$runner")"
  echo "link_wrapper_hash=$(hash_file "$link_wrapper")"
  echo "linker_path=$linker_path"
  echo "linker_hash=$(hash_file "$linker_path")"
  echo "compiler_tree_hash=$(tree_hash_or_missing "$source_root/src/compiler")"
  echo "application_tree_hash=$(tree_hash_or_missing "$source_root/src/app")"
  echo "cli_tree_hash=$(tree_hash_or_missing "$source_root/src/app/cli")"
  echo "library_tree_hash=$(tree_hash_or_missing "$source_root/src/lib")"
  echo "mcp_tree_hash=$(tree_hash_or_missing "$source_root/src/app/mcp")"
  echo "lsp_tree_hash=$(tree_hash_or_missing "$source_root/src/app/simple_lsp_mcp")"
  echo "compiler_bootstrap_tests_hash=$(tree_hash_or_missing "$source_root/test/01_unit/compiler/bootstrap")"
  echo "compiler_full_tests_hash=$(tree_hash_or_missing "$source_root/test/01_unit/compiler")"
  echo "compiler_core_tests_hash=$(tree_hash_or_missing "$source_root/test/01_unit/compiler_core")"
  echo "format_fixed_test_hash=$(file_hash_or_missing "$source_root/test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl")"
  echo "mcp_tests_hash=$(tree_hash_or_missing "$source_root/test/01_unit/app/mcp_unit")"
  echo "lsp_tests_hash=$(tree_hash_or_missing "$source_root/test/01_unit/app/lsp")"
  echo "all_tests_hash=$(tree_hash_or_missing "$source_root/test")"
  echo "check_scripts_hash=$(tree_hash_or_missing "$source_root/scripts/check")"
  echo "mcp_config_hash=$(tree_hash_or_missing "$source_root/config/mcp")"
  echo "git_head=$(git_head_or_missing)"
  echo "git_tracked_dirty_hash=$(git_tracked_dirty_hash)"
  echo "timeout_seconds=$timeout_seconds"
} >"$config_tmp"

{
  printf 'link_cli\trequired\t-\n'
  printf 'link_mcp\trequired\t-\n'
  printf 'link_lsp\trequired\t-\n'
  if [ "$scope" = full ]; then
    printf 'cli_help\trequired\tlink_cli\n'
    printf 'cli_version\trequired\tlink_cli\n'
    printf 'mcp_help\trequired\tlink_mcp\n'
    printf 'mcp_version\trequired\tlink_mcp\n'
    printf 'lsp_help\trequired\tlink_lsp\n'
    printf 'lsp_version\trequired\tlink_lsp\n'
    printf 'core_runtime_smoke\trequired\tcli_help,cli_version\n'
    printf 'redeploy_sanity\trequired\tcore_runtime_smoke\n'
    printf 'compiler_check\trequired\tcli_help,cli_version\n'
    printf 'library_check\trequired\tcli_help,cli_version\n'
    printf 'mcp_check\trequired\tcompiler_check,library_check\n'
    printf 'lsp_check\trequired\tcompiler_check,library_check\n'
    printf 'essential_tools\trequired\tcompiler_check,library_check\n'
    printf 'lint_help\trequired\tessential_tools\n'
    printf 'lint_focused\trequired\tlint_help\n'
    printf 'duplicate_help\trequired\tessential_tools\n'
    printf 'duplicate_focused\trequired\tduplicate_help\n'
    printf 'format_fixed_focused_regression\trequired\tessential_tools,lint_focused,duplicate_focused\n'
    printf 'compiler_bootstrap_tests\trequired\tformat_fixed_focused_regression\n'
    printf 'compiler_core_tests\trequired\tessential_tools,lint_focused,duplicate_focused\n'
    printf 'compiler_full_tests\trequired\tcompiler_bootstrap_tests,compiler_core_tests\n'
    printf 'tooling_contract_tests\trequired\tessential_tools\n'
    printf 'mcp_unit_tests\trequired\tmcp_check,essential_tools\n'
    printf 'lsp_unit_tests\trequired\tlsp_check,essential_tools\n'
    printf 'lsp_log_modes_tests\trequired\tlsp_unit_tests,lsp_help,lsp_version\n'
    printf 'mcp_protocol\trequired\tmcp_help,mcp_version,mcp_check\n'
    printf 'mcp_focused\trequired\tmcp_protocol\n'
    printf 'lsp_protocol\trequired\tlsp_help,lsp_version,lsp_check,link_lsp\n'
    printf 'mcp_stdio_integration\trequired\tmcp_protocol,mcp_focused,mcp_unit_tests\n'
    printf 'lsp_stdio_integration\trequired\tlsp_protocol,lsp_unit_tests,lsp_log_modes_tests\n'
    printf 'test_daemon\trequired\tessential_tools\n'
    printf 'examples_check\trequired\tessential_tools\n'
    printf 'fmt\trequired\tessential_tools\n'
    printf 'fix\trequired\tessential_tools\n'
    printf 'verify\trequired\tcompiler_full_tests\n'
    printf 'spipe_docgen\trequired\tcompiler_full_tests\n'
    printf 'native_build\trequired\tredeploy_sanity,compiler_full_tests\n'
    printf 'security\trequired\tlibrary_check\n'
    printf 'build\trequired\tcompiler_check\n'
    printf 'run\trequired\tcore_runtime_smoke\n'
    printf 'doc_coverage\trequired\tlibrary_check\n'
    printf 'vscode_dispatch\trequired\tcli_help\n'
    printf 'electron_dispatch\trequired\tcli_help\n'
    printf 'vscode_external\toptional\tvscode_dispatch\n'
    printf 'electron_external\toptional\telectron_dispatch\n'
    printf 'simple_core_smoke\toptional\tnative_build\n'
  fi
} >"$matrix_tmp"

write_resume_mismatch_summary() {
  mismatch_status=$1
  mismatch_total=$(wc -l <"$matrix" | tr -d ' ')
  mismatch_tmp="$summary.tmp.$$"
  {
    echo "schema=Stage4ToolingMatrixSummaryV1"
    echo "matrix_id=$matrix_id"
    echo "matrix_hash=$(hash_file "$matrix")"
    echo "config_hash=$(hash_file "$config")"
    echo "scope=$scope"
    echo "admission_eligible=false"
    echo "task_total=$mismatch_total"
    echo "terminal_count=0"
    echo "passed=0"
    echo "failed=1"
    echo "blocked=0"
    echo "unsupported=0"
    echo "remaining=$mismatch_total"
    echo "required_not_pass=1"
    echo "optional_failed=0"
    echo "stage4_compiler_files=unknown"
    echo "overall=FAIL"
    echo "status=$mismatch_status"
  } >"$mismatch_tmp"
  mv "$mismatch_tmp" "$summary"
}

if [ "$resume" -eq 1 ]; then
  if ! cmp -s "$config_tmp" "$config"; then
    write_resume_mismatch_summary resume-config-identity-mismatch
    die "resume config identity mismatch"
  fi
  if ! cmp -s "$matrix_tmp" "$matrix"; then
    write_resume_mismatch_summary resume-matrix-identity-mismatch
    die "resume matrix identity mismatch"
  fi
else
  mv "$config_tmp" "$config"
  mv "$matrix_tmp" "$matrix"
fi
matrix_hash=$(hash_file "$matrix")
config_hash=$(hash_file "$config")

frozen_identity_snapshot() {
  {
    echo "compiler_manifest_hash=$(hash_file "$compiler_manifest")"
    echo "compiler_tree_hash=$(tree_hash_or_missing "$source_root/src/compiler")"
    echo "application_tree_hash=$(tree_hash_or_missing "$source_root/src/app")"
    echo "cli_tree_hash=$(tree_hash_or_missing "$source_root/src/app/cli")"
    echo "library_tree_hash=$(tree_hash_or_missing "$source_root/src/lib")"
    echo "mcp_tree_hash=$(tree_hash_or_missing "$source_root/src/app/mcp")"
    echo "lsp_tree_hash=$(tree_hash_or_missing "$source_root/src/app/simple_lsp_mcp")"
    echo "all_tests_hash=$(tree_hash_or_missing "$source_root/test")"
    echo "check_scripts_hash=$(tree_hash_or_missing "$source_root/scripts/check")"
    echo "mcp_config_hash=$(tree_hash_or_missing "$source_root/config/mcp")"
    echo "runner_hash=$(hash_file "$runner")"
    echo "link_wrapper_hash=$(hash_file "$link_wrapper")"
    echo "git_head=$(git_head_or_missing)"
    echo "git_tracked_dirty_hash=$(git_tracked_dirty_hash)"
  }
}

frozen_identity_stable() {
  frozen_identity_snapshot | while IFS='=' read -r frozen_key frozen_value; do
    [ "$(field "$frozen_key" "$config")" = "$frozen_value" ] || exit 1
  done
}

write_identity_snapshot() {
  snapshot_task=$1
  snapshot_phase=$2
  frozen_identity_snapshot >"$state/$snapshot_task.identity-$snapshot_phase"
}

task_required() {
  awk -F '\t' -v task="$1" '$1 == task { print $2; exit }' "$matrix"
}

tool_output() {
  case "$1" in
    cli) printf '%s/build/stage4-tools/%s_cli/simple\n' "$source_root" "$matrix_id" ;;
    mcp) printf '%s/build/stage4-tools/%s_mcp/simple_mcp_server\n' "$source_root" "$matrix_id" ;;
    lsp) printf '%s/build/stage4-tools/%s_lsp/simple_lsp_mcp_server\n' "$source_root" "$matrix_id" ;;
  esac
}

tool_publish_rel() {
  printf 'build/stage4-tools/%s_%s\n' "$matrix_id" "$1"
}

tool_cache_rel() {
  printf 'build/mini_cache_stage4_%s_%s\n' "$matrix_id" "$1"
}

tool_entry() {
  case "$1" in
    cli) printf 'src/app/cli/main.spl\n' ;;
    mcp) printf 'src/app/mcp/main.spl\n' ;;
    lsp) printf 'src/app/simple_lsp_mcp/main.spl\n' ;;
  esac
}

tool_journal() {
  case "$1" in cli) printf '%s\n' "$cli_journal" ;; mcp) printf '%s\n' "$mcp_journal" ;; lsp) printf '%s\n' "$lsp_journal" ;; esac
}

path_fingerprint() {
  fingerprint_path=$1
  if [ -f "$fingerprint_path" ]; then
    printf '%s:%s\n' "$fingerprint_path" "$(hash_file "$fingerprint_path")"
  elif [ -d "$fingerprint_path" ]; then
    printf '%s:TREE:%s\n' "$fingerprint_path" "$(tree_hash_or_missing "$fingerprint_path")"
  else
    printf '%s:MISSING\n' "$fingerprint_path"
  fi
}

task_input_fingerprint() {
  input_task=$1
  {
    input_required=$(task_required "$input_task")
    input_deps=$(awk -F '\t' -v task="$input_task" '$1 == task { print $3; exit }' "$matrix")
    echo "task=$input_task"
    echo "required=$input_required"
    echo "dependencies=$input_deps"
    echo "matrix=$matrix_hash"
    echo "config=$config_hash"
    path_fingerprint "$compiler_manifest"
    if [ "$input_deps" != - ]; then
      printf '%s\n' "$input_deps" | tr ',' '\n' | while IFS= read -r input_dep; do
        path_fingerprint "$state/$input_dep.env"
      done
    fi
    case "$input_task" in
      link_cli|link_mcp|link_lsp)
        input_tool=${input_task#link_}
        input_journal=$(tool_journal "$input_tool")
        path_fingerprint "$input_journal"
        awk -F '\t' '$1 == "unit" { print $2; print $4 }' "$input_journal" 2>/dev/null | while IFS= read -r input_unit_path; do
          case "$input_unit_path" in
            /*) path_fingerprint "$input_unit_path" ;;
            *) path_fingerprint "$source_root/${input_unit_path#./}" ;;
          esac
        done
        echo "tool=$input_tool"
        echo "entry=$(tool_entry "$input_tool")"
        ;;
      cli_help|cli_version)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$(dirname "$(tool_output cli)")/ToolingLinkReceiptV1.env"
        ;;
      mcp_help|mcp_version)
        path_fingerprint "$(tool_output mcp)"
        path_fingerprint "$(dirname "$(tool_output mcp)")/ToolingLinkReceiptV1.env"
        ;;
      lsp_help|lsp_version)
        path_fingerprint "$(tool_output lsp)"
        path_fingerprint "$(dirname "$(tool_output lsp)")/ToolingLinkReceiptV1.env"
        ;;
      core_runtime_smoke)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/check-core-runtime-smoke.shs"
        ;;
      redeploy_sanity)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/cert/redeploy_gate/redeploy_gate.shs"
        ;;
      essential_tools)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/check-bootstrap-essential-tools-smoke.shs"
        path_fingerprint "$source_root/test/fixtures/pure_simple_tooling"
        path_fingerprint "$source_root/test/fixtures/duplication"
        path_fingerprint "$source_root/scripts/check/fixtures"
        path_fingerprint "$source_root/scripts/check/validate-json.spl"
        path_fingerprint "$source_root/scripts/check/validate-jsonl.spl"
        path_fingerprint "$source_root/scripts/check/check-dedicated-host-startup-wiring.shs"
        path_fingerprint "$source_root/test/01_unit/lib/core/list_constructor_hardening_spec.spl"
        ;;
      lint_help|lint_focused)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/cli/lint_entry.spl"
        path_fingerprint "$source_root/test/fixtures/pure_simple_tooling/clean.spl"
        ;;
      duplicate_help|duplicate_focused)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/compiler/90.tools/duplicate_check/main.spl"
        path_fingerprint "$source_root/test/fixtures/duplication/dup_pair"
        path_fingerprint "$source_root/scripts/check/validate-json.spl"
        ;;
      compiler_check)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/compiler"
        ;;
      library_check)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/lib"
        ;;
      mcp_check)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/mcp"
        ;;
      lsp_check)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/simple_lsp_mcp"
        ;;
      compiler_bootstrap_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/compiler/bootstrap"
        path_fingerprint "$source_root/src/compiler"
        ;;
      compiler_core_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/compiler_core"
        path_fingerprint "$source_root/src/compiler"
        ;;
      compiler_full_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/compiler"
        path_fingerprint "$source_root/src/compiler"
        ;;
      format_fixed_focused_regression)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl"
        path_fingerprint "$source_root/src/compiler"
        path_fingerprint "$source_root/src/lib/std/common/format/format_fixed.spl"
        ;;
      mcp_protocol|mcp_focused)
        path_fingerprint "$(tool_output mcp)"
        path_fingerprint "$source_root/src/app/mcp"
        path_fingerprint "$source_root/src/lib/std/mcp_sdk"
        ;;
      lsp_protocol)
        path_fingerprint "$(tool_output lsp)"
        path_fingerprint "$source_root/src/app/simple_lsp_mcp"
        path_fingerprint "$source_root/scripts/smoke/simple_lsp_protocol_smoke.spl"
        ;;
      tooling_contract_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/lib/tooling/bootstrap_stage_split_spec.spl"
        path_fingerprint "$source_root/test/02_integration/app/cli/stage4_tools_only_manifest_spec.spl"
        ;;
      mcp_unit_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/app/mcp_unit"
        ;;
      lsp_unit_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/01_unit/app/lsp"
        ;;
      lsp_log_modes_tests)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$(tool_output lsp)"
        path_fingerprint "$source_root/test/02_integration/app/simple_lsp_mcp_log_modes_spec.spl"
        ;;
      mcp_stdio_integration)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$(tool_output mcp)"
        path_fingerprint "$source_root/test/02_integration/app/mcp_stdio_integration_spec.spl"
        path_fingerprint "$source_root/scripts/check/check-mcp-wrapper-contract.shs"
        path_fingerprint "$source_root/scripts/setup/setup.shs"
        path_fingerprint "$source_root/config/mcp"
        path_fingerprint "$source_root/bin/simple_lsp_mcp_server.cmd"
        ;;
      lsp_stdio_integration)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$(tool_output lsp)"
        path_fingerprint "$source_root/test/02_integration/app/simple_lsp_mcp_stdio_spec.spl"
        path_fingerprint "$source_root/bin/mcp_stdio_bridge.js"
        ;;
      test_daemon)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/test_daemon"
        ;;
      examples_check)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl"
        ;;
      fmt)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/fixtures/fmt/unformatted.spl"
        ;;
      fix)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/fixtures/pure_simple_tooling/clean.spl"
        ;;
      verify)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/verify"
        ;;
      spipe_docgen)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/fixtures/pure_simple_tooling/sibling_describe_green_spec.spl"
        ;;
      native_build|run)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl"
        ;;
      security)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/fixtures/pure_simple_tooling/clean.spl"
        ;;
      build)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/build/cli_entry.spl"
        ;;
      doc_coverage)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/test/fixtures/doc_coverage"
        ;;
      vscode_dispatch|vscode_external)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/cli/vscode_entry.spl"
        path_fingerprint "$source_root/src/app/vscode_extension/package.json"
        ;;
      electron_dispatch|electron_external)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/src/app/cli/electron_entry.spl"
        path_fingerprint "$source_root/tools/electron-shell/package.json"
        ;;
      simple_core_smoke)
        path_fingerprint "$(tool_output cli)"
        path_fingerprint "$source_root/scripts/check/check-simple-core-runtime-smoke.shs"
        ;;
    esac
  } | hash_text
}

write_task_input_snapshot() {
  input_snapshot_task=$1
  input_snapshot_phase=$2
  task_input_fingerprint "$input_snapshot_task" >"$state/$input_snapshot_task.input-$input_snapshot_phase"
}

task_input_unchanged() {
  unchanged_task=$1
  [ -f "$state/$unchanged_task.input-before" ] && [ ! -L "$state/$unchanged_task.input-before" ] || return 1
  [ -f "$state/$unchanged_task.input-after" ] && [ ! -L "$state/$unchanged_task.input-after" ] || return 1
  [ "$(cat "$state/$unchanged_task.input-before")" = "$(cat "$state/$unchanged_task.input-after")" ]
}

write_task_receipt() {
  receipt_task=$1
  receipt_result=$2
  receipt_status=$3
  receipt_input=$4
  receipt_log=$5
  receipt_output=$6
  receipt_output_hash=$7
  receipt_file="$state/$receipt_task.env"
  receipt_tmp="$receipt_file.tmp.$$"
  receipt_log_hash=-
  [ ! -f "$receipt_log" ] || receipt_log_hash=$(hash_file "$receipt_log")
  receipt_command_executed=true
  case "$receipt_result" in BLOCKED_UPSTREAM|UNSUPPORTED) receipt_command_executed=false ;; esac
  receipt_test_executed=false
  receipt_executed_test_count=0
  if [ -f "$state/$receipt_task.executed-tests" ]; then
    receipt_executed_test_count=$(cat "$state/$receipt_task.executed-tests")
    case "$receipt_executed_test_count" in ''|*[!0-9]*) receipt_executed_test_count=0 ;; esac
    [ "$receipt_executed_test_count" -eq 0 ] || receipt_test_executed=true
  fi
  receipt_pass_marker=-
  receipt_pass_marker_path=-
  receipt_pass_marker_hash=-
  if [ -f "$state/$receipt_task.pass-marker" ] && [ ! -L "$state/$receipt_task.pass-marker" ]; then
    receipt_pass_marker=$(cat "$state/$receipt_task.pass-marker")
    receipt_pass_marker_path="$state/$receipt_task.pass-marker"
    receipt_pass_marker_hash=$(hash_file "$receipt_pass_marker_path")
  fi
  receipt_executed_tests_path=-
  receipt_executed_tests_hash=-
  if [ -f "$state/$receipt_task.executed-tests" ] && [ ! -L "$state/$receipt_task.executed-tests" ]; then
    receipt_executed_tests_path="$state/$receipt_task.executed-tests"
    receipt_executed_tests_hash=$(hash_file "$receipt_executed_tests_path")
  fi
  receipt_support_status=supported
  receipt_unsupported_reason=-
  if [ "$receipt_result" = UNSUPPORTED ]; then
    receipt_support_status=unsupported
    receipt_unsupported_reason=$receipt_status
  fi
  receipt_command_path="$logs/$receipt_task.command"
  receipt_command_hash=-
  if [ -f "$receipt_command_path" ] && [ ! -L "$receipt_command_path" ]; then
    receipt_command_hash=$(hash_file "$receipt_command_path")
  else
    receipt_command_path=-
  fi
  receipt_identity_before="$state/$receipt_task.identity-before"
  receipt_identity_after="$state/$receipt_task.identity-after"
  receipt_identity_before_hash=-
  receipt_identity_after_hash=-
  [ ! -f "$receipt_identity_before" ] || [ -L "$receipt_identity_before" ] || receipt_identity_before_hash=$(hash_file "$receipt_identity_before")
  [ ! -f "$receipt_identity_after" ] || [ -L "$receipt_identity_after" ] || receipt_identity_after_hash=$(hash_file "$receipt_identity_after")
  receipt_input_before=-
  receipt_input_after=-
  [ ! -f "$state/$receipt_task.input-before" ] || receipt_input_before=$(cat "$state/$receipt_task.input-before")
  [ ! -f "$state/$receipt_task.input-after" ] || receipt_input_after=$(cat "$state/$receipt_task.input-after")
  {
    echo "schema=Stage4MatrixTaskReceiptV1"
    echo "task_id=$receipt_task"
    echo "required=$(task_required "$receipt_task")"
    echo "result=$receipt_result"
    echo "status=$receipt_status"
    echo "input_fingerprint=$receipt_input"
    echo "log_path=$receipt_log"
    echo "log_hash=$receipt_log_hash"
    echo "output_path=$receipt_output"
    echo "output_hash=$receipt_output_hash"
    echo "command_executed=$receipt_command_executed"
    echo "test_executed=$receipt_test_executed"
    echo "executed_test_count=$receipt_executed_test_count"
    echo "pass_marker=$receipt_pass_marker"
    echo "pass_marker_path=$receipt_pass_marker_path"
    echo "pass_marker_hash=$receipt_pass_marker_hash"
    echo "executed_tests_path=$receipt_executed_tests_path"
    echo "executed_tests_hash=$receipt_executed_tests_hash"
    echo "support_status=$receipt_support_status"
    echo "unsupported_reason=$receipt_unsupported_reason"
    echo "matrix_hash=$matrix_hash"
    echo "config_hash=$config_hash"
    echo "compiler_manifest_path=$compiler_manifest"
    echo "compiler_manifest_hash=$(hash_file "$compiler_manifest")"
    echo "compiler_identity=$(field compiler_identity "$config")"
    echo "compiler_abi=$(field compiler_abi "$config")"
    echo "runtime_abi=$(field runtime_abi "$config")"
    echo "compiler_tree_hash=$(field compiler_tree_hash "$config")"
    echo "application_tree_hash=$(field application_tree_hash "$config")"
    echo "library_tree_hash=$(field library_tree_hash "$config")"
    echo "mcp_tree_hash=$(field mcp_tree_hash "$config")"
    echo "lsp_tree_hash=$(field lsp_tree_hash "$config")"
    echo "all_tests_hash=$(field all_tests_hash "$config")"
    echo "command_path=$receipt_command_path"
    echo "command_hash=$receipt_command_hash"
    echo "identity_before_hash=$receipt_identity_before_hash"
    echo "identity_after_hash=$receipt_identity_after_hash"
    echo "input_fingerprint_before=$receipt_input_before"
    echo "input_fingerprint_after=$receipt_input_after"
  } >"$receipt_tmp"
  mv "$receipt_tmp" "$receipt_file"
}

task_is_test() {
  case "$1" in
    format_fixed_focused_regression|compiler_bootstrap_tests|compiler_core_tests|compiler_full_tests|tooling_contract_tests|mcp_unit_tests|lsp_unit_tests|lsp_log_modes_tests|mcp_stdio_integration|lsp_stdio_integration)
      return 0
      ;;
  esac
  return 1
}

tool_receipt_valid() {
  valid_tool=$1
  valid_output=$(tool_output "$valid_tool")
  valid_receipt="$(dirname "$valid_output")/ToolingLinkReceiptV1.env"
  [ -x "$valid_output" ] && [ ! -L "$valid_output" ] &&
    [ -f "$valid_receipt" ] && [ ! -L "$valid_receipt" ] || return 1
  exact_env_schema "$valid_receipt" \
    schema_version tool_id entry_path compiler_manifest_hash compiler_manifest_file_hash \
    source_hash producer_hash backend target compiler_identity compiler_executable_hash \
    compiler_archive_hash compiler_interface_hash runtime_archive_hash compiler_abi runtime_abi \
    tool_compile_journal_hash compiled_unit_count source_set_hash object_set_hash \
    entry_source_hash entry_object_hash compiler_sources_compiled stage4_compiler_files \
    output_path output_hash help_smoke_passed version_smoke_passed || return 1
  env_keys_once "$compiler_manifest" \
    schema_version source_hash producer_hash backend target compiler_abi runtime_abi compiler_identity \
    admission_receipt_path admission_receipt_hash compiler_executable_path compiler_executable_hash \
    compiler_archive_path compiler_archive_hash compiler_interface_path compiler_interface_hash \
    runtime_archive_path runtime_archive_hash || return 1
  [ "$(field schema_version "$compiler_manifest")" = CompilerArtifactManifestV1 ] || return 1
  [ "$(field schema_version "$valid_receipt")" = ToolingLinkReceiptV1 ] || return 1
  [ "$(field tool_id "$valid_receipt")" = "$valid_tool" ] || return 1
  [ "$(field entry_path "$valid_receipt")" = "$(tool_entry "$valid_tool")" ] || return 1
  valid_journal=$(tool_journal "$valid_tool")
  [ -f "$valid_journal" ] && [ ! -L "$valid_journal" ] || return 1
  [ "$(field tool_compile_journal_hash "$valid_receipt")" = "$(hash_file "$valid_journal")" ] || return 1
  valid_units=0
  valid_tab=$(printf '\t')
  while IFS="$valid_tab" read -r valid_kind valid_source valid_source_hash valid_object valid_object_hash valid_extra; do
    [ "$valid_kind" = unit ] || continue
    [ -z "${valid_extra:-}" ] || return 1
    case "$valid_source" in /*) valid_source_path=$valid_source ;; *) valid_source_path="$source_root/${valid_source#./}" ;; esac
    case "$valid_object" in /*) valid_object_path=$valid_object ;; *) valid_object_path="$source_root/${valid_object#./}" ;; esac
    [ -f "$valid_source_path" ] && [ ! -L "$valid_source_path" ] || return 1
    [ -f "$valid_object_path" ] && [ ! -L "$valid_object_path" ] || return 1
    [ "$(hash_file "$valid_source_path")" = "$valid_source_hash" ] || return 1
    [ "$(hash_file "$valid_object_path")" = "$valid_object_hash" ] || return 1
    valid_units=$((valid_units + 1))
  done <"$valid_journal"
  [ "$valid_units" -eq "$(field compiled_unit_count "$valid_receipt")" ] || return 1
  [ "$(field compiler_manifest_file_hash "$valid_receipt")" = "$(hash_file "$compiler_manifest")" ] || return 1
  [ "$(field source_hash "$valid_receipt")" = "$(field source_hash "$compiler_manifest")" ] || return 1
  [ "$(field producer_hash "$valid_receipt")" = "$(field producer_hash "$compiler_manifest")" ] || return 1
  [ "$(field backend "$valid_receipt")" = "$(field backend "$compiler_manifest")" ] || return 1
  [ "$(field target "$valid_receipt")" = "$(field target "$compiler_manifest")" ] || return 1
  [ "$(field compiler_identity "$valid_receipt")" = "$(field compiler_identity "$compiler_manifest")" ] || return 1
  [ "$(field compiler_abi "$valid_receipt")" = "$(field compiler_abi "$compiler_manifest")" ] || return 1
  [ "$(field runtime_abi "$valid_receipt")" = "$(field runtime_abi "$compiler_manifest")" ] || return 1
  for valid_artifact_key in admission_receipt compiler_executable compiler_archive compiler_interface runtime_archive; do
    valid_artifact_path=$(field "${valid_artifact_key}_path" "$compiler_manifest")
    valid_artifact_hash=$(field "${valid_artifact_key}_hash" "$compiler_manifest")
    [ -f "$valid_artifact_path" ] && [ ! -L "$valid_artifact_path" ] || return 1
    [ "$(hash_file "$valid_artifact_path")" = "$valid_artifact_hash" ] || return 1
  done
  valid_admission=$(field admission_receipt_path "$compiler_manifest")
  env_keys_once "$valid_admission" schema_version admission_status compiler_identity backend target \
    compiler_abi runtime_abi compiler_executable_hash compiler_archive_hash \
    compiler_interface_hash runtime_archive_hash || return 1
  [ "$(field schema_version "$valid_admission")" = Stage3AdmissionReceiptV1 ] || return 1
  [ "$(field admission_status "$valid_admission")" = PASS ] || return 1
  for valid_admission_key in compiler_identity backend target compiler_abi runtime_abi \
    compiler_executable_hash compiler_archive_hash compiler_interface_hash runtime_archive_hash; do
    [ "$(field "$valid_admission_key" "$valid_admission")" = "$(field "$valid_admission_key" "$compiler_manifest")" ] || return 1
  done
  [ "$(field compiled_unit_count "$valid_receipt")" -gt 0 ] 2>/dev/null || return 1
  valid_entry_hash=$(hash_file "$source_root/$(tool_entry "$valid_tool")")
  [ "$(field entry_source_hash "$valid_receipt")" = "$valid_entry_hash" ] || return 1
  [ -n "$(field entry_object_hash "$valid_receipt")" ] || return 1
  [ "$(field stage4_compiler_files "$valid_receipt")" = 0 ] || return 1
  [ "$(field compiler_sources_compiled "$valid_receipt")" = 0 ] || return 1
  [ "$(field help_smoke_passed "$valid_receipt")" = false ] || return 1
  [ "$(field version_smoke_passed "$valid_receipt")" = false ] || return 1
  [ "$(field output_path "$valid_receipt")" = "$(tool_publish_rel "$valid_tool")/$(basename "$valid_output")" ] || return 1
  [ "$(field output_hash "$valid_receipt")" = "$(hash_file "$valid_output")" ] || return 1
}

receipt_reusable() {
  reusable_task=$1
  reusable_input=$2
  reusable_receipt="$state/$reusable_task.env"
  [ -f "$reusable_receipt" ] && [ ! -L "$reusable_receipt" ] || return 1
  [ "$(field schema "$reusable_receipt")" = Stage4MatrixTaskReceiptV1 ] || return 1
  [ "$(field task_id "$reusable_receipt")" = "$reusable_task" ] || return 1
  [ "$(field required "$reusable_receipt")" = "$(task_required "$reusable_task")" ] || return 1
  [ "$(field matrix_hash "$reusable_receipt")" = "$matrix_hash" ] || return 1
  [ "$(field config_hash "$reusable_receipt")" = "$config_hash" ] || return 1
  reusable_result=$(field result "$reusable_receipt")
  case "$reusable_result" in PASS|UNSUPPORTED) ;; *) return 1 ;; esac
  if [ "$reusable_result" = UNSUPPORTED ]; then
    [ "$(task_required "$reusable_task")" = optional ] || return 1
    [ "$(field support_status "$reusable_receipt")" = unsupported ] || return 1
    [ "$(field unsupported_reason "$reusable_receipt")" != - ] || return 1
    [ "$(field command_executed "$reusable_receipt")" = false ] || return 1
    [ "$(field command_path "$reusable_receipt")" = - ] || return 1
  fi
  if [ "$reusable_result" = PASS ]; then
    [ "$(field command_executed "$reusable_receipt")" = true ] || return 1
    reusable_command=$(field command_path "$reusable_receipt")
    [ -f "$reusable_command" ] && [ ! -L "$reusable_command" ] || return 1
    [ "$(hash_file "$reusable_command")" = "$(field command_hash "$reusable_receipt")" ] || return 1
    reusable_marker=$(field pass_marker_path "$reusable_receipt")
    [ -f "$reusable_marker" ] && [ ! -L "$reusable_marker" ] || return 1
    [ "$(hash_file "$reusable_marker")" = "$(field pass_marker_hash "$reusable_receipt")" ] || return 1
    [ "$(cat "$reusable_marker")" = "$(field pass_marker "$reusable_receipt")" ] || return 1
    if task_is_test "$reusable_task"; then
      [ "$(field test_executed "$reusable_receipt")" = true ] || return 1
      [ "$(field executed_test_count "$reusable_receipt")" -gt 0 ] 2>/dev/null || return 1
      [ "$(field pass_marker "$reusable_receipt")" != - ] || return 1
      reusable_executed=$(field executed_tests_path "$reusable_receipt")
      [ -f "$reusable_executed" ] && [ ! -L "$reusable_executed" ] || return 1
      [ "$(hash_file "$reusable_executed")" = "$(field executed_tests_hash "$reusable_receipt")" ] || return 1
      [ "$(cat "$reusable_executed")" = "$(field executed_test_count "$reusable_receipt")" ] || return 1
    fi
    reusable_output=$(field output_path "$reusable_receipt")
    reusable_output_hash=$(field output_hash "$reusable_receipt")
    if [ "$reusable_output" != - ]; then
      [ -f "$reusable_output" ] && [ ! -L "$reusable_output" ] || return 1
      [ "$(hash_file "$reusable_output")" = "$reusable_output_hash" ] || return 1
    fi
  fi
  reusable_before="$state/$reusable_task.identity-before"
  reusable_after="$state/$reusable_task.identity-after"
  [ -f "$reusable_before" ] && [ ! -L "$reusable_before" ] &&
    [ -f "$reusable_after" ] && [ ! -L "$reusable_after" ] || return 1
  [ "$(hash_file "$reusable_before")" = "$(field identity_before_hash "$reusable_receipt")" ] || return 1
  [ "$(hash_file "$reusable_after")" = "$(field identity_after_hash "$reusable_receipt")" ] || return 1
  [ "$(hash_file "$reusable_before")" = "$(hash_file "$reusable_after")" ] || return 1
  frozen_identity_stable || return 1
  [ "$(field input_fingerprint "$reusable_receipt")" = "$reusable_input" ] || return 1
  reusable_input_before="$state/$reusable_task.input-before"
  reusable_input_after="$state/$reusable_task.input-after"
  [ -f "$reusable_input_before" ] && [ ! -L "$reusable_input_before" ] &&
    [ -f "$reusable_input_after" ] && [ ! -L "$reusable_input_after" ] || return 1
  [ "$(cat "$reusable_input_before")" = "$reusable_input" ] || return 1
  [ "$(cat "$reusable_input_after")" = "$reusable_input" ] || return 1
  [ "$(field input_fingerprint_before "$reusable_receipt")" = "$reusable_input" ] || return 1
  [ "$(field input_fingerprint_after "$reusable_receipt")" = "$reusable_input" ] || return 1
  reusable_log=$(field log_path "$reusable_receipt")
  reusable_log_hash=$(field log_hash "$reusable_receipt")
  if [ "$reusable_log" != - ]; then
    [ -f "$reusable_log" ] && [ ! -L "$reusable_log" ] || return 1
    [ "$(hash_file "$reusable_log")" = "$reusable_log_hash" ] || return 1
  fi
  if [ "$reusable_result" = PASS ]; then
    case "$reusable_task" in
      link_cli) tool_receipt_valid cli || return 1 ;;
      link_mcp) tool_receipt_valid mcp || return 1 ;;
      link_lsp) tool_receipt_valid lsp || return 1 ;;
    esac
  fi
}

receipt_envelope_valid() {
  envelope_task=$1
  envelope_required=$2
  envelope_receipt="$state/$envelope_task.env"
  [ -f "$envelope_receipt" ] && [ ! -L "$envelope_receipt" ] || return 1
  exact_env_schema "$envelope_receipt" \
    schema task_id required result status input_fingerprint log_path log_hash output_path output_hash \
    command_executed test_executed executed_test_count pass_marker pass_marker_path pass_marker_hash \
    executed_tests_path executed_tests_hash support_status unsupported_reason matrix_hash config_hash \
    compiler_manifest_path compiler_manifest_hash compiler_identity compiler_abi runtime_abi \
    compiler_tree_hash application_tree_hash library_tree_hash mcp_tree_hash lsp_tree_hash all_tests_hash \
    command_path command_hash identity_before_hash identity_after_hash input_fingerprint_before \
    input_fingerprint_after || return 1
  [ "$(field schema "$envelope_receipt")" = Stage4MatrixTaskReceiptV1 ] || return 1
  [ "$(field task_id "$envelope_receipt")" = "$envelope_task" ] || return 1
  [ "$(field required "$envelope_receipt")" = "$envelope_required" ] || return 1
  [ "$(field matrix_hash "$envelope_receipt")" = "$matrix_hash" ] || return 1
  [ "$(field config_hash "$envelope_receipt")" = "$config_hash" ] || return 1
  envelope_input=$(task_input_fingerprint "$envelope_task")
  [ "$(field input_fingerprint "$envelope_receipt")" = "$envelope_input" ] || return 1
  envelope_input_before="$state/$envelope_task.input-before"
  envelope_input_after="$state/$envelope_task.input-after"
  [ -f "$envelope_input_before" ] && [ ! -L "$envelope_input_before" ] &&
    [ -f "$envelope_input_after" ] && [ ! -L "$envelope_input_after" ] || return 1
  [ "$(cat "$envelope_input_before")" = "$envelope_input" ] || return 1
  [ "$(cat "$envelope_input_after")" = "$envelope_input" ] || return 1
  [ "$(field input_fingerprint_before "$envelope_receipt")" = "$envelope_input" ] || return 1
  [ "$(field input_fingerprint_after "$envelope_receipt")" = "$envelope_input" ] || return 1
  envelope_before="$state/$envelope_task.identity-before"
  envelope_after="$state/$envelope_task.identity-after"
  [ -f "$envelope_before" ] && [ ! -L "$envelope_before" ] &&
    [ -f "$envelope_after" ] && [ ! -L "$envelope_after" ] || return 1
  [ "$(hash_file "$envelope_before")" = "$(field identity_before_hash "$envelope_receipt")" ] || return 1
  [ "$(hash_file "$envelope_after")" = "$(field identity_after_hash "$envelope_receipt")" ] || return 1
  envelope_log=$(field log_path "$envelope_receipt")
  [ -f "$envelope_log" ] && [ ! -L "$envelope_log" ] || return 1
  [ "$(hash_file "$envelope_log")" = "$(field log_hash "$envelope_receipt")" ] || return 1
  envelope_result=$(field result "$envelope_receipt")
  case "$envelope_result" in
    PASS|UNSUPPORTED)
      receipt_reusable "$envelope_task" "$envelope_input" || return 1
      ;;
    FAIL|CRASH|TIMEOUT)
      [ "$(field command_executed "$envelope_receipt")" = true ] || return 1
      envelope_command=$(field command_path "$envelope_receipt")
      [ -f "$envelope_command" ] && [ ! -L "$envelope_command" ] || return 1
      [ "$(hash_file "$envelope_command")" = "$(field command_hash "$envelope_receipt")" ] || return 1
      ;;
    BLOCKED_UPSTREAM)
      [ "$(field command_executed "$envelope_receipt")" = false ] || return 1
      [ "$(field command_path "$envelope_receipt")" = - ] || return 1
      ;;
    *) return 1 ;;
  esac
}

write_summary() {
  summary_tmp="$summary.tmp.$$"
  total=$(wc -l <"$matrix" | tr -d ' ')
  terminal=0
  passed=0
  failed=0
  blocked=0
  unsupported=0
  required_not_pass=0
  optional_failed=0
  while IFS="$(printf '\t')" read -r summary_task summary_required summary_deps; do
    summary_receipt="$state/$summary_task.env"
    [ -f "$summary_receipt" ] || continue
    terminal=$((terminal + 1))
    if receipt_envelope_valid "$summary_task" "$summary_required"; then
      summary_result=$(field result "$summary_receipt")
    else
      summary_result=INVALID_RECEIPT
    fi
    case "$summary_result" in
      PASS) passed=$((passed + 1)) ;;
      BLOCKED_UPSTREAM) blocked=$((blocked + 1)) ;;
      UNSUPPORTED) unsupported=$((unsupported + 1)) ;;
      *) failed=$((failed + 1)) ;;
    esac
    if [ "$summary_required" = required ] && [ "$summary_result" != PASS ]; then
      required_not_pass=$((required_not_pass + 1))
    fi
    if [ "$summary_required" = optional ]; then
      case "$summary_result" in PASS|UNSUPPORTED) ;; *) optional_failed=$((optional_failed + 1)) ;; esac
    fi
  done <"$matrix"
  stage4_compiler_files=unknown
  if [ "$required_not_pass" -eq 0 ] && [ "$optional_failed" -eq 0 ] &&
     [ "$(field result "$state/link_cli.env" 2>/dev/null)" = PASS ] &&
     [ "$(field result "$state/link_mcp.env" 2>/dev/null)" = PASS ] &&
     [ "$(field result "$state/link_lsp.env" 2>/dev/null)" = PASS ] &&
     tool_receipt_valid cli && tool_receipt_valid mcp && tool_receipt_valid lsp &&
     frozen_identity_stable; then
    stage4_compiler_files=0
  fi
  overall=RUNNING
  if [ "$terminal" -eq "$total" ]; then
    if [ "$required_not_pass" -eq 0 ] && [ "$optional_failed" -eq 0 ]; then
      if [ "$scope" = full ]; then overall=PASS; else overall=SCOPED_PASS; fi
    elif [ "$blocked" -gt 0 ]; then
      overall=BLOCKED
    else
      overall=FAIL
    fi
  fi
  {
    echo "schema=Stage4ToolingMatrixSummaryV1"
    echo "matrix_id=$matrix_id"
    echo "matrix_hash=$matrix_hash"
    echo "config_hash=$config_hash"
    echo "scope=$scope"
    echo "admission_eligible=$([ "$overall" = PASS ] && echo true || echo false)"
    echo "task_total=$total"
    echo "terminal_count=$terminal"
    echo "passed=$passed"
    echo "failed=$failed"
    echo "blocked=$blocked"
    echo "unsupported=$unsupported"
    echo "remaining=$((total - terminal))"
    echo "required_not_pass=$required_not_pass"
    echo "optional_failed=$optional_failed"
    echo "stage4_compiler_files=$stage4_compiler_files"
    echo "overall=$overall"
  } >"$summary_tmp"
  mv "$summary_tmp" "$summary"
}

task_dependencies_pass() {
  dependency_task=$1
  dependency_csv=$(awk -F '\t' -v task="$dependency_task" '$1 == task { print $3; exit }' "$matrix")
  [ "$dependency_csv" = - ] && return 0
  old_ifs=$IFS
  IFS=,
  set -- $dependency_csv
  IFS=$old_ifs
  for dependency in "$@"; do
    [ "$(field result "$state/$dependency.env" 2>/dev/null)" = PASS ] || return 1
    dependency_input=$(task_input_fingerprint "$dependency")
    receipt_reusable "$dependency" "$dependency_input" || return 1
  done
}

classify_status() {
  classify_task=$1
  classify_code=$2
  case "$classify_code" in
    0) echo PASS ;;
    124) echo TIMEOUT ;;
    137) echo CRASH ;;
    134|136|139) echo CRASH ;;
    *) echo FAIL ;;
  esac
}

record_command() {
  command_task=$1
  shift
  command_file="$logs/$command_task.command"
  {
    echo "cwd=$source_root"
    echo "HOME=$homes/$command_task"
    echo "TMPDIR=$tmps/$command_task"
    echo 'SIMPLE_NO_STUB_FALLBACK=1'
    echo 'argv-begin'
    for command_arg in "$@"; do printf '%s\n' "$command_arg"; done
    echo 'argv-end'
  } >>"$command_file"
}

run_logged() {
  run_task=$1
  shift
  run_log="$logs/$run_task.log"
  mkdir -p "$homes/$run_task" "$tmps/$run_task"
  : >"$logs/$run_task.command"
  record_command "$run_task" "$@"
  rm -f "$state/$run_task.watchdog-timeout"
  printf '%s\n' "$(date +%s)" >"$state/$run_task.started"
  run_status=0
  if command -v timeout >/dev/null 2>&1; then
    (cd "$source_root" && env HOME="$homes/$run_task" TMPDIR="$tmps/$run_task" \
      SIMPLE_NO_STUB_FALLBACK=1 timeout -k 15s "${timeout_seconds}s" "$@") \
      >"$run_log" 2>&1 || run_status=$?
  else
    (cd "$source_root" && env HOME="$homes/$run_task" TMPDIR="$tmps/$run_task" \
      SIMPLE_NO_STUB_FALLBACK=1 "$@") >"$run_log" 2>&1 || run_status=$?
  fi
  printf '%s\n' "$(date +%s)" >"$state/$run_task.ended"
  run_elapsed=$(( $(cat "$state/$run_task.ended") - $(cat "$state/$run_task.started") ))
  if [ "$run_status" -eq 124 ]; then
    printf 'watchdog=true\nelapsed_seconds=%s\n' "$run_elapsed" >"$state/$run_task.watchdog-timeout"
  fi
  return "$run_status"
}

run_logged_append() {
  append_task=$1
  shift
  append_log="$logs/$append_task.log"
  mkdir -p "$homes/$append_task" "$tmps/$append_task"
  append_status=0
  record_command "$append_task" "$@"
  rm -f "$state/$append_task.watchdog-timeout"
  printf '%s\n' "$(date +%s)" >"$state/$append_task.started"
  if command -v timeout >/dev/null 2>&1; then
    (cd "$source_root" && env HOME="$homes/$append_task" TMPDIR="$tmps/$append_task" \
      SIMPLE_NO_STUB_FALLBACK=1 timeout -k 15s "${timeout_seconds}s" "$@") \
      >>"$append_log" 2>&1 || append_status=$?
  else
    (cd "$source_root" && env HOME="$homes/$append_task" TMPDIR="$tmps/$append_task" \
      SIMPLE_NO_STUB_FALLBACK=1 "$@") >>"$append_log" 2>&1 || append_status=$?
  fi
  printf '%s\n' "$(date +%s)" >"$state/$append_task.ended"
  append_elapsed=$(( $(cat "$state/$append_task.ended") - $(cat "$state/$append_task.started") ))
  [ "$append_status" -ne 124 ] || printf 'watchdog=true\nelapsed_seconds=%s\n' "$append_elapsed" >"$state/$append_task.watchdog-timeout"
  return "$append_status"
}

run_expected_status() {
  expected_task=$1
  expected_status=$2
  shift 2
  actual_status=0
  run_logged "$expected_task" "$@" || actual_status=$?
  [ "$actual_status" -eq "$expected_status" ] || return 1
  return 0
}

run_expected_status_append() {
  expected_task=$1
  expected_status=$2
  shift 2
  actual_status=0
  run_logged_append "$expected_task" "$@" || actual_status=$?
  [ "$actual_status" -eq "$expected_status" ] || return 1
  return 0
}

run_logged_with_input() {
  input_task=$1
  input_file=$2
  shift 2
  input_log="$logs/$input_task.log"
  mkdir -p "$homes/$input_task" "$tmps/$input_task"
  : >"$logs/$input_task.command"
  record_command "$input_task" "$@" "stdin=$input_file"
  input_status=0
  rm -f "$state/$input_task.watchdog-timeout"
  printf '%s\n' "$(date +%s)" >"$state/$input_task.started"
  if command -v timeout >/dev/null 2>&1; then
    (cd "$source_root" && env HOME="$homes/$input_task" TMPDIR="$tmps/$input_task" \
      SIMPLE_NO_STUB_FALLBACK=1 timeout -k 15s "${timeout_seconds}s" "$@" <"$input_file") \
      >"$input_log" 2>&1 || input_status=$?
  else
    (cd "$source_root" && env HOME="$homes/$input_task" TMPDIR="$tmps/$input_task" \
      SIMPLE_NO_STUB_FALLBACK=1 "$@" <"$input_file") >"$input_log" 2>&1 || input_status=$?
  fi
  printf '%s\n' "$(date +%s)" >"$state/$input_task.ended"
  input_elapsed=$(( $(cat "$state/$input_task.ended") - $(cat "$state/$input_task.started") ))
  [ "$input_status" -ne 124 ] || printf 'watchdog=true\nelapsed_seconds=%s\n' "$input_elapsed" >"$state/$input_task.watchdog-timeout"
  return "$input_status"
}

validate_help_log() {
  help_task=$1
  help_log=$2
  [ -s "$help_log" ] || return 1
  case "$help_task" in
    cli_help) grep -Fq 'Usage: simple' "$help_log" ;;
    mcp_help) grep -Fq 'Simple MCP Server' "$help_log" && grep -Fq 'Usage: simple mcp' "$help_log" ;;
    lsp_help) grep -Fq 'Usage: simple_lsp_mcp_server' "$help_log" && grep -Fq -- '--log-mode' "$help_log" && grep -Fq -- '--progress' "$help_log" ;;
  esac
}

validate_version_log() {
  version_task=$1
  version_log=$2
  [ -s "$version_log" ] || return 1
  case "$version_task" in
    cli_version) grep -Eiq '^simple([- ]|$)' "$version_log" && ! grep -Eq 'Rust-built|bootstrap seed only' "$version_log" ;;
    mcp_version) grep -Fxq 'Simple MCP Server v4.0.0' "$version_log" ;;
    lsp_version) grep -Fxq 'simple-lsp-mcp 0.9.8' "$version_log" ;;
  esac
}

run_check_task() {
  check_task=$1
  check_target=$2
  check_cli=$(tool_output cli)
  run_logged "$check_task" env SIMPLE_LIB="$source_root/src" "$check_cli" check "$check_target" || return $?
  checked_count=$(grep -Ec '^Checking .*\.spl|^Checking ' "$logs/$check_task.log" || :)
  [ "$checked_count" -gt 0 ] || return 1
  printf 'checked_sources=%s\n' "$checked_count" >>"$logs/$check_task.log"
  printf 'checked_sources=%s\n' "$checked_count" >"$state/$check_task.pass-marker"
}

run_test_task() {
  test_task=$1
  expected_total=$2
  shift 2
  test_cli=$(tool_output cli)
  run_logged "$test_task" env SIMPLE_LIB="$source_root/src" "$test_cli" test "$@" \
    --mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran --fail-fast || return $?
  validate_test_task_log "$test_task" "$expected_total" "$@"
}

validate_test_task_log() {
  test_task=$1
  expected_total=$2
  shift 2
  summary_fields=$(sed -n 's/.*Results: \([0-9][0-9]*\) total, \([0-9][0-9]*\) passed, \([0-9][0-9]*\) failed.*/\1 \2 \3/p' "$logs/$test_task.log" | tail -n 1)
  [ "$(printf '%s\n' "$summary_fields" | awk '{print NF}')" -eq 3 ] || return 1
  executed_count=$(printf '%s\n' "$summary_fields" | awk '{print $1}')
  passed_count=$(printf '%s\n' "$summary_fields" | awk '{print $2}')
  failed_count=$(printf '%s\n' "$summary_fields" | awk '{print $3}')
  case "$executed_count:$passed_count:$failed_count" in *[!0-9:]*|0:*) return 1 ;; esac
  [ "$failed_count" -eq 0 ] && [ "$passed_count" -eq "$executed_count" ] || return 1
  if [ "$expected_total" != - ]; then [ "$executed_count" -eq "$expected_total" ] || return 1; fi
  verdict_total=0
  for expected_target in "$@"; do
    verdict_line=$(grep -F "SPEC FILE VERDICT: $expected_target " "$logs/$test_task.log" | tail -n 1)
    [ -n "$verdict_line" ] || return 1
    verdict_executed=$(printf '%s\n' "$verdict_line" | sed -n 's/.* executed=\([0-9][0-9]*\).*/\1/p')
    case "$verdict_executed" in ''|*[!0-9]*|0) return 1 ;; esac
    printf '%s\n' "$verdict_line" | grep -Eq ' passed=[0-9]+ failed=0 dropped=0' || return 1
    verdict_total=$((verdict_total + verdict_executed))
  done
  [ "$verdict_total" -eq "$executed_count" ] || return 1
  printf '%s\n' "$executed_count" >"$state/$test_task.executed-tests"
  printf 'results_total=%s_passed=%s_failed=0_targets=%s\n' "$executed_count" "$passed_count" "$#" >"$state/$test_task.pass-marker"
}

make_test_manifest() {
  manifest_task=$1
  manifest_root=$2
  shift 2
  manifest_dir="$work_root/manifests"
  manifest_path="$manifest_dir/$manifest_task.txt"
  manifest_tmp="$manifest_path.tmp.$$"
  mkdir -p "$manifest_dir"
  find "$manifest_root" -type f -name '*_spec.spl' -print | LC_ALL=C sort | while IFS= read -r manifest_file; do
    manifest_include=true
    for manifest_exclude in "$@"; do
      case "$manifest_file" in "$manifest_exclude"|"$manifest_exclude"/*) manifest_include=false ;; esac
    done
    [ "$manifest_include" != true ] || printf '%s\n' "$manifest_file"
  done >"$manifest_tmp"
  [ -s "$manifest_tmp" ] || return 1
  mv "$manifest_tmp" "$manifest_path"
  printf '%s\n' "$manifest_path"
}

run_manifest_test_task() {
  manifest_test_task=$1
  manifest_expected_total=$2
  manifest_file=$3
  set --
  while IFS= read -r manifest_test_file; do
    case "$manifest_test_file" in *' '*) return 1 ;; esac
    set -- "$@" "$manifest_test_file"
  done <"$manifest_file"
  [ "$#" -gt 0 ] || return 1
  run_test_task "$manifest_test_task" "$manifest_expected_total" "$@"
}

quarantine_publish() {
  quarantine_tool=$1
  quarantine_path="$(tool_publish_rel "$quarantine_tool")"
  [ -e "$quarantine_path" ] || return 0
  mkdir -p "$work_root/quarantine"
  quarantine_index=1
  while [ -e "$work_root/quarantine/${quarantine_tool}.$quarantine_index" ]; do
    quarantine_index=$((quarantine_index + 1))
  done
  mv "$quarantine_path" "$work_root/quarantine/${quarantine_tool}.$quarantine_index"
}

run_link_task() {
  link_tool=$1
  link_task="link_$link_tool"
  link_input=$(task_input_fingerprint "$link_task")
  if receipt_reusable "$link_task" "$link_input"; then return 0; fi
  rm -f "$logs/$link_task.command" "$state/$link_task.pass-marker" "$state/$link_task.executed-tests"
  printf '%s\n' "$link_input" >"$state/$link_task.input-before"
  write_identity_snapshot "$link_task" before
  if ! frozen_identity_stable; then
    link_log="$logs/$link_task.log"
    printf 'frozen identity drift before link\n' >"$link_log"
    write_identity_snapshot "$link_task" after
    write_task_input_snapshot "$link_task" after
    write_task_receipt "$link_task" BLOCKED_UPSTREAM identity-drift-before "$link_input" "$link_log" - -
    write_summary
    return 0
  fi
  link_journal=$(tool_journal "$link_tool")
  link_log="$logs/$link_task.log"
  if [ ! -f "$link_journal" ]; then
    printf 'missing required journal: %s\n' "$link_journal" >"$link_log"
    write_identity_snapshot "$link_task" after
    write_task_input_snapshot "$link_task" after
    write_task_receipt "$link_task" BLOCKED_UPSTREAM missing-journal "$link_input" "$link_log" - -
    write_summary
    return 0
  fi
  quarantine_publish "$link_tool"
  link_status=0
  run_logged "$link_task" "$link_wrapper" stage4-tools-only \
    "--compiler-manifest=$compiler_manifest" \
    "--tool-compile-journal=$link_journal" \
    "--tool-id=$link_tool" "--entry=$(tool_entry "$link_tool")" \
    "--cache-dir=$(tool_cache_rel "$link_tool")" \
    "--publish-dir=$(tool_publish_rel "$link_tool")" \
    "--linker=$linker_path" || link_status=$?
  link_result=$(classify_status "$link_task" "$link_status")
  link_output=$(tool_output "$link_tool")
  link_output_hash=-
  if [ "$link_result" = PASS ] && tool_receipt_valid "$link_tool"; then
    link_output_hash=$(hash_file "$link_output")
  elif [ "$link_result" = PASS ]; then
    link_result=FAIL
    link_status=invalid-link-receipt
  fi
  write_identity_snapshot "$link_task" after
  write_task_input_snapshot "$link_task" after
  if ! task_input_unchanged "$link_task"; then
    link_result=FAIL
    link_status=input-drift-after
  fi
  if ! frozen_identity_stable; then
    link_result=FAIL
    link_status=identity-drift-after
  fi
  if [ "$link_result" = PASS ]; then
    printf 'task=%s_validated_link=true\n' "$link_task" >"$state/$link_task.pass-marker"
  fi
  write_task_receipt "$link_task" "$link_result" "$link_status" "$link_input" "$link_log" "$link_output" "$link_output_hash"
  write_summary
}

run_gate_command() {
  gate_task=$1
  gate_input=$(task_input_fingerprint "$gate_task")
  if receipt_reusable "$gate_task" "$gate_input"; then return 0; fi
  printf '%s\n' "$gate_input" >"$state/$gate_task.input-before"
  gate_log="$logs/$gate_task.log"
  rm -f "$logs/$gate_task.command" "$state/$gate_task.executed-tests" "$state/$gate_task.pass-marker"
  write_identity_snapshot "$gate_task" before
  if ! frozen_identity_stable; then
    printf 'frozen identity drift before task\n' >"$gate_log"
    write_identity_snapshot "$gate_task" after
    write_task_input_snapshot "$gate_task" after
    write_task_receipt "$gate_task" BLOCKED_UPSTREAM identity-drift-before "$gate_input" "$gate_log" - -
    write_summary
    return 0
  fi
  if ! task_dependencies_pass "$gate_task"; then
    printf 'required predecessor did not PASS\n' >"$gate_log"
    write_identity_snapshot "$gate_task" after
    write_task_input_snapshot "$gate_task" after
    write_task_receipt "$gate_task" BLOCKED_UPSTREAM required-predecessor "$gate_input" "$gate_log" - -
    write_summary
    return 0
  fi
  case "$gate_task" in
    mcp_stdio_integration|lsp_stdio_integration)
      printf 'required row retained fail-closed: protocol-root artifact/hash contract awaits static acceptance\n' >"$gate_log"
      write_identity_snapshot "$gate_task" after
      write_task_input_snapshot "$gate_task" after
      write_task_receipt "$gate_task" BLOCKED_UPSTREAM protocol-root-contract-not-accepted "$gate_input" "$gate_log" - -
      write_summary
      return 0
      ;;
  esac
  cli_output=$(tool_output cli)
  gate_status=0
  case "$gate_task" in
    cli_help)
      run_logged "$gate_task" "$cli_output" --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_help_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    cli_version)
      run_logged "$gate_task" "$cli_output" --version || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_version_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    mcp_help)
      run_logged "$gate_task" "$(tool_output mcp)" --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_help_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    mcp_version)
      run_logged "$gate_task" "$(tool_output mcp)" --version || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_version_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    lsp_help)
      run_logged "$gate_task" "$(tool_output lsp)" --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_help_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    lsp_version)
      run_logged "$gate_task" "$(tool_output lsp)" --version || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_version_log "$gate_task" "$gate_log" || gate_status=1
      ;;
    core_runtime_smoke)
      run_logged "$gate_task" sh "$source_root/scripts/check/check-core-runtime-smoke.shs" "$cli_output" || gate_status=$?
      ;;
    redeploy_sanity)
      run_logged "$gate_task" sh "$source_root/scripts/check/cert/redeploy_gate/redeploy_gate.shs" "$cli_output" || gate_status=$?
      ;;
    essential_tools)
      run_logged "$gate_task" env SIMPLE_BINARY="$cli_output" sh "$source_root/scripts/check/check-bootstrap-essential-tools-smoke.shs" "$cli_output" || gate_status=$?
      ;;
    lint_help)
      run_logged "$gate_task" "$cli_output" lint --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Usage: simple lint' "$gate_log" || gate_status=1
      ;;
    lint_focused)
      run_logged "$gate_task" "$cli_output" lint "$source_root/src/app/cli/lint_entry.spl" || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Lint passed: all files clean' "$gate_log" || gate_status=1
      ;;
    duplicate_help)
      run_logged "$gate_task" "$cli_output" duplicate-check --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Usage: simple duplicate-check' "$gate_log" || gate_status=1
      ;;
    duplicate_focused)
      duplicate_json="$work_root/outputs/duplicate-focused.json"
      mkdir -p "$(dirname "$duplicate_json")"
      run_expected_status "$gate_task" 1 "$cli_output" duplicate-check \
        "$source_root/test/fixtures/duplication/dup_pair" --no-default-excludes \
        --mode token --min-lines 5 --min-tokens 8 --format json || gate_status=$?
      if [ "$gate_status" -eq 0 ]; then
        cp "$gate_log" "$duplicate_json" || gate_status=1
      fi
      if [ "$gate_status" -eq 0 ]; then
        run_logged_append "$gate_task" env SIMPLE_LIB="$source_root/src" "$cli_output" run \
          "$source_root/scripts/check/validate-json.spl" "$duplicate_json" || gate_status=$?
      fi
      ;;
    compiler_check)
      run_check_task "$gate_task" "$source_root/src/compiler" || gate_status=$?
      ;;
    library_check)
      run_check_task "$gate_task" "$source_root/src/lib" || gate_status=$?
      ;;
    mcp_check)
      run_check_task "$gate_task" "$source_root/src/app/mcp" || gate_status=$?
      ;;
    lsp_check)
      run_check_task "$gate_task" "$source_root/src/app/simple_lsp_mcp" || gate_status=$?
      ;;
    compiler_bootstrap_tests)
      bootstrap_manifest=$(make_test_manifest "$gate_task" "$source_root/test/01_unit/compiler/bootstrap" \
        "$source_root/test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl") || gate_status=1
      [ "$gate_status" -ne 0 ] || run_manifest_test_task "$gate_task" - "$bootstrap_manifest" || gate_status=$?
      ;;
    compiler_core_tests)
      core_manifest=$(make_test_manifest "$gate_task" "$source_root/test/01_unit/compiler_core") || gate_status=1
      [ "$gate_status" -ne 0 ] || run_manifest_test_task "$gate_task" - "$core_manifest" || gate_status=$?
      ;;
    compiler_full_tests)
      full_manifest=$(make_test_manifest "$gate_task" "$source_root/test/01_unit/compiler" \
        "$source_root/test/01_unit/compiler/bootstrap") || gate_status=1
      [ "$gate_status" -ne 0 ] || run_manifest_test_task "$gate_task" - "$full_manifest" || gate_status=$?
      ;;
    format_fixed_focused_regression)
      focused_spec="$source_root/test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl"
      run_test_task "$gate_task" 5 "$focused_spec" || gate_status=$?
      ;;
    mcp_protocol|mcp_focused|lsp_protocol)
      protocol_input="$work_root/inputs/$gate_task.jsonl"
      mkdir -p "$(dirname "$protocol_input")"
      printf '%s\n' \
        '{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"p4dbg","version":"1"}}}' \
        '{"jsonrpc":"2.0","method":"notifications/initialized","params":{}}' \
        '{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}' >"$protocol_input"
      if [ "$gate_task" = mcp_focused ]; then
        printf '%s\n' \
          '{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"simple_pipe","arguments":{"surface":"spipe"}}}' \
          '{"jsonrpc":"2.0","id":"4","method":"tools/call","params":{"name":"simple_search","arguments":{"query":"__PURE_SIMPLE_MCP_SANITY_NO_MATCH__","scope":"src"}}}' >>"$protocol_input"
      fi
      protocol_binary=$(tool_output mcp)
      [ "$gate_task" != lsp_protocol ] || protocol_binary=$(tool_output lsp)
      run_logged_with_input "$gate_task" "$protocol_input" env SIMPLE_LIB="$source_root/src" \
        SIMPLE_MCP_ALLOW_SOURCE_FALLBACK=0 SIMPLE_MCP_TOOL_SET=all "$protocol_binary" || gate_status=$?
      ;;
    tooling_contract_tests)
      run_test_task "$gate_task" - \
        "$source_root/test/01_unit/lib/tooling/bootstrap_stage_split_spec.spl" \
        "$source_root/test/02_integration/app/cli/stage4_tools_only_manifest_spec.spl" || gate_status=$?
      ;;
    mcp_unit_tests)
      mcp_manifest=$(make_test_manifest "$gate_task" "$source_root/test/01_unit/app/mcp_unit") || gate_status=1
      [ "$gate_status" -ne 0 ] || run_manifest_test_task "$gate_task" - "$mcp_manifest" || gate_status=$?
      ;;
    lsp_unit_tests)
      lsp_manifest=$(make_test_manifest "$gate_task" "$source_root/test/01_unit/app/lsp") || gate_status=1
      [ "$gate_status" -ne 0 ] || run_manifest_test_task "$gate_task" - "$lsp_manifest" || gate_status=$?
      ;;
    lsp_log_modes_tests)
      log_modes_spec="$source_root/test/02_integration/app/simple_lsp_mcp_log_modes_spec.spl"
      run_logged "$gate_task" env SIMPLE_LIB="$source_root/src" SIMPLE_LSP_MCP_TEST_BINARY="$(tool_output lsp)" \
        "$cli_output" test "$log_modes_spec" --mode=interpreter --no-session-daemon --sequential \
        --no-db --no-cache --assert-ran --fail-fast || gate_status=$?
      [ "$gate_status" -ne 0 ] || validate_test_task_log "$gate_task" 5 "$log_modes_spec" || gate_status=1
      ;;
    test_daemon)
      run_expected_status "$gate_task" 1 "$cli_output" test-daemon || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'simple test-daemon start' "$gate_log" || gate_status=1
      ;;
    examples_check)
      example_dir="$work_root/fixtures/examples"
      mkdir -p "$example_dir"
      cp "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl" "$example_dir/pass.spl" || gate_status=1
      if [ "$gate_status" -eq 0 ]; then
        run_logged "$gate_task" "$cli_output" examples-check "$example_dir" --limit 1 --fail-fast --json || gate_status=$?
      fi
      [ "$gate_status" -ne 0 ] || grep -Eq '"total":1.*"passed":1.*"failed":0' "$gate_log" || gate_status=1
      ;;
    fmt)
      fmt_dir="$work_root/fixtures/fmt"
      mkdir -p "$fmt_dir"
      cp "$source_root/test/fixtures/fmt/unformatted.spl" "$fmt_dir/input.spl" || gate_status=1
      if [ "$gate_status" -eq 0 ]; then run_logged "$gate_task" "$cli_output" fmt "$fmt_dir/input.spl" --write || gate_status=$?; fi
      if [ "$gate_status" -eq 0 ]; then run_logged_append "$gate_task" "$cli_output" fmt "$fmt_dir/input.spl" --check || gate_status=$?; fi
      ;;
    fix)
      fix_dir="$work_root/fixtures/fix"
      mkdir -p "$fix_dir"
      cp "$source_root/test/fixtures/pure_simple_tooling/clean.spl" "$fix_dir/input.spl" || gate_status=1
      fix_before=$(file_hash_or_missing "$fix_dir/input.spl")
      if [ "$gate_status" -eq 0 ]; then run_logged "$gate_task" "$cli_output" fix "$fix_dir/input.spl" --dry-run || gate_status=$?; fi
      fix_after=$(file_hash_or_missing "$fix_dir/input.spl")
      [ "$gate_status" -ne 0 ] || [ "$fix_before" = "$fix_after" ] || gate_status=1
      ;;
    verify)
      run_logged "$gate_task" "$cli_output" verify --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Usage: simple verify' "$gate_log" || gate_status=1
      ;;
    spipe_docgen)
      docgen_out="$work_root/outputs/spipe-docgen"
      mkdir -p "$docgen_out"
      run_logged "$gate_task" "$cli_output" spipe-docgen \
        "$source_root/test/fixtures/pure_simple_tooling/sibling_describe_green_spec.spl" \
        --output "$docgen_out" || gate_status=$?
      [ "$gate_status" -ne 0 ] || [ -n "$(find "$docgen_out" -type f -size +0c -print -quit 2>/dev/null)" ] || gate_status=1
      ;;
    native_build)
      native_cache="$work_rel/cache/native-build"
      native_out="$work_root/outputs/native-build/p2_add"
      mkdir -p "$(dirname "$native_out")"
      run_logged "$gate_task" "$cli_output" native-build --backend=cranelift \
        --source "$source_root/src/compiler" --source "$source_root/src/app" --source "$source_root/src/lib" \
        --entry-closure --threads 1 --cache-dir "$native_cache" \
        --entry "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl" --output "$native_out" || gate_status=$?
      [ "$gate_status" -ne 0 ] || [ -x "$native_out" ] || gate_status=1
      if [ "$gate_status" -eq 0 ]; then run_logged_append "$gate_task" "$native_out" || gate_status=$?; fi
      [ "$gate_status" -ne 0 ] || grep -Fxq '5' "$gate_log" || gate_status=1
      ;;
    security)
      run_logged "$gate_task" "$cli_output" security check "$source_root/test/fixtures/pure_simple_tooling/clean.spl" || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'security: no findings' "$gate_log" || gate_status=1
      ;;
    build)
      run_expected_status "$gate_task" 2 "$cli_output" build --explain || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'build-explain-error: --target <name> required' "$gate_log" || gate_status=1
      ;;
    run)
      run_logged "$gate_task" "$cli_output" run "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl" || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fxq '5' "$gate_log" || gate_status=1
      ;;
    doc_coverage)
      run_logged "$gate_task" "$cli_output" doc-coverage "$source_root/test/fixtures/doc_coverage" --missing || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'orphan_fn' "$gate_log" || gate_status=1
      [ "$gate_status" -ne 0 ] || ! grep -Fq 'documented_thing' "$gate_log" || gate_status=1
      ;;
    vscode_dispatch)
      run_logged "$gate_task" "$cli_output" vscode --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Usage: simple vscode' "$gate_log" || gate_status=1
      ;;
    electron_dispatch)
      run_logged "$gate_task" "$cli_output" electron --help || gate_status=$?
      [ "$gate_status" -ne 0 ] || grep -Fq 'Usage: simple electron' "$gate_log" || gate_status=1
      ;;
    vscode_external)
      if ! command -v npm >/dev/null 2>&1 || [ ! -f "$source_root/src/app/vscode_extension/package.json" ]; then
        printf 'optional prerequisite unavailable: npm and vscode package.json required\n' >"$gate_log"
        write_identity_snapshot "$gate_task" after
        write_task_input_snapshot "$gate_task" after
        write_task_receipt "$gate_task" UNSUPPORTED external-prerequisite-unavailable "$gate_input" "$gate_log" - -
        write_summary
        return 0
      fi
      run_logged "$gate_task" "$cli_output" vscode build "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl" || gate_status=$?
      ;;
    electron_external)
      if ! command -v npm >/dev/null 2>&1 || [ ! -f "$source_root/tools/electron-shell/package.json" ]; then
        printf 'optional prerequisite unavailable: npm and electron package.json required\n' >"$gate_log"
        write_identity_snapshot "$gate_task" after
        write_task_input_snapshot "$gate_task" after
        write_task_receipt "$gate_task" UNSUPPORTED external-prerequisite-unavailable "$gate_input" "$gate_log" - -
        write_summary
        return 0
      fi
      run_logged "$gate_task" "$cli_output" electron build "$source_root/scripts/check/cert/redeploy_gate/fixtures/p2_add.spl" || gate_status=$?
      ;;
    simple_core_smoke)
      help_output=$("$cli_output" native-build --help 2>/dev/null || :)
      if ! printf '%s\n' "$help_output" | grep -Fq -- --emit-archive; then
        printf 'selected Stage4 CLI does not advertise --emit-archive\n' >"$gate_log"
        write_identity_snapshot "$gate_task" after
        write_task_input_snapshot "$gate_task" after
        write_task_receipt "$gate_task" UNSUPPORTED emit-archive-unavailable "$gate_input" "$gate_log" - -
        write_summary
        return 0
      fi
      run_logged "$gate_task" env SIMPLE_BINARY="$cli_output" \
        BUILD_DIR="$work_root/simple-core-smoke" SIMPLE_CORE_BUILD_DIR="$work_root/simple-core" \
        sh "$source_root/scripts/check/check-simple-core-runtime-smoke.shs" || gate_status=$?
      ;;
  esac
  if [ "$gate_status" -eq 0 ]; then
    case "$gate_task" in
      core_runtime_smoke)
        grep -Fqx 'core_runtime_smoke=true' "$gate_log" || gate_status=1
        ;;
      essential_tools)
        for essential_marker in \
          essential_list_constructor_smoke=true \
          essential_test_runner_smoke=true \
          essential_lint_smoke=true \
          essential_duplicate_checker_smoke=true \
          bootstrap_essential_tools_smoke=true; do
          grep -Fqx "$essential_marker" "$gate_log" || gate_status=1
        done
        if [ "$gate_status" -eq 0 ]; then
          printf 'validated_output_markers=5\n' >"$state/$gate_task.pass-marker"
        fi
        ;;
      mcp_protocol)
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"1"' "$gate_log" || gate_status=1
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"2"' "$gate_log" || gate_status=1
        grep -Fq 'protocolVersion' "$gate_log" || gate_status=1
        grep -Fq 'inputSchema' "$gate_log" || gate_status=1
        grep -Fq 'debug_create_session' "$gate_log" || gate_status=1
        ! grep -Fq '"error"' "$gate_log" || gate_status=1
        ;;
      mcp_focused)
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"3"' "$gate_log" || gate_status=1
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"4"' "$gate_log" || gate_status=1
        grep -Fq 'spipe: linked' "$gate_log" || gate_status=1
        grep -Fq 'No results found.' "$gate_log" || gate_status=1
        ! grep -Eq 'native_missing|source fallback|stub fallback' "$gate_log" || gate_status=1
        ;;
      lsp_protocol)
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"1"' "$gate_log" || gate_status=1
        grep -Eq '"id"[[:space:]]*:[[:space:]]*"2"' "$gate_log" || gate_status=1
        grep -Fq 'protocolVersion' "$gate_log" || gate_status=1
        grep -Fq 'inputSchema' "$gate_log" || gate_status=1
        ! grep -Fq '"error"' "$gate_log" || gate_status=1
        ;;
    esac
  fi
  write_identity_snapshot "$gate_task" after
  write_task_input_snapshot "$gate_task" after
  if ! task_input_unchanged "$gate_task"; then
    gate_status=1
    printf 'task input drift after command\n' >>"$gate_log"
  fi
  if ! frozen_identity_stable; then
    gate_status=1
    printf 'frozen identity drift after task\n' >>"$gate_log"
  fi
  gate_result=$(classify_status "$gate_task" "$gate_status")
  gate_output=-
  gate_output_hash=-
  if [ "$gate_result" = PASS ]; then
    if [ ! -f "$state/$gate_task.pass-marker" ]; then
      printf 'task=%s_validated_pass=true\n' "$gate_task" >"$state/$gate_task.pass-marker"
    fi
    case "$gate_task" in
      duplicate_focused)
        gate_output="$work_root/outputs/duplicate-focused.json"
        ;;
      fmt)
        gate_output="$work_root/fixtures/fmt/input.spl"
        ;;
      fix)
        gate_output="$work_root/fixtures/fix/input.spl"
        ;;
      spipe_docgen)
        gate_output=$(find "$work_root/outputs/spipe-docgen" -type f -size +0c -print -quit 2>/dev/null || :)
        ;;
      native_build)
        gate_output="$work_root/outputs/native-build/p2_add"
        ;;
    esac
    if [ "$gate_output" != - ] && [ -f "$gate_output" ]; then gate_output_hash=$(hash_file "$gate_output"); fi
  fi
  write_task_receipt "$gate_task" "$gate_result" "$gate_status" "$gate_input" "$gate_log" "$gate_output" "$gate_output_hash"
  write_summary
}

write_summary
run_link_task cli
run_link_task mcp
run_link_task lsp

if [ "$scope" = full ]; then
  while IFS="$(printf '\t')" read -r task required deps; do
    case "$task" in link_*) continue ;; esac
    run_gate_command "$task"
  done <"$matrix"
fi

write_summary
overall=$(field overall "$summary")
case "$overall" in PASS|SCOPED_PASS) exit 0 ;; *) exit 1 ;; esac
}

# --- folded: stage4-tools-only.sh -----------------------------------------
bootstrap_folded_stage4_tools_only() {
# Validate one approved Stage-4 tool journal and atomically publish its output.
set -eu

die() {
  echo "stage4-tools-only: $*" >&2
  exit 1
}

manifest=
journal=
cache=
publish=
tool_id=
entry_path=
linker=cc

for arg in "$@"; do
  case "$arg" in
    --compiler-manifest=*) manifest=${arg#*=} ;;
    --tool-compile-journal=*) journal=${arg#*=} ;;
    --cache-dir=*) cache=${arg#*=} ;;
    --publish-dir=*) publish=${arg#*=} ;;
    --tool-id=*) tool_id=${arg#*=} ;;
    --entry=*) entry_path=${arg#*=} ;;
    --linker=*) linker=${arg#*=} ;;
    *) die "unknown option: $arg" ;;
  esac
done

[ -f "$manifest" ] || die "compiler manifest is required"
[ -f "$journal" ] || die "tool compile journal is required"
case "$cache" in
  build/mini_cache_stage4_*) ;;
  *) die "cache must be a contained Stage-4 mini cache" ;;
esac
case "${cache#build/mini_cache_stage4_}" in
  ''|*/*|*..*) die "invalid cache identity" ;;
esac
case "$publish" in
  build/stage4-tools/*) ;;
  *) die "publish directory must be contained" ;;
esac
case "${publish#build/stage4-tools/}" in
  ''|*/*|*..*) die "invalid publish identity" ;;
esac

case "$tool_id:$entry_path" in
  cli:src/app/cli/main.spl) output_name=simple ;;
  mcp:src/app/mcp/main.spl) output_name=simple_mcp_server ;;
  lsp:src/app/simple_lsp_mcp/main.spl) output_name=simple_lsp_mcp_server ;;
  *) die "unapproved tool identity: $tool_id:$entry_path" ;;
esac

[ ! -e "$publish" ] || die "publish directory already exists"

value() {
  value_file=$1
  value_key=$2
  value_count=$(awk -F= -v key="$value_key" '$1 == key { count++ } END { print count + 0 }' "$value_file")
  [ "$value_count" -eq 1 ] || die "$value_key must occur once"
  sed -n "s/^${value_key}=//p" "$value_file"
}

valid_hash() {
  printf '%s\n' "$1" | grep -Eq '^[0-9a-f]{64}$'
}

hash_file() {
  sha256sum "$1" | awk '{print $1}'
}

verify_file() {
  verify_path=$1
  verify_hash=$2
  verify_label=$3
  [ -f "$verify_path" ] || die "$verify_label missing"
  valid_hash "$verify_hash" || die "$verify_label hash invalid"
  [ "$(hash_file "$verify_path")" = "$verify_hash" ] || die "$verify_label hash mismatch"
}

schema=$(value "$manifest" schema_version)
[ "$schema" = CompilerArtifactManifestV1 ] || die "manifest schema"
source_hash=$(value "$manifest" source_hash)
producer_hash=$(value "$manifest" producer_hash)
backend=$(value "$manifest" backend)
[ -n "$backend" ] || die "Stage3 backend identity required"
target=$(value "$manifest" target)
compiler_abi=$(value "$manifest" compiler_abi)
runtime_abi=$(value "$manifest" runtime_abi)
identity=$(value "$manifest" compiler_identity)
case "$identity" in
  ''|*Rust-built*|*'bootstrap seed only'*) die "admitted pure-Simple Stage3 identity required" ;;
esac

admission=$(value "$manifest" admission_receipt_path)
admission_hash=$(value "$manifest" admission_receipt_hash)
compiler_exe=$(value "$manifest" compiler_executable_path)
compiler_exe_hash=$(value "$manifest" compiler_executable_hash)
compiler_archive=$(value "$manifest" compiler_archive_path)
compiler_archive_hash=$(value "$manifest" compiler_archive_hash)
compiler_interface=$(value "$manifest" compiler_interface_path)
compiler_interface_hash=$(value "$manifest" compiler_interface_hash)
runtime_archive=$(value "$manifest" runtime_archive_path)
runtime_archive_hash=$(value "$manifest" runtime_archive_hash)

valid_hash "$source_hash" && valid_hash "$producer_hash" || die "provenance hash invalid"
verify_file "$admission" "$admission_hash" admission
verify_file "$compiler_exe" "$compiler_exe_hash" executable
verify_file "$compiler_archive" "$compiler_archive_hash" compiler_archive
verify_file "$compiler_interface" "$compiler_interface_hash" interface
verify_file "$runtime_archive" "$runtime_archive_hash" runtime
[ "$(value "$admission" schema_version)" = Stage3AdmissionReceiptV1 ] || die "Stage3 admission schema"
[ "$(value "$admission" admission_status)" = PASS ] || die "Stage3 not admitted"
[ "$(value "$admission" compiler_identity)" = "$identity" ] || die "admission identity mismatch"
for key in backend compiler_executable_hash compiler_archive_hash compiler_interface_hash runtime_archive_hash target compiler_abi runtime_abi; do
  [ "$(value "$manifest" "$key")" = "$(value "$admission" "$key")" ] || die "admission mismatch $key"
done

mkdir -p "$cache" "$(dirname "$publish")"
canonical="$cache/manifest.canonical"
: >"$canonical"
frame() {
  frame_name=$1
  frame_value=$2
  frame_file=$3
  name_len=$(printf %s "$frame_name" | wc -c | tr -d ' ')
  value_len=$(printf %s "$frame_value" | wc -c | tr -d ' ')
  printf '%s:%s%s:%s' "$name_len" "$frame_name" "$value_len" "$frame_value" >>"$frame_file"
}
for pair in \
  "schema=$schema" "source=$source_hash" "producer=$producer_hash" \
  "backend=$backend" "target=$target" "compiler_abi=$compiler_abi" \
  "runtime_abi=$runtime_abi" "compiler_identity=$identity" \
  "admission_receipt_path=$admission" "admission_receipt_hash=$admission_hash" \
  "compiler_executable_path=$compiler_exe" "compiler_executable_hash=$compiler_exe_hash" \
  "compiler_archive_path=$compiler_archive" "compiler_archive_hash=$compiler_archive_hash" \
  "compiler_interface_path=$compiler_interface" "compiler_interface_hash=$compiler_interface_hash" \
  "runtime_archive_path=$runtime_archive" "runtime_archive_hash=$runtime_archive_hash"; do
  frame "${pair%%=*}" "${pair#*=}" "$canonical"
done
manifest_hash=$(hash_file "$canonical")

[ "$(value "$journal" schema_version)" = ToolCompileJournalV1 ] || die "journal schema"
[ "$(value "$journal" tool_id)" = "$tool_id" ] || die "journal tool mismatch"
[ "$(value "$journal" entry_path)" = "$entry_path" ] || die "journal entry mismatch"
[ "$(value "$journal" compiler_manifest_hash)" = "$manifest_hash" ] || die "journal manifest mismatch"
[ "$(value "$journal" compiler_executable_hash)" = "$compiler_exe_hash" ] || die "journal compiler mismatch"
[ "$(value "$journal" source_hash)" = "$source_hash" ] || die "journal source mismatch"
[ "$(value "$journal" producer_hash)" = "$producer_hash" ] || die "journal producer mismatch"
[ "$(value "$journal" backend)" = "$backend" ] || die "journal backend mismatch"
[ "$(value "$journal" target)" = "$target" ] || die "journal target mismatch"
[ "$(value "$journal" compiler_abi)" = "$compiler_abi" ] || die "journal compiler ABI mismatch"
[ "$(value "$journal" runtime_abi)" = "$runtime_abi" ] || die "journal runtime ABI mismatch"
[ "$(value "$journal" compiler_archive_hash)" = "$compiler_archive_hash" ] || die "journal compiler archive mismatch"
[ "$(value "$journal" compiler_interface_hash)" = "$compiler_interface_hash" ] || die "journal compiler interface mismatch"
[ "$(value "$journal" runtime_archive_hash)" = "$runtime_archive_hash" ] || die "journal runtime archive mismatch"
[ "$(value "$journal" compiler_sources_compiled)" = 0 ] || die "journal compiled compiler sources"
[ "$(value "$journal" stage4_compiler_files)" = 0 ] || die "journal Stage4 compiler files"

objects="$cache/objects"
sources="$cache/sources"
: >"$objects"
: >"$sources"
unit_count=0
entry_source_hash=
entry_object_hash=
tab=$(printf '\t')
while IFS="$tab" read -r kind source_path source_sha object_path object_sha extra; do
  [ "$kind" = unit ] || continue
  [ -z "${extra:-}" ] || die "bad unit row"
  case "$source_path" in
    /*|../*|*/../*|*//*|src/compiler|src/compiler/*|./src/compiler|./src/compiler/*)
      die "compiler traversal"
      ;;
    src/app/*|src/lib/*|./src/app/*|./src/lib/*) ;;
    *) die "unowned source" ;;
  esac
  verify_file "$source_path" "$source_sha" source
  verify_file "$object_path" "$object_sha" object
  grep -Fqx "$source_path" "$sources" && die "duplicate source"
  grep -Fqx "$object_path" "$objects" && die "duplicate object"
  printf '%s\n' "$source_path" >>"$sources"
  printf '%s\n' "$object_path" >>"$objects"
  normalized_source=${source_path#./}
  if [ "$normalized_source" = "$entry_path" ]; then
    entry_source_hash=$source_sha
    entry_object_hash=$object_sha
  fi
  unit_count=$((unit_count + 1))
done <"$journal"
[ "$unit_count" -gt 0 ] || die "empty journal"
[ -n "$entry_source_hash" ] || die "journal does not contain the approved entry source"
source_set_hash=$(hash_file "$sources")
object_set_hash=$(hash_file "$objects")

publish_parent=$(dirname "$publish")
publish_name=$(basename "$publish")
staging="$publish_parent/.${publish_name}.tmp.$$"
trap 'rm -rf "$staging"' EXIT INT TERM HUP
mkdir "$staging"
set --
while IFS= read -r object_path; do
  set -- "$@" "$object_path"
done <"$objects"
"$linker" -o "$staging/$output_name" "$@" "$compiler_archive" "$runtime_archive"
[ -s "$staging/$output_name" ] || die "empty output"

output_hash=$(hash_file "$staging/$output_name")
journal_hash=$(hash_file "$journal")
receipt="$staging/ToolingLinkReceiptV1.env"
{
  echo "schema_version=ToolingLinkReceiptV1"
  echo "tool_id=$tool_id"
  echo "entry_path=$entry_path"
  echo "compiler_manifest_hash=$manifest_hash"
  echo "compiler_manifest_file_hash=$(hash_file "$manifest")"
  echo "source_hash=$source_hash"
  echo "producer_hash=$producer_hash"
  echo "backend=$backend"
  echo "target=$target"
  echo "compiler_identity=$identity"
  echo "compiler_executable_hash=$compiler_exe_hash"
  echo "compiler_archive_hash=$compiler_archive_hash"
  echo "compiler_interface_hash=$compiler_interface_hash"
  echo "runtime_archive_hash=$runtime_archive_hash"
  echo "compiler_abi=$compiler_abi"
  echo "runtime_abi=$runtime_abi"
  echo "tool_compile_journal_hash=$journal_hash"
  echo "compiled_unit_count=$unit_count"
  echo "source_set_hash=$source_set_hash"
  echo "object_set_hash=$object_set_hash"
  echo "entry_source_hash=$entry_source_hash"
  echo "entry_object_hash=$entry_object_hash"
  echo "compiler_sources_compiled=0"
  echo "stage4_compiler_files=0"
  echo "output_path=$publish/$output_name"
  echo "output_hash=$output_hash"
  echo "help_smoke_passed=false"
  echo "version_smoke_passed=false"
} >"$receipt"
mv "$staging" "$publish"
trap - EXIT INT TERM HUP
echo "Stage4 tools-only PASS tool_id=$tool_id stage4_compiler_files=0"
}

# --- folded: resume-stage3-from-admitted.sh -----------------------------------------
bootstrap_folded_resume_stage3() {
set -eu

# Exit 2 means "ERROR — nothing was checked" and MUST always state the reason.
# A silent exit 2 here made a real Stage-2 refusal UNDIAGNOSABLE — see
# doc/08_tracking/bug/simpleos_stage2_bootstrap_sanity_exit2_without_diagnostic_2026-08-20.md
bootstrap_stage3_error() {
  printf 'ERROR — nothing was checked (%s)\n' "$1" >&2
  exit 2
}

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
source_output=${1:?usage: resume-stage3-from-admitted.sh OUTPUT_DIR}
case "$source_output" in /*|*../*|../*|*/..|..) bootstrap_stage3_error "OUTPUT_DIR must be a repo-relative path without .. components: $source_output" ;; esac
output="$root/$source_output"
[ "$(CDPATH= cd -- "$output" && pwd -P)" = "$output" ] ||
  bootstrap_stage3_error "OUTPUT_DIR is not a canonical existing directory: $output"

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
. "$root/scripts/check/lib/bootstrap-planner-admission-bound.shs"
planner_admission=${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}
[ -n "$planner_admission" ] || {
  echo "bootstrap-policy-error: planner-admission-v2-required" >&2; exit 64;
}
bootstrap_planner_v2_verify "$planner_admission" "$root" || exit 64
[ "$(bootstrap_planner_v2_field target "$planner_admission")" = \
  //bootstrap:stage3 ] || exit 64

platform=$(bootstrap_stage3_host_platform)
stage3="$output/stage3/$platform"
stage2="$output/stage2/$platform/simple"
admitted="$stage3/stage2-admitted/simple"
stage2_admission="$stage3/stage2-admitted/admission.env"
runtime="$stage3/stage2-runtime-authority"
seed="$runtime/simple"
stamp="$seed.inputs.sha256"
native_all="$runtime/libsimple_native_all.a"
backfill="$runtime/libsimple_compiler_backfill.a"
stage2_sanity="$stage3/stage2-sanity.env"
stage2_receiver="$stage3/stage2-receiver.env"
stage2_receiver_log="$stage3/stage2-receiver.log"
stage2_transcript="$stage3/stage2-command.transcript"
stage2_log="$output/logs/$platform/stage2-native-build.log"
candidate="$stage3/simple"
manifest="$stage3/provenance.env"
stage3_transcript="$stage3/stage3-command.transcript"
stage3_log="$output/logs/$platform/stage3-native-build.log"
stage3_sanity="$stage3/stage3-sanity.env"
stage2_cache="$stage3/stage2-native-cache"
stage3_cache="$stage3/stage3-native-cache"
home="$stage3/stage3-home"
tmp="$stage3/stage3-tmp"
source_before="$stage3/source-inputs-before.txt"
source_after="$stage3/source-inputs-after.txt"
git_before="$stage3/git-state-before.env"
git_after="$stage3/git-state-after.env"
tool_before="$stage3/tool-authority-before.txt"
tool_after="$stage3/tool-authority-after.txt"
runtime_origin_before="$stage3/runtime-origin-before.txt"
runtime_origin_after="$stage3/runtime-origin-after.txt"
runtime_admitted="$stage3/runtime-admitted.txt"
lock="$output.lock"
archive="$stage3/recovery-threads1"

for required in "$stage2" "$admitted" "$stage2_admission" "$seed" "$stamp" "$native_all" \
  "$stage2_sanity" "$stage2_receiver" "$stage2_receiver_log" \
  "$stage2_transcript" "$stage2_log" "$source_before" \
  "$git_before" \
  "$runtime_origin_before" "$runtime_origin_after" "$runtime_admitted" \
  "$tool_before"; do
  { [ -f "$required" ] && [ ! -L "$required" ]; } ||
    bootstrap_stage3_error "required Stage-2 input missing or is a symlink: $required"
  [ "$(bootstrap_stage3_canonical_file "$required")" = "$required" ] ||
    bootstrap_stage3_error "required Stage-2 input is not a canonical path: $required"
done
for required_dir in "$runtime" "$stage2_cache"; do
  { [ -d "$required_dir" ] && [ ! -L "$required_dir" ]; } ||
    bootstrap_stage3_error "required Stage-2 directory missing or is a symlink: $required_dir"
  [ "$(bootstrap_stage3_canonical_path "$required_dir")" = "$required_dir" ] ||
    bootstrap_stage3_error "required Stage-2 directory is not a canonical path: $required_dir"
done

stage2_sha=$(bootstrap_stage3_hash_file "$stage2")
admitted_sha=$(bootstrap_stage3_hash_file "$admitted")
[ "$stage2_sha" = "$admitted_sha" ] || exit 1
[ "$(bootstrap_stage3_manifest_value status "$stage2_sanity")" = pass ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_after "$stage2_sanity")" = "$admitted_sha" ] || exit 1
stage2_backend=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --backend) || exit 1
stage2_threads=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --threads) || exit 1
stage2_compile_stack_mib=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --compile-stack-mib 2>/dev/null || true)
stage2_progress=$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_BUILD_PROGRESS_EVENTS) || exit 1
case "$stage2_backend" in llvm|llvm-lib|cranelift) ;; *) exit 1 ;; esac
case "$stage2_threads" in ''|*[!0-9]*|0) exit 1 ;; esac
case "$stage2_compile_stack_mib" in ''|*[!0-9]*|0) stage2_compile_stack_mib='' ;; esac
if [ -n "$stage2_compile_stack_mib" ]; then
  stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$stage2_progress" "SIMPLE_BINARY=$seed" \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads" \
  --compile-stack-mib "$stage2_compile_stack_mib" \
  --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2")
else
  stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$stage2_progress" "SIMPLE_BINARY=$seed" \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads" \
  --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2")
fi
bootstrap_stage3_verify_sanity_evidence_receipt \
  "$stage2_sanity" "$stage2"
bootstrap_stage3_verify_receiver_evidence_receipt \
  "$stage2_receiver" "$stage2" "$runtime_admitted" "$stage2_receiver_log"
bootstrap_stage3_verify_stage2_admission_receipt \
  "$stage2_admission" "$admitted" "$source_before" "$runtime_admitted" \
  "$tool_before" "$stage2_args" "$stage2_sanity" "$stage2_receiver"
path=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" PATH)
cmp -s "$runtime_origin_before" "$runtime_origin_after"
cmp -s "$runtime_origin_after" "$runtime_admitted"
runtime_check="$archive/runtime-preflight.$$"
mkdir -p "$archive"
bootstrap_stage3_directory_snapshot "$runtime_check" "$runtime"
cmp -s "$runtime_admitted" "$runtime_check"
rm -f "$runtime_check"

# The Stage-2 source, Git, and tool files are immutable admission receipts.
# Compare fresh resume-time snapshots through separate temporary paths before
# acquiring the output lock or removing any prior recovery artifact; never
# overwrite the admitted records to manufacture a matching interval.
resume_source_check="$archive/source-preflight.$$"
resume_git_check="$archive/git-preflight.$$"
resume_tool_check="$archive/tool-preflight.$$"
bootstrap_stage3_source_snapshot "$resume_source_check" "$root"
bootstrap_stage3_git_state "$root" "$resume_git_check"
bootstrap_stage3_tool_authority_snapshot "$resume_tool_check" "$path" "$root"
cmp -s "$source_before" "$resume_source_check"
cmp -s "$git_before" "$resume_git_check"
cmp -s "$tool_before" "$resume_tool_check"
rm -f "$resume_source_check" "$resume_git_check" "$resume_tool_check"

if [ -f "$manifest" ] && bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate" >/dev/null 2>&1; then
  echo "error: canonical Stage 3 already converged: $manifest" >&2
  exit 1
fi
mkdir "$lock" || { echo "error: bootstrap output is locked: $lock" >&2; exit 1; }
printf '%s\n' "$$" >"$lock/pid"
trap 'rm -rf "$lock"' EXIT HUP INT TERM

# Prune native-build cache scope directories older than a TTL.
#
# Scope dirs are named
# `backend=...;cpu=...;opt=...;compiler=<sha>+src<fingerprint>n<count>` and are
# mint-once: as soon as any input in the closure changes, the source
# fingerprint changes and a NEW scope dir is minted. The old one is never
# consulted again, and nothing else ever collects it. That was harmless only
# while the wrappers wiped the entire cache dir on every run; now that these
# caches persist across runs (so an unchanged tree gets a real cache hit) the
# wipe is gone and scope dirs would otherwise accumulate without bound.
#
# Age-based rather than LRU on purpose: it needs no bookkeeping sidecar and no
# lock protocol. Several bootstrap lanes build concurrently on this host, and a
# scope dir whose mtime is older than the TTL cannot belong to a live build, so
# this can never pull artifacts out from under a running lane. Only entries
# matching the `backend=*` scope-dir shape are ever removed, so sibling files
# (build_cache.sdn, *.smf) are untouched. Override the window with
# BOOTSTRAP_NATIVE_CACHE_TTL_DAYS; 0 or a non-numeric value disables pruning.
bootstrap_native_cache_prune() {
  bnc_dir=$1
  bnc_ttl=${BOOTSTRAP_NATIVE_CACHE_TTL_DAYS:-7}
  [ -d "${bnc_dir}" ] || return 0
  case "${bnc_ttl}" in
    ''|*[!0-9]*) return 0 ;;
  esac
  [ "${bnc_ttl}" -gt 0 ] || return 0
  bnc_n=$(find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -print 2>/dev/null | wc -l)
  [ "${bnc_n}" -gt 0 ] || return 0
  find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -exec rm -rf {} + 2>/dev/null || true
  echo "  native cache: pruned ${bnc_n} scope dir(s) older than ${bnc_ttl}d in ${bnc_dir}"
}

for old in "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"; do
  if [ -e "$old" ]; then cp -p "$old" "$archive/$(basename "$old").before-resume"; fi
done
rm -f "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"
# stage3-native-cache is content-hash scoped by the pure-Simple driver itself
# (driver_native_sources_fingerprint in
# src/compiler/80.driver/driver_aot_native_output.spl), so a resumed run with
# an unchanged source tree can reuse it. Wiping it unconditionally on every
# resume defeated cross-run incrementality. Preserve by default;
# RESUME_STAGE3_FRESH_CACHE=1 forces a clean rebuild.
if [ "${RESUME_STAGE3_FRESH_CACHE:-0}" = 1 ]; then
  rm -rf "$stage3_cache"
else
  # Preserved cache still needs a reaper: scope dirs are mint-once and nothing
  # else collects them now that the unconditional wipe is gone.
  bootstrap_native_cache_prune "$stage3_cache"
  bootstrap_native_cache_prune "$stage2_cache"
fi
mkdir -p "$stage3_cache" "$home" "$tmp" "$(dirname "$stage3_log")"

# Stage-2 authority files remain the immutable pre-build bindings. Fresh
# post-build evidence is written only to the distinct `*_after` paths below.
# Per-lane private caches: stage2 and stage3 run different compiler binaries over
# the same source tree, so each cache dir is fenced to its own lane and reuse of a
# foreign lane's dir is refused. Additive: old checkouts without the guard skip it.
# doc/05_design/compiler/incremental_build/per_lane_private_caches.md
cache_scope_guard="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)/scripts/check/check-cache-scope-ownership.shs"
if [ -f "$cache_scope_guard" ]; then
  mkdir -p "$stage2_cache"
  sh "$cache_scope_guard" "$stage2_cache" stage2 || exit 1
  sh "$cache_scope_guard" "$stage3_cache" stage3 || exit 1
fi

# Recovery starts a fresh evidence interval after the immutable Stage-2 checks.
bootstrap_stage3_source_snapshot "$source_before" "$root"
bootstrap_stage3_git_state "$root" "$git_before"
bootstrap_stage3_tool_authority_snapshot "$tool_before" "$path" "$root"
script="$root/scripts/bootstrap/bootstrap-from-scratch.sh"
helper="$BOOTSTRAP_STAGE3_FACADE_PATH"
script_sha_before=$(bootstrap_stage3_hash_file "$script")
helper_sha_before=$(bootstrap_stage3_hash_file "$helper")
helper_bundle_before=$(bootstrap_stage3_helper_bundle_fingerprint)
seed_fingerprint=$(bootstrap_stage3_manifest_value inputs_fingerprint "$stamp")
progress="$output/bootstrap-build-progress.events"
memory_snapshot="$stage3/memory-snapshot-v1.$$.events"
phase_profile="$stage3/phase-profile.$$.events"
evidence_run_id="stage3-${platform}-$$"
[ ! -e "$memory_snapshot" ] && [ ! -L "$memory_snapshot" ] || exit 1
[ ! -e "$phase_profile" ] && [ ! -L "$phase_profile" ] || exit 1

# See bootstrap_stage3_diagnostic_env in
# scripts/check/lib/bootstrap-stage3/authority.shs.  Computed once, word-split
# into both the args hash and the real invocation so they cannot diverge; empty
# unless an allowlisted print-only probe var is set to exactly 1.
stage3_diagnostic_env=$(bootstrap_stage3_diagnostic_env) || exit 1
stage3_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_STAGE3_STREAMING_SURFACES=1" \
  "SIMPLE_FRONTEND_CACHE=0" \
  "MALLOC_ARENA_MAX=2" "MALLOC_TRIM_THRESHOLD_=0" \
  "SIMPLE_NATIVE_ARENA_DECLS=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$progress" \
  "SIMPLE_COMPILER_PHASE_PROFILE=1" \
  "SIMPLE_COMPILER_PHASE_PROFILE_FILE=$phase_profile" \
  "SIMPLE_MEM_SNAPSHOT_FILE=$memory_snapshot" \
  "SIMPLE_EVIDENCE_RUN_ID=$evidence_run_id" \
  "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1" \
  "SIMPLE_NATIVE_BUILD_TARGET=$platform" "SIMPLE_NATIVE_BUILD_THREADS=1" \
  "SIMPLE_NATIVE_BUILD_CACHE_DIR=$stage3_cache" "SIMPLE_RUNTIME_PATH=$runtime" \
  "SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap" "SIMPLE_BINARY=$admitted" \
  ${stage3_diagnostic_env} \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl)

set +e
bootstrap_stage3_run_transcribed "$stage3_transcript" "$root" "$stage3_log" \
  "$home" "$tmp" "$path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  SIMPLE_FRONTEND_CACHE=0 \
  MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BUILD_PROGRESS_EVENTS="$progress" \
  SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_PHASE_PROFILE_FILE="$phase_profile" \
  SIMPLE_MEM_SNAPSHOT_FILE="$memory_snapshot" \
  SIMPLE_EVIDENCE_RUN_ID="$evidence_run_id" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$stage3_cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" \
  ${stage3_diagnostic_env} -- \
  "$admitted" native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl
status=$?
set -e
if [ "$status" -ne 0 ]; then
  exit "$status"
fi
[ -x "$candidate" ] || {
  echo "error: Stage 3 compiler exited successfully without an executable candidate" >&2
  exit 1
}
! grep -qE '^(Build complete: [0-9]+ compiled|Linked: .* via clang)' "$stage3_log" || exit 1
[ "$(bootstrap_stage3_hash_file "$admitted")" = "$admitted_sha" ] || exit 1
runtime_check="$archive/runtime-after.$$"
bootstrap_stage3_directory_snapshot "$runtime_check" "$runtime"
cmp -s "$runtime_admitted" "$runtime_check"
rm -f "$runtime_check"

CANDIDATE_FRONTEND_ROOT=$root
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "$root/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"
bootstrap_stage_sanity() (
  candidate_sanity=$1 evidence=$2 sanity_home=$3 sanity_tmp=$4 sanity_path=$5
  for name in $(env | sed 's/=.*//'); do unset "$name"; done
  HOME=$sanity_home TMPDIR=$sanity_tmp PATH=$sanity_path LC_ALL=C LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="$evidence.tmp.$$" frontend_log="$evidence_tmp.frontend"
  before=$(bootstrap_stage3_hash_file "$candidate_sanity")
  version_status=0; version=$(run_timeout 10 "$candidate_sanity" --version 2>&1) || version_status=$?
  unsupported_status=0
  unsupported=$(run_timeout 10 "$candidate_sanity" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1) || unsupported_status=$?
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND="$stage2_backend" \
    CANDIDATE_FRONTEND_BOOTSTRAP=0 \
    candidate_frontend_smoke "$candidate_sanity" >"$frontend_log" 2>&1 || frontend_status=$?
  frontend_bootstrap_status=0
  if [ "$frontend_status" -eq 0 ]; then
    CANDIDATE_FRONTEND_BACKEND="$stage2_backend" \
      CANDIDATE_FRONTEND_BOOTSTRAP=1 \
      candidate_frontend_smoke "$candidate_sanity" >>"$frontend_log" 2>&1 || \
      frontend_bootstrap_status=$?
    frontend_status=$frontend_bootstrap_status
  fi
  after=$(bootstrap_stage3_hash_file "$candidate_sanity")
  sanity_status=fail
  if [ "$version_status" -eq 0 ] && [ "$version" = "simple-bootstrap 1.0.0-RC" ] && \
    [ "$unsupported_status" -eq 1 ] && case "$unsupported" in *"unknown command 'run'"*) true;; *) false;; esac && \
    [ "$frontend_status" -eq 0 ] && [ "$before" = "$after" ]; then sanity_status=pass; fi
  { echo schema=simple-bootstrap-sanity-evidence-v1; echo status="$sanity_status"; \
    echo candidate_sha256_before="$before"; echo version_status="$version_status"; \
    echo version_output="$version"; echo unsupported_status="$unsupported_status"; \
    printf 'unsupported_output_sha256=%s\n' "$(printf %s "$unsupported" | bootstrap_stage3_hash_stream)"; \
    echo frontend_smoke_status="$frontend_status"; \
    echo frontend_smoke_bootstrap_mode_status="$frontend_bootstrap_status"; \
    echo frontend_smoke_output_sha256="$(bootstrap_stage3_hash_file "$frontend_log")"; \
    echo candidate_sha256_after="$after"; } >"$evidence_tmp"
  mv "$evidence_tmp" "$evidence"; rm -f "$frontend_log"; [ "$sanity_status" = pass ]
)
bootstrap_stage_sanity "$candidate" "$stage3_sanity" "$home" "$tmp" "$path"
bootstrap_stage3_source_snapshot "$source_after" "$root"
bootstrap_stage3_git_state "$root" "$git_after"
bootstrap_stage3_tool_authority_snapshot "$tool_after" "$path" "$root"
cmp -s "$source_before" "$source_after"
cmp -s "$git_before" "$git_after"
cmp -s "$tool_before" "$tool_after"

BSTAGE3_ROOT=$root BSTAGE3_MANIFEST=$manifest BSTAGE3_PLATFORM=$platform
BSTAGE3_BACKEND=$stage2_backend BSTAGE3_MODE=dynload BSTAGE3_SEED=$seed
BSTAGE3_SEED_STAMP=$stamp BSTAGE3_NATIVE_ALL=$native_all BSTAGE3_BACKFILL=$backfill
BSTAGE3_RUNTIME_ORIGIN_BEFORE=$runtime_origin_before BSTAGE3_RUNTIME_ORIGIN_AFTER=$runtime_origin_after
BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT=$runtime_admitted BSTAGE3_TOOL_AUTHORITY=$tool_after
BSTAGE3_TOOL_AUTHORITY_BEFORE=$tool_before
BSTAGE3_STAGE2=$stage2 BSTAGE3_STAGE2_ADMITTED=$admitted
BSTAGE3_STAGE2_ADMISSION=$stage2_admission BSTAGE3_STAGE3=$candidate
BSTAGE3_SOURCE_BEFORE=$source_before BSTAGE3_SOURCE_AFTER=$source_after
BSTAGE3_STAGE2_LOG=$stage2_log BSTAGE3_STAGE3_LOG=$stage3_log
BSTAGE3_STAGE2_ARGS_SHA256=$stage2_args BSTAGE3_STAGE3_ARGS_SHA256=$stage3_args
BSTAGE3_STAGE2_THREADS=$stage2_threads BSTAGE3_STAGE3_THREADS=1
BSTAGE3_STAGE2_CACHE_DIR=$stage2_cache BSTAGE3_STAGE3_CACHE_DIR=$stage3_cache
BSTAGE3_RUNTIME_PATH=$runtime BSTAGE3_STAGE2_COMMAND_OUTPUT=$stage2
BSTAGE3_STAGE3_COMMAND_OUTPUT=$candidate BSTAGE3_BOOTSTRAP_SCRIPT=$script
BSTAGE3_HELPER=$helper BSTAGE3_HELPER_SHA256_BEFORE=$helper_sha_before
BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE=$helper_bundle_before
BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE=$script_sha_before
BSTAGE3_SEED_INPUTS_FINGERPRINT=$seed_fingerprint BSTAGE3_SEED_FEATURES=
BSTAGE3_GIT_BEFORE=$git_before BSTAGE3_GIT_AFTER=$git_after
BSTAGE3_STAGE2_TRANSCRIPT=$stage2_transcript BSTAGE3_STAGE3_TRANSCRIPT=$stage3_transcript
BSTAGE3_STAGE2_SANITY=$stage2_sanity BSTAGE3_STAGE2_RECEIVER=$stage2_receiver
BSTAGE3_STAGE3_SANITY=$stage3_sanity
BSTAGE3_LOCK=$lock BSTAGE3_RUST_LOG=error
export BSTAGE3_ROOT BSTAGE3_MANIFEST BSTAGE3_PLATFORM BSTAGE3_BACKEND BSTAGE3_MODE \
  BSTAGE3_SEED BSTAGE3_SEED_STAMP BSTAGE3_NATIVE_ALL BSTAGE3_BACKFILL \
  BSTAGE3_RUNTIME_ORIGIN_BEFORE BSTAGE3_RUNTIME_ORIGIN_AFTER \
  BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT BSTAGE3_TOOL_AUTHORITY \
  BSTAGE3_TOOL_AUTHORITY_BEFORE BSTAGE3_STAGE2 BSTAGE3_STAGE2_ADMITTED \
  BSTAGE3_STAGE2_ADMISSION BSTAGE3_STAGE3 BSTAGE3_SOURCE_BEFORE BSTAGE3_SOURCE_AFTER \
  BSTAGE3_STAGE2_LOG BSTAGE3_STAGE3_LOG BSTAGE3_STAGE2_ARGS_SHA256 \
  BSTAGE3_STAGE3_ARGS_SHA256 BSTAGE3_STAGE2_THREADS BSTAGE3_STAGE3_THREADS \
  BSTAGE3_STAGE2_CACHE_DIR BSTAGE3_STAGE3_CACHE_DIR BSTAGE3_RUNTIME_PATH \
  BSTAGE3_STAGE2_COMMAND_OUTPUT BSTAGE3_STAGE3_COMMAND_OUTPUT BSTAGE3_BOOTSTRAP_SCRIPT \
  BSTAGE3_HELPER BSTAGE3_HELPER_SHA256_BEFORE BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE \
  BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE BSTAGE3_SEED_INPUTS_FINGERPRINT \
  BSTAGE3_SEED_FEATURES BSTAGE3_GIT_BEFORE BSTAGE3_GIT_AFTER \
  BSTAGE3_STAGE2_TRANSCRIPT BSTAGE3_STAGE3_TRANSCRIPT BSTAGE3_STAGE2_SANITY \
  BSTAGE3_STAGE2_RECEIVER BSTAGE3_STAGE3_SANITY BSTAGE3_LOCK BSTAGE3_RUST_LOG
bootstrap_stage3_write_manifest
bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate"
}

# --- folded: bootstrap-windows.sh -------------------------------------------
# Windows (Git Bash / MSYS2) entry. bootstrap-windows.cmd calls this as
# `bootstrap-from-scratch.sh windows-entry <args...>`.
bootstrap_folded_windows_entry() {
  bwe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
  bwe_abi="${SIMPLE_WINDOWS_ABI:-}"
  bwe_saved_count=$#
  for bwe_arg in "$@"; do
    case "$bwe_arg" in
      --msvc) bwe_abi="msvc" ;;
      --mingw) bwe_abi="gnu" ;;
      *) set -- "$@" "$bwe_arg" ;;
    esac
  done
  shift "$bwe_saved_count"
  case "${bwe_abi}" in
    "") ;;
    gnu|msvc) SIMPLE_WINDOWS_ABI="${bwe_abi}"; export SIMPLE_WINDOWS_ABI ;;
    *) echo "error: SIMPLE_WINDOWS_ABI must be gnu or msvc" >&2; exit 1 ;;
  esac
  # Materialize git symlinks as NTFS junctions/hardlinks before anything else
  # reads the tree. A checkout done by a Windows session that lacks a
  # fresh-logon SeCreateSymbolicLinkPrivilege token (see
  # doc/08_tracking/bug/windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md)
  # degrades every git symlink to a plain text placeholder file containing the
  # literal target string -- `src/compiler/backend` (an alias for the numbered
  # `70.backend` layer dir) and dozens like it would silently resolve to
  # nothing, breaking the loader in confusing ways far from this root cause.
  # No-op, fast, and idempotent on a checkout where symlinks already resolved
  # correctly (e.g. an elevated or Developer-Mode-since-logon session).
  sh "${bwe_dir}/../setup/materialize-symlinks-windows.shs" "${bwe_dir}/../.." || {
    echo "warning: symlink materialization reported failures; continuing, but the build may hit missing-source errors below" >&2
  }
  exec sh "${bwe_dir}/bootstrap-from-scratch.sh" "$@"
}

# --- subcommand dispatch -----------------------------------------------------
# Runs before option parsing so a folded helper is reached by name, not a flag.
case "${1:-}" in
  preserve-phase-binary)
    shift; bootstrap_folded_preserve_phase_binary "$@"; exit $? ;;
  progress-watch)
    shift; bootstrap_folded_progress_watch "$@"; exit $? ;;
  planner-admission-v2)
    shift; bootstrap_folded_planner_admission_v2 "$@"; exit $? ;;
  stage2-sanity-diagnostic)
    shift; bootstrap_folded_stage2_sanity_diagnostic "$@"; exit $? ;;
  rollback-deploy)
    shift; bootstrap_folded_rollback_deploy "$@"; exit $? ;;
  stage4-tooling-matrix)
    shift; bootstrap_folded_stage4_tooling_matrix "$@"; exit $? ;;
  stage4-tools-only)
    shift; bootstrap_folded_stage4_tools_only "$@"; exit $? ;;
  resume-stage3)
    shift; bootstrap_folded_resume_stage3 "$@"; exit $? ;;
  windows-entry)
    shift; bootstrap_folded_windows_entry "$@"; exit $? ;;
esac

# Sourced as a pure function library (tests and sibling gates): stop here.
if [ "${BOOTSTRAP_LIB_ONLY:-0}" = "1" ]; then
  return 0 2>/dev/null || exit 0
fi

# The coordinated strategy supervisor is the default entry for an ordinary
# multi-stage bootstrap. Single-stage recovery, receipt validation, help, and
# diagnostic sweeps keep their direct fail-closed paths. The supervisor sets
# SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED before launching this stage engine.
if [ "${SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED:-0}" != 1 ]; then
  bootstrap_strategy_entry=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P) || exit 70
  bootstrap_strategy_arg=${SIMPLE_BOOTSTRAP_STRATEGY:-normal}
  bootstrap_strategy_output=build/bootstrap
  bootstrap_strategy_bypass=0
  bootstrap_strategy_expect_value=0
  for bootstrap_strategy_option in "$@"; do
    if [ "${bootstrap_strategy_expect_value}" -eq 1 ]; then
      bootstrap_strategy_arg=${bootstrap_strategy_option}
      bootstrap_strategy_expect_value=0
      continue
    fi
    case "${bootstrap_strategy_option}" in
      --strategy=*) bootstrap_strategy_arg=${bootstrap_strategy_option#*=} ;;
      --strategy) bootstrap_strategy_expect_value=1 ;;
      --output=*) bootstrap_strategy_output=${bootstrap_strategy_option#*=} ;;
      --help|--validate-bootstrap-receipt|--stop-after-stage2|--stop-after-stage3|\
      --resume-stage3-from-admitted=*|--resume-stage4-from-admitted=*|--diagnostic-sweep)
        bootstrap_strategy_bypass=1
        ;;
      --target=simpleos-*|--target=freebsd-*) bootstrap_strategy_bypass=1 ;;
    esac
  done
  if [ "${bootstrap_strategy_bypass}" -eq 0 ] &&
     [ -x "${bootstrap_strategy_entry}/bootstrap-strategy.sh" ]; then
    exec "${bootstrap_strategy_entry}/bootstrap-strategy.sh" \
      --strategy="${bootstrap_strategy_arg}" \
      --output="${bootstrap_strategy_output}" -- "$@"
  fi
fi

# Keep bootstrap and every non-detached descendant in one dedicated kernel
# process group. Lock recovery remains fail-closed while any group member lives.
bootstrap_entry_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P) || exit 70
bootstrap_session_helper=\
"${bootstrap_entry_dir}/../check/lib/portable-session-exec.pl"
if [ "${SIMPLE_BOOTSTRAP_SESSION_READY:-0}" = 1 ]; then
  bootstrap_session_identity=$(perl "${bootstrap_session_helper}" \
    --identity-parent) || {
    echo "error: bootstrap could not verify its native session identity" >&2
    exit 70
  }
  bootstrap_session_pid=$(printf '%s\n' "${bootstrap_session_identity}" |
    sed -n 's/^pid=//p')
  bootstrap_session_pgid=$(printf '%s\n' "${bootstrap_session_identity}" |
    sed -n 's/^pgid=//p')
  case "${bootstrap_session_pid}" in
    ''|*[!0-9]*) bootstrap_session_pid=invalid ;;
  esac
  case "${bootstrap_session_pgid}" in
    ''|*[!0-9]*) bootstrap_session_pgid=invalid ;;
  esac
  [ "${bootstrap_session_pid}" = "${bootstrap_session_pgid}" ] || {
    echo "error: bootstrap session guard was bypassed without PID=PGID" >&2
    exit 70
  }
else
  SIMPLE_BOOTSTRAP_SESSION_READY=1
  export SIMPLE_BOOTSTRAP_SESSION_READY
  exec perl "${bootstrap_session_helper}" \
    /bin/sh "$0" "$@"
fi
set -eu
bootstrap_early_repo_root=$(CDPATH= cd -- "${bootstrap_entry_dir}/../.." && pwd -P) || exit 70
. "${bootstrap_early_repo_root}/scripts/check/lib/bootstrap-planner-admission-bound.shs"

# Bootstrap wrapper for Linux, macOS, Windows/MSYS2, and FreeBSD.
#
# Output layout uses <arch>-<vendor>-<os>-<abi> target triple:
#   build/bootstrap/stage{1,2,3}/<triple>/simple
#
# Triple examples:
#   Linux:   x86_64-unknown-linux-gnu
#   FreeBSD: x86_64-unknown-freebsd-elf

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-from-scratch.sh [options]

Bootstrap wrapper.

Linux / macOS / Windows (Git Bash or MSYS2) / FreeBSD:
  Runs the verified staged bootstrap pipeline using the active runtime binary.

SimpleOS / --target=simpleos-x86_64:
  Runs the host-driven SimpleOS bootstrap target lane and stages guest artifacts
  for the underlying x86_64-simpleos lane.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple

Options:
  --backend=<name>   Backend for stage2/stage3/stage4 (default: llvm; cranelift also supported)
  --output=<dir>     Output directory for bootstrap artifacts (default: build/bootstrap)
  --bootstrap-receipt=<path>
                     Canonical non-None typed-reason receipt emitted by
                     `simple build bootstrap`; required before any stage starts
  --validate-bootstrap-receipt
                     Validate authorization and exit without starting a stage
  --stop-after-stage3
                     Stop after producing and independently verifying the
                     provenance-bound Stage 3 compiler. Requires a planner
                     receipt targeting //bootstrap:stage3 and never starts
                     Stage 4, deployment, release, or diagnostic lanes.
  --full-bootstrap   Rebuild the Rust seed/runtime when missing or stale, then
                     rebuild the pure-Simple stages. Without this flag bootstrap
                     never runs cargo and reuses the existing Rust seed.
  --strategy=<name>  Bootstrap scheduling strategy: adhoc, normal, or full
                     (default: normal; env: SIMPLE_BOOTSTRAP_STRATEGY).
                     normal reuses incremental caches and schedules isolated
                     phase verification; full inventories every eligible build
                     and test to a terminal summary even after task crashes.
  --stop-after-stage2
                     With --full-bootstrap, build and admit the measured
                     Stage-2 trust root, then stop before Stage 3. This is the
                     sole receipt-free bootstrap lane.
  --resume-stage3-from-admitted=<output>
                     Resume only Stage 3 from OUTPUT's frozen admitted Stage 2
                     using a new one-thread recovery transcript/evidence lane.
  --resume-stage4-from-admitted=<output>
                     Continue at Stage 4 from OUTPUT's provenance-admitted
                     Stage 3 without rebuilding or mutating Stage 2/3.
  --pure-simple      Compatibility alias for the default no-Rust rebuild mode.
  --mode=<name>      Pure-Simple build mode: dynload or one-binary
                     (default: dynload; env: SIMPLE_BOOTSTRAP_MODE)
                     SIMPLE_NO_STUB_FALLBACK=1 also makes staged failures fatal
  --full-cli         Relink the full CLI after the staged pure-Simple build
                     (supported on native Linux and macOS hosts).
                     Implied by --deploy and one-binary mode.
  --fresh-cache      Clear the dynload native cache once before rebuilding
  --incremental-unlimited
                     Reuse incremental caches, including one-binary Stage 4,
                     and use every detected host CPU; retain Stage 4
                     structural streaming ownership
  --diagnostic-sweep Continue checking independent .spl files after failures,
                     group all diagnostics, and never build or deploy artifacts
  --diagnostics[=MODE]
                     Opt-in compiler observability: debug or test (default:
                     off; bare --diagnostics selects debug; env:
                     SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE). Both modes imply
                     --progress. Debug also keeps LLVM IR and memory snapshots.
  --diagnostic-root=<path>
                     File or directory selected by --diagnostic-sweep
                     (default: src/compiler, src/lib, and src/app; repeatable)
  --diagnostic-child-compiler=<path>
                     Admitted pure-Simple worker used by diagnostic check
                     processes (default: bin/simple; env:
                     SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER)
  --clean-release    Final release proof: deploy and test a clean build while
                     clearing every reusable native cache before each batch
  --deploy           Copy the resulting/compiler artifact into bin/simple when supported
  --release          Deploy, then run the release-blocking whole test suite
  --target=<triple>  Target platform (freebsd-x86_64 or simpleos-x86_64)
  --verbose          Accepted for compatibility
  --jobs=<n|full|half|min|auto>
                     Native build workers (default: half CPUs locally, 2 on GitHub Actions)
  --no-mcp           Skip MCP server builds (Stage 5)
  --keep-artifacts   Accepted for compatibility; artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --progress[=<path>]
                     Append milestone/liveness samples to PATH (default:
                     <output>/bootstrap-progress.log; env: SIMPLE_BOOTSTRAP_PROGRESS_LOG)
  --progress-interval=<seconds>
                     Liveness sample interval (default: 30; env:
                     SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL)
  --release-local    Alias for --release (deploy, then the release-blocking
                     whole test suite against the local deployment)

Folded subcommands (first positional argument; every folded bootstrap helper
script now lives inside this file and is reached by name):
  preserve-phase-binary <bin> <phase>
                     Snapshot a phase binary into build/phase_snapshots
  progress-watch [args]
                     Standalone bootstrap progress/liveness watcher
  planner-admission-v2 --target=... --reason=... [args]
                     Emit/validate a v2 bootstrap planner admission receipt
  stage2-sanity-diagnostic [--selftest]
                     Stage-2 sanity-diagnostic gate selftest
  rollback-deploy [<triple>]
                     Roll back the last bin/release bootstrap deployment
  stage4-tooling-matrix [args]
                     Stage 4 tooling matrix build/verify lane
  stage4-tools-only [args]
                     Stage 4 tools-only lane
  resume-stage3 <output>
                     Stage 3 one-thread recovery lane (also reachable as
                     --resume-stage3-from-admitted=<output>)
  windows-entry [--msvc|--mingw] [opts]
                     Windows (Git Bash/MSYS2) entry: materialize NTFS symlinks,
                     then re-enter this wrapper (used by bootstrap-windows.cmd)

  --help             Show this help

Subcommands (folded former sibling scripts; must be the FIRST argument):
  preserve-phase-binary <binary> <phase>|--gc <days>
                     Immutable lineage snapshots of phase compiler binaries
  progress-watch --pid=N --progress-log=PATH [options]
                     Milestone/liveness progress sampler
  planner-admission-v2 --target=... [--selftest]
                     Mint/verify the bootstrap planner admission-v2 receipt
  stage2-sanity-diagnostic [args]
                     Stage-2 sanity failure diagnostic
  rollback-deploy [args]
                     Roll back a bootstrap deploy from its receipt
  stage4-tooling-matrix [args]
                     Stage-4 tools-only matrix (consumes admitted Stage-3
                     artifacts; never builds or admits a compiler)
  stage4-tools-only [args]
                     Single Stage-4 tool compile/link step
  resume-stage3 OUTPUT_DIR
                     Resume Stage 3 from OUTPUT_DIR's frozen admitted Stage 2
  windows-entry [--msvc|--mingw] [options]
                     Windows (Git Bash/MSYS2) entry used by bootstrap-windows.cmd

Library use (pure predicate/helper functions, no pipeline):
  BOOTSTRAP_LIB_ONLY=1 . scripts/bootstrap/bootstrap-from-scratch.sh
EOF
}

backend="llvm"
output_dir="build/bootstrap"
deploy=0
build_mcp=1
target=""
verbose=0
jobs=""
pure_simple=0
full_bootstrap=0
resume_stage3_output=""
resume_stage4_output=""
full_cli=0
fresh_cache=0
release_tests=0
diagnostic_sweep=0
stop_after_stage2=0
diagnostic_roots=""
diagnostic_child_compiler="${SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER:-bin/simple}"
diagnostics_mode="${SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE:-off}"
# Progress heartbeat is ON by default. A stage can run 15+ minutes writing
# nothing -- stage2-native-build.log was 337 bytes for an entire stage -- so a
# silent run is indistinguishable from a hung one. Three sessions killed healthy
# builds on that ambiguity (one had already finished 62/62). The watcher is a
# separate process that wakes every progress_interval seconds; it does not touch
# the build's own I/O path, so enabling it costs one sleeping process and one
# short line per interval. Set SIMPLE_BOOTSTRAP_PROGRESS_LOG= (empty) to opt out.
progress_log="${SIMPLE_BOOTSTRAP_PROGRESS_LOG-default}"
progress_interval="${SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL:-30}"
execution_profile="${SIMPLE_BOOTSTRAP_EXECUTION_PROFILE:-incremental}"
bootstrap_strategy="${SIMPLE_BOOTSTRAP_STRATEGY:-normal}"
bootstrap_mode="${SIMPLE_BOOTSTRAP_MODE:-dynload}"
bootstrap_receipt_path="${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}"
validate_bootstrap_receipt=0
stop_after_stage3=0
stage3_current_acceptance_status=unverified
case "${SIMPLE_NO_STUB_FALLBACK:-0}" in
  1|true|yes|on) strict_bootstrap=1 ;;
  *) strict_bootstrap=0 ;;
esac

while [ "$#" -gt 0 ]; do
  case "$1" in
    --backend=*)
      backend=${1#*=}
      ;;
    --output=*)
      output_dir=${1#*=}
      ;;
    --bootstrap-receipt=*)
      bootstrap_receipt_path=${1#*=}
      ;;
    --validate-bootstrap-receipt)
      validate_bootstrap_receipt=1
      ;;
    --stop-after-stage3)
      stop_after_stage3=1
      ;;
    --target=*)
      target=${1#*=}
      ;;
    --jobs=*)
      jobs=${1#*=}
      ;;
    --deploy)
      deploy=1
      ;;
    --release|--release-local)
      release_tests=1
      deploy=1
      ;;
    --full-bootstrap)
      full_bootstrap=1
      ;;
    --strategy=*)
      bootstrap_strategy=${1#*=}
      ;;
    --strategy)
      shift
      if [ "$#" -eq 0 ]; then
        echo "error: --strategy requires adhoc, normal, or full" >&2
        usage >&2
        exit 1
      fi
      bootstrap_strategy=$1
      ;;
    --resume-stage3-from-admitted=*)
      resume_stage3_output=${1#*=}
      ;;
    --resume-stage4-from-admitted=*)
      resume_stage4_output=${1#*=}
      ;;
    --pure-simple)
      pure_simple=1
      ;;
    --full-cli)
      full_cli=1
      ;;
    --fresh-cache|--no-cache)
      fresh_cache=1
      ;;
    --incremental-unlimited)
      execution_profile=incremental-unlimited
      ;;
    --diagnostic-sweep)
      diagnostic_sweep=1
      ;;
    --stop-after-stage2)
      stop_after_stage2=1
      ;;
    --diagnostics)
      diagnostics_mode=debug
      ;;
    --diagnostics=*)
      diagnostics_mode=${1#*=}
      ;;
    --diagnostic-root=*)
      diagnostic_root=${1#*=}
      if [ -z "${diagnostic_root}" ]; then
        echo "error: --diagnostic-root requires a path" >&2
        exit 1
      fi
      diagnostic_roots="${diagnostic_roots} --root=${diagnostic_root}"
      ;;
    --diagnostic-child-compiler=*)
      diagnostic_child_compiler=${1#*=}
      if [ -z "${diagnostic_child_compiler}" ]; then
        echo "error: --diagnostic-child-compiler requires a path" >&2
        exit 1
      fi
      ;;
    --clean-release)
      execution_profile=clean-release
      fresh_cache=1
      release_tests=1
      deploy=1
      ;;
    --mode=*)
      bootstrap_mode=${1#*=}
      if [ -z "${bootstrap_mode}" ]; then
        bootstrap_mode=dynload
      fi
      ;;
    --mode)
      shift
      if [ "$#" -eq 0 ]; then
        echo "error: --mode requires dynload or one-binary" >&2
        usage >&2
        exit 1
      fi
      bootstrap_mode=$1
      ;;
    --verbose)
      verbose=1
      ;;
    --no-mcp)
      build_mcp=0
      ;;
    --keep-artifacts|--no-verify)
      ;;
    --progress)
      progress_log=default
      ;;
    --progress=*)
      progress_log=${1#*=}
      [ -n "${progress_log}" ] || progress_log=default
      ;;
    --progress-interval=*)
      progress_interval=${1#*=}
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option '$1'" >&2
      usage >&2
      exit 1
      ;;
  esac
  shift
done

if [ "${stop_after_stage2}" -eq 1 ]; then
  [ "${stop_after_stage3}" -eq 0 ] &&
    [ -z "${resume_stage3_output}" ] && [ -z "${resume_stage4_output}" ] &&
    [ "${full_cli}" -eq 0 ] && [ "${deploy}" -eq 0 ] &&
    [ "${release_tests}" -eq 0 ] && [ "${diagnostic_sweep}" -eq 0 ] &&
    [ "${diagnostics_mode}" = off ] && [ "${bootstrap_mode}" = dynload ] || {
    echo "error: --stop-after-stage2 excludes Stage 3/4, resume/full-cli/deploy/release/diagnostic options and requires --mode=dynload" >&2
    exit 1
  }
  case "${target}" in
    simpleos-x86_64)
      echo "error: --stop-after-stage2 is unavailable for the SimpleOS target lane" >&2
      exit 1
      ;;
  esac
elif [ "${stop_after_stage3}" -eq 1 ]; then
  [ -z "${resume_stage3_output}" ] && [ -z "${resume_stage4_output}" ] &&
    [ "${full_cli}" -eq 0 ] && [ "${deploy}" -eq 0 ] &&
    [ "${release_tests}" -eq 0 ] && [ "${diagnostic_sweep}" -eq 0 ] &&
    [ "${diagnostics_mode}" = off ] && [ "${bootstrap_mode}" = dynload ] || {
    echo "error: --stop-after-stage3 excludes resume/full-cli/deploy/release/diagnostic options and requires --mode=dynload" >&2
    exit 1
  }
fi

# Reject malformed diagnostics options before planner admission. Option syntax
# errors are non-executing and must remain diagnosable without a stage receipt.
case "${diagnostics_mode}" in
  off|test|debug) ;;
  *)
    echo "error: --diagnostics requires off, debug, or test (got '${diagnostics_mode}')" >&2
    exit 1
    ;;
esac

# This is the common staged-bootstrap boundary, including Windows forwarding
# and admitted Stage 3 resume. A direct/ad-hoc invocation cannot start even
# Stage 1 without the canonical receipt produced by the pure-Simple planner.
bootstrap_stage2_trust_root=0
if [ "${stop_after_stage2}" -eq 1 ] && [ "${full_bootstrap}" -eq 1 ] &&
   { [ -z "${bootstrap_receipt_path}" ] || [ ! -f "${bootstrap_receipt_path}" ]; }; then
  # The first independently admitted pure-Simple parent cannot itself require
  # a receipt produced by that parent. Keep this trust-root exception narrower
  # than every ordinary/resume/deploy path: explicit Rust rebuild, native
  # Stage-2-only stop, dynload mode, and the full Stage 2 admission gates below.
  bootstrap_stage2_trust_root=1
  bootstrap_reason=stage2-trust-root-refresh
elif [ -z "${bootstrap_receipt_path}" ] || [ ! -f "${bootstrap_receipt_path}" ]; then
  # The named command must be one that PLANS a receipt, never one that starts a
  # stage, and must list every flag the planner requires. The old wording named
  # 'simple build bootstrap --bootstrap-reason=... --bootstrap-receipt=...',
  # which on the Rust seed silently dropped both flags and started a real Stage 1
  # native-build. Gated by scripts/check/check-bootstrap-receipt-instruction.shs.
  echo "bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path> --parent-compiler-sha256=<hex64> --runtime-snapshot-sha256=<hex64> --planner-source-closure-sha256=<hex64> --planner-sha256=<hex64>'" >&2
  exit 64
fi
if [ "${bootstrap_stage2_trust_root}" -eq 0 ]; then
  case "${bootstrap_receipt_path}" in
    /*) ;;
    *) bootstrap_receipt_path="$(pwd -P)/${bootstrap_receipt_path}" ;;
  esac
  bootstrap_receipt_target='//bootstrap:stage4'
  if [ "${stop_after_stage2}" -eq 1 ]; then
    bootstrap_receipt_target='//bootstrap:stage2'
  elif [ -n "${resume_stage3_output}" ] || [ "${stop_after_stage3}" -eq 1 ]; then
    bootstrap_receipt_target='//bootstrap:stage3'
  fi
  bootstrap_planner_v2_verify "${bootstrap_receipt_path}" "${bootstrap_early_repo_root}" || {
    echo "bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2" >&2
    exit 64
  }
  [ "$(bootstrap_planner_v2_field target "${bootstrap_receipt_path}")" = "${bootstrap_receipt_target}" ] || {
    echo "bootstrap-policy-error: planner-admission-target-mismatch" >&2
    exit 64
  }
  bootstrap_reason=$(bootstrap_planner_v2_field reason "${bootstrap_receipt_path}") || exit 64
  SIMPLE_BOOTSTRAP_REASON_RECEIPT=${bootstrap_receipt_path}
  export SIMPLE_BOOTSTRAP_REASON_RECEIPT
fi
if [ "${validate_bootstrap_receipt}" -eq 1 ]; then
  echo "bootstrap-policy: receipt-valid target=${bootstrap_receipt_target} reason=${bootstrap_reason} execution=not-attempted"
  exit 0
fi

case "${progress_interval}" in
  ''|*[!0-9]*|0)
    echo "error: --progress-interval requires a positive integer" >&2
    exit 1
    ;;
esac

case "${backend}" in
  llvm|llvm-lib|cranelift) ;;
  *)
    echo "error: unsupported bootstrap backend '${backend}' (expected llvm, llvm-lib, or cranelift)" >&2
    exit 1
    ;;
esac

case "${bootstrap_mode}" in
  dynload|one-binary) ;;
  *)
    echo "error: unknown --mode '${bootstrap_mode}' (expected dynload or one-binary)" >&2
    exit 1
    ;;
esac

case "${execution_profile}" in
  incremental|incremental-unlimited|clean-release) ;;
  *)
    echo "error: unknown bootstrap execution profile '${execution_profile}'" >&2
    exit 1
    ;;
esac

bootstrap_strategy_validate "${bootstrap_strategy}" || {
  echo "error: unknown --strategy '${bootstrap_strategy}' (expected adhoc, normal, or full)" >&2
  exit 1
}
bootstrap_failure_policy=$(bootstrap_strategy_failure_policy "${bootstrap_strategy}")
SIMPLE_BOOTSTRAP_STRATEGY=${bootstrap_strategy}
SIMPLE_BOOTSTRAP_FAILURE_POLICY=${bootstrap_failure_policy}
export SIMPLE_BOOTSTRAP_STRATEGY SIMPLE_BOOTSTRAP_FAILURE_POLICY

if [ "${stop_after_stage2}" -eq 1 ] && [ -n "${resume_stage3_output}" ]; then
  echo "error: --stop-after-stage2 and --resume-stage3-from-admitted conflict" >&2
  exit 1
fi

if [ -n "${resume_stage3_output}" ]; then
  [ "${full_bootstrap}" -eq 0 ] && [ "${full_cli}" -eq 0 ] &&
    [ "${fresh_cache}" -eq 0 ] && [ "${deploy}" -eq 0 ] &&
    [ "${release_tests}" -eq 0 ] && [ "${diagnostic_sweep}" -eq 0 ] &&
    [ "${diagnostics_mode}" = off ] || {
    echo "error: Stage 3 resume is mutually exclusive with rebuild/deploy/diagnostic options" >&2
    exit 1
  }
  case "${jobs}" in ''|1) ;; *) echo "error: Stage 3 resume permits only --jobs=1 (it execs resume-stage3-from-admitted.sh, which takes no jobs argument and pins the stage-3 recompile to --threads 1; a jobs value here would be silently ignored)" >&2; exit 1 ;; esac
  exec /bin/sh "$0" resume-stage3 "${resume_stage3_output}"
fi

if [ -n "${resume_stage4_output}" ]; then
  [ -z "${resume_stage3_output}" ] && [ "${full_bootstrap}" -eq 0 ] &&
    [ "${fresh_cache}" -eq 0 ] && [ "${release_tests}" -eq 0 ] &&
    [ "${diagnostic_sweep}" -eq 0 ] && [ "${diagnostics_mode}" = off ] &&
    [ "${deploy}" -eq 1 ] || {
    echo "error: Stage 4 resume requires --deploy and excludes rebuild/release/diagnostic options" >&2
    exit 1
  }
  case "${jobs}" in ''|1) jobs=1 ;; *) echo "error: Stage 4 resume permits only --jobs=1 (resume reuses the already-admitted stage-3 artifact and only relinks the full CLI; a jobs value here would be silently ignored)" >&2; exit 1 ;; esac
  output_dir=${resume_stage4_output}
  full_cli=1
fi

case "${diagnostics_mode}" in
  off) ;;
  test)
    [ -n "${progress_log}" ] || progress_log=default
    SIMPLE_COMPILER_PHASE_PROFILE=${SIMPLE_COMPILER_PHASE_PROFILE:-1}
    export SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE SIMPLE_COMPILER_PHASE_PROFILE
    ;;
  debug)
    [ -n "${progress_log}" ] || progress_log=default
    SIMPLE_BOOTSTRAP_DIAG=${SIMPLE_BOOTSTRAP_DIAG:-1}
    SIMPLE_COMPILER_TRACE=${SIMPLE_COMPILER_TRACE:-1}
    SIMPLE_COMPILER_PHASE_PROFILE=${SIMPLE_COMPILER_PHASE_PROFILE:-1}
    SIMPLE_KEEP_LLVM_IR=${SIMPLE_KEEP_LLVM_IR:-1}
    SIMPLE_MEM_SNAPSHOT=${SIMPLE_MEM_SNAPSHOT:-1}
    export SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE SIMPLE_BOOTSTRAP_DIAG
    export SIMPLE_COMPILER_TRACE SIMPLE_COMPILER_PHASE_PROFILE
    export SIMPLE_KEEP_LLVM_IR SIMPLE_MEM_SNAPSHOT
    ;;
  *)
    echo "error: --diagnostics requires off, debug, or test (got '${diagnostics_mode}')" >&2
    exit 1
    ;;
esac

if [ "${pure_simple}" -eq 1 ] && [ "${full_bootstrap}" -eq 1 ]; then
  echo "error: --pure-simple and --full-bootstrap conflict" >&2
  exit 1
fi

if [ "${deploy}" -eq 1 ] || [ "${bootstrap_mode}" = "one-binary" ]; then
  full_cli=1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/../.." && pwd)
cd "${repo_root}"
BOOTSTRAP_STAGE3_FACADE_PATH=\
"${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "${BOOTSTRAP_STAGE3_FACADE_PATH}"
PORTABLE_LOCK_ATOMIC_HELPER_PATH=\
"${repo_root}/scripts/check/lib/portable-hardlink-lock.pl"
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
# The immutable authority publication below republishes the seed by SYMLINK,
# which Windows shells will silently turn into a copy unless told otherwise.
. "${repo_root}/scripts/check/lib/portable-symlink-mode.shs"
. "${repo_root}/scripts/check/lib/portable-process-lock.shs"
bootstrap_runtime_authority_path=\
"${repo_root}/src/compiler_rust/target/bootstrap"
bootstrap_script_path="${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh"
bootstrap_script_sha256_before=$(bootstrap_stage3_hash_file "${bootstrap_script_path}")
bootstrap_provenance_helper="${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
bootstrap_provenance_helper_sha256_before=$(
  bootstrap_stage3_hash_file "${bootstrap_provenance_helper}"
)
bootstrap_provenance_bundle_fingerprint_before=$(
  bootstrap_stage3_helper_bundle_fingerprint
)
STAGE4_PROVENANCE_HELPER_PATH=\
"${repo_root}/scripts/check/lib/stage4-candidate-provenance.shs"
export STAGE4_PROVENANCE_HELPER_PATH
. "${STAGE4_PROVENANCE_HELPER_PATH}"
stage4_provenance_helper_sha256_before=$(
  bootstrap_stage3_hash_file "${STAGE4_PROVENANCE_HELPER_PATH}"
)

# Concurrency guard: two bootstraps sharing one ${output_dir} interleave logs
# and race binary writes (observed 2026-07-24: twin stage2 builds truncated
# each other's linked binary to 0 KB, and target/bootstrap/simple was clobbered
# to 0 bytes by the same class of race). Directory-based lock, stale-safe.
bootstrap_lock_handle=
rust_target_lock_handle=
portable_lock_canonical_output "${output_dir}" || {
  echo "error: invalid or inaccessible bootstrap output path: ${output_dir}" >&2
  exit 1
}
output_dir=${PORTABLE_LOCK_CANONICAL_OUTPUT}
bootstrap_lock_root="$(dirname -- "${output_dir}")/.simple-bootstrap-locks"
bootstrap_lock_name="output-$(bootstrap_stage3_args_sha256 "${output_dir}")"
bootstrap_lock_rc=0
portable_lock_acquire "${bootstrap_lock_root}" "${bootstrap_lock_name}" \
  "${SIMPLE_BOOTSTRAP_LOCK_WAIT_SECONDS:-30}" || bootstrap_lock_rc=$?
if [ "${bootstrap_lock_rc}" -ne 0 ]; then
  # Name the ACTUAL cause. Collapsing every rc into "timed out" sent a 2026-08-24
  # Windows/Git Bash session hunting a nonexistent concurrent bootstrap when the
  # real fault was rc=70: the lock helper could not read this host's process
  # identity. Only rc=75 is a genuine timeout.
  case "${bootstrap_lock_rc}" in
    64) bootstrap_lock_reason="invalid lock root or lock name" ;;
    69) bootstrap_lock_reason="lock helper missing: ${PORTABLE_LOCK_ATOMIC_HELPER_PATH:-unset}" ;;
    70) bootstrap_lock_reason="could not determine this process identity (ps/proc unavailable)" ;;
    73) bootstrap_lock_reason="could not create the lock claim file" ;;
    75) bootstrap_lock_reason="timed out waiting for another bootstrap to release it" ;;
    *) bootstrap_lock_reason="unexpected lock error" ;;
  esac
  echo "error: could not acquire bootstrap output ownership: ${output_dir}" >&2
  echo "  reason: ${bootstrap_lock_reason} (rc=${bootstrap_lock_rc})" >&2
  exit 1
fi
bootstrap_lock_handle=${PORTABLE_LOCK_HANDLE}
bootstrap_progress_pid=
deploy_lock_handle=
bootstrap_progress_state=
build_progress_events=
bootstrap_progress_event() {
  [ -n "${build_progress_events}" ] || return 0
  progress_phase=$1
  progress_current=$2
  progress_terminal=${3:-running}
  progress_failed=${4:-unknown}
  if [ "${progress_terminal}" = succeeded ]; then
    printf 'event=build_progress phase=%s unit_kind=tasks done=6 total=6 remaining=0 tasks_done=6 tasks_total=6 tasks_remaining=0 failed=0 cached=unknown current=%s terminal=succeeded\n' \
      "${progress_phase}" "${progress_current}" >>"${build_progress_events}"
  else
    printf 'event=build_progress phase=%s unit_kind=unknown done=unknown total=unknown remaining=unknown tasks_done=unknown tasks_total=unknown tasks_remaining=unknown failed=%s cached=unknown current=%s terminal=%s\n' \
      "${progress_phase}" "${progress_failed}" "${progress_current}" \
      "${progress_terminal}" >>"${build_progress_events}"
  fi
}
bootstrap_progress_mark() {
  [ -n "${progress_log}" ] || return 0
  milestone=$1
  main_log=${2:-}
  {
    echo "milestone=${milestone}"
    echo "main_log=${main_log}"
  } >"${bootstrap_progress_state}.tmp.$$"
  mv "${bootstrap_progress_state}.tmp.$$" "${bootstrap_progress_state}"
  printf 'event=milestone timestamp=%s status=alive pid=%s milestone=%s main_log=%s\n' \
    "$(date +%s)" "$$" "${milestone}" "${main_log:-absent}" >>"${progress_log}"
  case "${milestone}" in
    complete|exit-0)
      bootstrap_progress_event complete complete succeeded 0
      ;;
    exit-*)
      bootstrap_progress_event "${milestone}" failed failed 1
      ;;
    *)
      bootstrap_progress_event "${milestone}" "${milestone}" running unknown
      ;;
  esac
}
bootstrap_cleanup() {
  bootstrap_status=${1:-$?}
  trap - EXIT HUP INT QUIT TERM
  set +e
  resume_stage4_release_continuation_lock
  if [ -n "${progress_log}" ] && [ -n "${bootstrap_progress_state}" ]; then
    bootstrap_progress_mark "exit-${bootstrap_status}" ""
  fi
  if [ -n "${bootstrap_progress_pid}" ]; then
    kill "${bootstrap_progress_pid}" 2>/dev/null || true
    wait "${bootstrap_progress_pid}" 2>/dev/null || true
  fi
  if [ -z "${bootstrap_abnormal_signal:-}" ]; then
    if [ -n "${deploy_lock_handle}" ]; then
      portable_lock_release "${deploy_lock_handle}"
      deploy_lock_handle=
    fi
    if [ -n "${rust_target_lock_handle}" ]; then
      portable_lock_release "${rust_target_lock_handle}"
      rust_target_lock_handle=
    fi
    if [ -n "${bootstrap_lock_handle}" ]; then
      portable_lock_release "${bootstrap_lock_handle}"
      bootstrap_lock_handle=
    fi
  fi
  exit "${bootstrap_status}"
}
bootstrap_signal_exit() {
  bootstrap_abnormal_signal=$1
  bootstrap_signal_status=$2
  trap - HUP INT QUIT TERM
  exit "${bootstrap_signal_status}"
}
bootstrap_abnormal_signal=
trap 'bootstrap_cleanup $?' EXIT
trap 'bootstrap_signal_exit HUP 129' HUP
trap 'bootstrap_signal_exit INT 130' INT
trap 'bootstrap_signal_exit QUIT 131' QUIT
trap 'bootstrap_signal_exit TERM 143' TERM

if [ -n "${progress_log}" ]; then
  [ "${progress_log}" != default ] || progress_log="${output_dir}/bootstrap-progress.log"
  mkdir -p "$(dirname -- "${progress_log}")"
  progress_log="$(CDPATH= cd -- "$(dirname -- "${progress_log}")" && pwd -P)/$(basename -- "${progress_log}")"
  mkdir -p "${output_dir}"
  bootstrap_progress_state="$(CDPATH= cd -- "${output_dir}" && pwd -P)/bootstrap-progress.state"
  build_progress_events="$(CDPATH= cd -- "${output_dir}" && pwd -P)/bootstrap-build-progress.events"
  : >"${progress_log}"
  : >"${build_progress_events}"
  bootstrap_progress_mark starting ""
  sh "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" progress-watch \
    --pid="$$" --state-file="${bootstrap_progress_state}" \
    --event-file="${build_progress_events}" \
    --progress-log="${progress_log}" --interval="${progress_interval}" &
  bootstrap_progress_pid=$!
fi

normalize_target() {
  case "${1-}" in
    simpleos-x86_64|x86_64-simpleos) echo "simpleos-x86_64" ;;
    *) echo "${1-}" ;;
  esac
}

target=$(normalize_target "${target}")

# ===========================================================================
# Platform detection — <arch>-<vendor>-<os>-<abi> target triple
# ===========================================================================

host_os=$(uname -s 2>/dev/null || echo unknown)

if [ "${full_cli}" -eq 1 ]; then
  case "${host_os}" in
    Linux|Darwin) ;;
    *)
      echo "error: Stage 4 full-CLI capsule preparation requires native Linux or macOS" >&2
      exit 1
      ;;
  esac
fi

# FreeBSD must build inside FreeBSD. Linux hosts use the QEMU verifier, which
# syncs the repository and invokes this same wrapper in the guest.
if [ "${target}" = "freebsd-x86_64" ] && [ "${host_os}" != "FreeBSD" ]; then
  echo "error: FreeBSD bootstrap must run inside FreeBSD." >&2
  echo "  Linux host: sh scripts/check/check-freebsd-bootstrap-qemu.shs --full" >&2
  exit 1
fi

# SimpleOS target-lane dispatch (host-driven bootstrap to staged guest artifacts)
if [ "${target}" = "simpleos-x86_64" ]; then
  simpleos_args="--target=simpleos-x86_64 --build-dir=${output_dir}"
  if [ "${verbose}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --verbose"
  fi
  if [ -n "${jobs}" ]; then
    simpleos_args="${simpleos_args} --jobs=${jobs}"
  fi
  if [ "${deploy}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --package"
  fi
  echo "Bootstrap target lane: simpleos-x86_64"
  echo "  guest lane: x86_64-simpleos"
  exec "${repo_root}/bin/simple" run src/os/port/bootstrap_cross.spl -- ${simpleos_args}
fi

# Shared platform detection
. "${repo_root}/scripts/setup/platform-detect.shs"
PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
os="${PLATFORM_OS}"
echo "Platform: ${PLATFORM}"

exe_suffix=""
archive_prefix="lib"
archive_suffix=".a"
if [ "${os}" = "windows" ]; then
  exe_suffix=".exe"
  case "${SIMPLE_LINKER_FLAVOR:-${PLATFORM_ABI}}" in
    gnu|mingw) windows_linker_abi="gnu" ;;
    msvc) windows_linker_abi="msvc" ;;
    *) echo "error: SIMPLE_LINKER_FLAVOR must be gnu, mingw, or msvc on Windows" >&2; exit 1 ;;
  esac
  if [ "${windows_linker_abi}" != "${PLATFORM_ABI}" ]; then
    echo "error: SIMPLE_LINKER_FLAVOR conflicts with SIMPLE_WINDOWS_ABI=${PLATFORM_ABI}" >&2
    exit 1
  fi
  SIMPLE_WINDOWS_ABI="${PLATFORM_ABI}"
  SIMPLE_LINKER_FLAVOR="${windows_linker_abi}"
  export SIMPLE_WINDOWS_ABI SIMPLE_LINKER_FLAVOR
  if [ "${PLATFORM_ABI}" = "msvc" ]; then
    archive_prefix=""
    archive_suffix=".lib"
  else
    archive_prefix="lib"
    archive_suffix=".a"
  fi
fi

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 -q "$1"
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_stream() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 | awk '{print $NF}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_path_list() {
  while IFS= read -r file; do
    printf '%s  %s\n' "$(hash_file "${file}")" "${file}"
  done
}

run_timeout() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "${timeout_seconds}" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "${timeout_seconds}" "$@"
  else
    "$@"
  fi
}

run_timeout_kill() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout -k 1s "${timeout_seconds}s" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout -k 1s "${timeout_seconds}s" "$@"
  else
    "$@"
  fi
}

absolute_path() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "${repo_root}" "$1" ;;
  esac
}

if [ -n "${LLVM_PREFIX:-}" ] && [ -d "${LLVM_PREFIX}/bin" ]; then
  case ":${PATH}:" in
    *":${LLVM_PREFIX}/bin:"*) ;;
    *) export PATH="${LLVM_PREFIX}/bin:${PATH}" ;;
  esac
fi

# Bind builds to existing canonical tool directories. Hosted launchers may
# inject duplicate, missing, or symlinked PATH entries (notably Cryptex paths
# on macOS); those are not stable provenance authorities.
bootstrap_canonical_path=
bootstrap_path_old_ifs=$IFS
IFS=:
for bootstrap_path_entry in ${PATH}; do
  IFS=$bootstrap_path_old_ifs
  # Codex launchers prepend per-invocation arg0 shims that can disappear while
  # a long Rust authority build is running. They are not compiler/tool
  # authorities, and admitting them here makes the later before/after tool
  # snapshot fail solely because the launcher cleaned its temporary session.
  case "${bootstrap_path_entry}" in
    */.codex/tmp/arg0/*) IFS=:; continue ;;
  esac
  [ -d "${bootstrap_path_entry}" ] || {
    IFS=:
    continue
  }
  bootstrap_path_entry=$(
    CDPATH= cd -- "${bootstrap_path_entry}" && pwd -P
  ) || exit 1
  case ":${bootstrap_canonical_path}:" in
    *":${bootstrap_path_entry}:"*) ;;
    *)
      bootstrap_canonical_path=\
"${bootstrap_canonical_path:+${bootstrap_canonical_path}:}${bootstrap_path_entry}"
      ;;
  esac
  IFS=:
done
IFS=$bootstrap_path_old_ifs
[ -n "${bootstrap_canonical_path}" ] || {
  echo "error: canonical bootstrap PATH is empty" >&2
  exit 1
}
PATH=${bootstrap_canonical_path}
export PATH

log_dir="${output_dir}/logs/${PLATFORM}"
mkdir -p "${log_dir}"

host_cpus=$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 2)
case "${host_cpus}" in
  ''|*[!0-9]*) host_cpus=2 ;;
esac
case "${jobs}" in
  ""|auto)
    jobs=""
    ;;
  full)
    jobs="${host_cpus}"
    ;;
  half)
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
    ;;
  min|minimal|minimum)
    jobs=1
    ;;
esac
if [ -z "${jobs}" ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    jobs=2
  elif [ "${execution_profile}" = "clean-release" ]; then
    # A release proof is intentionally full-resource: it must not inherit the
    # conservative incremental scheduler used for developer iteration.
    jobs="${host_cpus}"
  elif [ "${execution_profile}" = "incremental-unlimited" ]; then
    jobs="${host_cpus}"
  else
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
  fi
fi
case "${jobs}" in
  ''|*[!0-9]*|0)
    echo "error: --jobs must be a positive integer" >&2
    exit 1
    ;;
esac
echo "Native build jobs: ${jobs} (host CPUs: ${host_cpus})"
selfhost_jobs="${jobs}"
if [ "${execution_profile}" = "incremental" ] && [ "${selfhost_jobs}" -gt 2 ]; then
  selfhost_jobs=2
fi
echo "Bootstrap execution profile: ${execution_profile} (self-host jobs: ${selfhost_jobs})"

native_cache_dir="${output_dir}/native_cache"
native_cache_stamp="${native_cache_dir}/bootstrap-wide-inputs.sha256"
native_cache_freshened=0

bootstrap_wide_inputs_hash() {
  {
    # Module fingerprints cover source edits, but unchanged modules must also
    # be rebuilt when the compiler/runtime that emits their objects changes.
    printf 'platform=%s backend=%s mode=%s stub_fallback=forbidden\n' "${PLATFORM}" "${backend}" "${bootstrap_mode}"
    printf 'seed-inputs=%s\n' "${seed_inputs_fingerprint:-missing}"
    find src/compiler -name '*.spl' -type f -print 2>/dev/null \
      | LC_ALL=C sort | hash_path_list
    env | LC_ALL=C sort | awk '/^SIMPLE_.*(AOP|MDSOC|WEAV|LOAD|INTERPRET|EXECUTION|LIB|NATIVE_BUILD)/ { print }'
  } | hash_stream
}

# Prune native-build cache scope directories older than a TTL.
#
# Scope dirs are named
# `backend=...;cpu=...;opt=...;compiler=<sha>+src<fingerprint>n<count>` and are
# mint-once: as soon as any input in the closure changes, the source
# fingerprint changes and a NEW scope dir is minted. The old one is never
# consulted again, and nothing else ever collects it. That was harmless only
# while the wrappers wiped the entire cache dir on every run; now that these
# caches persist across runs (so an unchanged tree gets a real cache hit) the
# wipe is gone and scope dirs would otherwise accumulate without bound.
#
# Age-based rather than LRU on purpose: it needs no bookkeeping sidecar and no
# lock protocol. Several bootstrap lanes build concurrently on this host, and a
# scope dir whose mtime is older than the TTL cannot belong to a live build, so
# this can never pull artifacts out from under a running lane. Only entries
# matching the `backend=*` scope-dir shape are ever removed, so sibling files
# (build_cache.sdn, *.smf) are untouched. Override the window with
# BOOTSTRAP_NATIVE_CACHE_TTL_DAYS; 0 or a non-numeric value disables pruning.
bootstrap_native_cache_prune() {
  bnc_dir=$1
  bnc_ttl=${BOOTSTRAP_NATIVE_CACHE_TTL_DAYS:-7}
  [ -d "${bnc_dir}" ] || return 0
  case "${bnc_ttl}" in
    ''|*[!0-9]*) return 0 ;;
  esac
  [ "${bnc_ttl}" -gt 0 ] || return 0
  bnc_n=$(find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -print 2>/dev/null | wc -l)
  [ "${bnc_n}" -gt 0 ] || return 0
  find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -exec rm -rf {} + 2>/dev/null || true
  echo "  native cache: pruned ${bnc_n} scope dir(s) older than ${bnc_ttl}d in ${bnc_dir}"
}

# Per-lane private cache. Each stage gets build/bootstrap/native_cache/<lane>/
# instead of every stage sharing one native_cache, so a phase-2 entry can never be
# picked up by a phase-3 lane running a different compiler over the same source.
# Guarded fail-closed by scripts/check/check-cache-scope-ownership.shs.
# Design: doc/05_design/compiler/incremental_build/per_lane_private_caches.md
native_cache_base_dir="${native_cache_dir}"
bootstrap_cache_scope_guard="${repo_root:-.}/scripts/check/check-cache-scope-ownership.shs"
# Cache-clearing helpers. Sourced (not exec'd) so prepare_native_cache can call
# native_cache_clear_context_change, which keeps the content-keyed frontend
# parse cache across a build-context change.

bootstrap_select_cache_lane() {
  bscl_label=$1
  bscl_lane=$(printf '%s' "${bscl_label}" | tr -c 'A-Za-z0-9._-' '_')
  [ -n "${bscl_lane}" ] || bscl_lane=default
  native_cache_dir="${native_cache_base_dir}/${bscl_lane}"
  native_cache_stamp="${native_cache_dir}/bootstrap-wide-inputs.sha256"
  # Propagate to the compilers themselves (both engines read SIMPLE_CACHE_SCOPE).
  SIMPLE_CACHE_SCOPE="${bscl_lane}"
  export SIMPLE_CACHE_SCOPE
  mkdir -p "${native_cache_dir}"
  # Old checkouts may not have the guard yet; stay additive rather than fatal.
  if [ -f "${bootstrap_cache_scope_guard}" ]; then
    if ! sh "${bootstrap_cache_scope_guard}" "${native_cache_dir}" "${bscl_lane}"; then
      echo "  ${bscl_label}: refusing to build against a foreign cache scope" >&2
      exit 1
    fi
  fi
}

prepare_native_cache() {
  label=$1
  bootstrap_select_cache_lane "${label}"
  if [ "${execution_profile}" = "clean-release" ]; then
    echo "  ${label}: clearing native cache (clean-release profile)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    return
  fi
  if bootstrap_cache_force_clear_one_binary \
    "${execution_profile}" "${bootstrap_mode}"; then
    echo "  ${label}: clearing native cache (one-binary mode)"
    rm -rf "${native_cache_dir}/"
    return
  fi

  mkdir -p "${native_cache_dir}"
  current_hash=$(bootstrap_wide_inputs_hash)
  if [ "${fresh_cache}" -eq 1 ] && [ "${native_cache_freshened}" -eq 0 ]; then
    echo "  ${label}: clearing native cache (--fresh-cache)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
    native_cache_freshened=1
    return
  fi
  if [ ! -f "${native_cache_stamp}" ] || [ "$(cat "${native_cache_stamp}" 2>/dev/null)" != "${current_hash}" ]; then
    # Keep `frontend/`: the parse cache is keyed by source-content sha256 plus a
    # header folding the full scope key (compiler exe hash + src/compiler/**
    # fingerprint + backend/cpu/opt/lane), so every axis this stamp guards is
    # already inside the entry and a mismatch fails closed to a reparse. Wiping
    # it too is what made a retried build reparse the whole closure from cold.
    # See the folded native-cache-clear library above.
    echo "  ${label}: clearing native cache (platform/backend/AOP build context changed; frontend parse cache preserved)"
    native_cache_clear_context_change "${native_cache_dir}" || true
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
  else
    echo "  ${label}: reusing native cache (${bootstrap_mode} mode)"
  fi
  bootstrap_native_cache_prune "${native_cache_dir}"
  bootstrap_stamp_cache_lane
}

# Re-stamp the ownership marker: every clear path above `rm -rf`s the dir, which
# removes it. An unmarked dir is claimable, so this is belt-and-braces, but it
# keeps the marker present for out-of-band inspection.
bootstrap_stamp_cache_lane() {
  [ -n "${native_cache_dir:-}" ] || return 0
  mkdir -p "${native_cache_dir}" 2>/dev/null || return 0
  printf 'lane=%s\n' "${SIMPLE_CACHE_SCOPE:-default}" \
    > "${native_cache_dir}/.cache_scope" 2>/dev/null || true
}

run_logged() {
  label=$1
  shift
  log_file="${log_dir}/${label}.log"
  {
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] ${label}"
    echo "cwd: $(pwd)"
    echo "command: $*"
    echo ""
  } >"${log_file}"

  set +e
  "$@" >>"${log_file}" 2>&1
  status=$?
  set -e

  echo "  ${label} log: ${log_file}"
  if [ "${status}" -ne 0 ]; then
    echo "error: ${label} failed with exit ${status}" >&2
    if [ "${status}" -ge 128 ]; then
      signal=$((${status} - 128))
      echo "error: ${label} terminated by signal ${signal}" >&2
    fi
    echo "error: see log ${log_file}" >&2
    exit "${status}"
  fi
}

CANDIDATE_FRONTEND_ROOT=${repo_root}
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "${repo_root}/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"

bootstrap_stage_sanity() (
  candidate=$1
  evidence_path=${2:-}
  sanity_home=$3
  sanity_tmpdir=$4
  sanity_path=$5
  # Captured BEFORE the environment scrub below, which unsets everything.
  sanity_repo_root=${repo_root}
  for sanity_env_name in $(env | sed 's/=.*//'); do
    case "${sanity_env_name}" in
      ''|[0-9]*|*[!A-Za-z0-9_]*) continue ;;
    esac
    unset "${sanity_env_name}"
  done
  HOME=${sanity_home}
  TMPDIR=${sanity_tmpdir}
  PATH=${sanity_path}
  LC_ALL=C
  LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="${evidence_path:-${TMPDIR:-/tmp}/bootstrap-sanity}.tmp.$$"
  frontend_log="${evidence_tmp}.frontend"
  rm -f "${evidence_tmp}" "${frontend_log}"
  candidate_sha_before=$(bootstrap_stage3_hash_file "${candidate}") || return 1
  # Expected version is DERIVED, never hardcoded. The literal
  # "simple-bootstrap 1.0.0-beta" used to live here; release commit 9a3f6051996
  # bumped src/app/cli/bootstrap_identity.spl (and ./VERSION) to 1.0.0-RC and did
  # not update this file, making the gate unsatisfiable by ANY correctly-built
  # Stage-2 binary. The failure was invisible because the version comparison had
  # no *_status field in the evidence -- every recorded field read as passing.
  # Fail-closed: an unreadable/empty VERSION, or a VERSION that disagrees with
  # bootstrap_identity.spl, is an ERROR (sanity_status=error), never a pass.
  version_expect_status=0
  version_expected=
  if [ -r "${sanity_repo_root}/VERSION" ]; then
    version_expected=$(sed -n '1s/[[:space:]]*$//p' "${sanity_repo_root}/VERSION")
  fi
  if [ -z "${version_expected}" ]; then
    version_expect_status=1
  else
    # Cross-check the compiled-in source of truth against ./VERSION. Drift
    # between these two is the exact defect this gate failed to survive.
    version_identity=$(sed -n 's/^[[:space:]]*"\(.*\)"[[:space:]]*$/\1/p' \
      "${sanity_repo_root}/src/app/cli/bootstrap_identity.spl" | sed -n '1p')
    if [ -z "${version_identity}" ] ||
      [ "${version_identity}" != "${version_expected}" ]; then
      version_expect_status=2
    fi
  fi
  version_status=0
  version=$(run_timeout 10 "${candidate}" --version 2>&1) ||
    version_status=$?
  version_match_status=1
  if [ "${version_expect_status}" -eq 0 ] &&
    [ "${version}" = "simple-bootstrap ${version_expected}" ]; then
    version_match_status=0
  fi
  unsupported_status=0
  if unsupported=$(run_timeout 10 "${candidate}" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1); then
    unsupported_status=0
  else
    unsupported_status=$?
  fi
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND="${backend}" \
    CANDIDATE_FRONTEND_BOOTSTRAP=0 \
    candidate_frontend_smoke "${candidate}" >"${frontend_log}" 2>&1 ||
    frontend_status=$?
  # Second pass under SIMPLE_BOOTSTRAP=1 -- the EXACT configuration Stage 3
  # invokes this candidate in. The single-pass (SIMPLE_BOOTSTRAP=0) gate
  # certified a configuration Stage 3 never uses, and on 2026-08-09 it admitted
  # a Stage-2 binary that could not lex a two-line file, whose failure then ran
  # unbounded (444 MB log / 32 GB RSS). See doc/08_tracking/bug/
  # stage2_binary_lexer_reads_every_source_as_empty_infinite_parser_loop_2026-08-09.md
  frontend_bootstrap_status=0
  if [ "${frontend_status}" -eq 0 ]; then
    CANDIDATE_FRONTEND_BACKEND="${backend}" \
      CANDIDATE_FRONTEND_BOOTSTRAP=1 \
      candidate_frontend_smoke "${candidate}" >>"${frontend_log}" 2>&1 ||
      frontend_bootstrap_status=$?
    frontend_status=${frontend_bootstrap_status}
  fi
  candidate_sha_after=$(bootstrap_stage3_hash_file "${candidate}") || return 1
  # The `run` sub-check is a NEGATIVE CONTROL, not a capability probe: the
  # Stage-2 candidate is built from src/app/cli/bootstrap_main.spl, which
  # deliberately implements only native-build/compile/--version/--help. Asserting
  # that `run` is rejected with rc 1 and the exact diagnostic proves the
  # candidate reached its own argv dispatch -- i.e. it is the bootstrap entry we
  # asked for and not some other binary. Do not "fix" it into a `run` that works.
  unsupported_match_status=1
  if [ "${unsupported_status}" -eq 1 ]; then
    case "${unsupported}" in
      *"unknown command 'run'"*) unsupported_match_status=0 ;;
    esac
  fi
  sha_stable_status=1
  if [ "${candidate_sha_before}" = "${candidate_sha_after}" ]; then
    sha_stable_status=0
  fi
  # Non-vacuity: count the sub-checks actually evaluated. A run that evaluated
  # none is ERROR, never a pass.
  sanity_checks_run=5
  if [ "${version_expect_status}" -ne 0 ]; then
    sanity_status=error
    sanity_checks_run=0
  elif [ "${version_status}" -eq 0 ] &&
    [ "${version_match_status}" -eq 0 ] &&
    [ "${unsupported_match_status}" -eq 0 ] &&
    [ "${frontend_status}" -eq 0 ] &&
    [ "${sha_stable_status}" -eq 0 ]; then
    sanity_status=pass
  else
    sanity_status=fail
  fi
  # Name the failing sub-check. The old gate exited 2 with no diagnostic text at
  # all, which is why a stale version literal cost a full 30-minute bootstrap to
  # even localise.
  if [ "${sanity_status}" != pass ]; then
    case "${version_expect_status}" in
      1) echo "error: sanity ERROR - cannot read ${sanity_repo_root}/VERSION" >&2 ;;
      2) echo "error: sanity ERROR - ./VERSION ('${version_expected}') disagrees with src/app/cli/bootstrap_identity.spl ('${version_identity}')" >&2 ;;
    esac
    [ "${version_status}" -eq 0 ] ||
      echo "error: sanity FAIL - --version exited ${version_status}" >&2
    { [ "${version_expect_status}" -ne 0 ] || [ "${version_match_status}" -eq 0 ]; } ||
      echo "error: sanity FAIL - version mismatch: got '${version}', want 'simple-bootstrap ${version_expected}'" >&2
    [ "${unsupported_match_status}" -eq 0 ] ||
      echo "error: sanity FAIL - 'run' negative control: rc ${unsupported_status}, output '${unsupported}'" >&2
    [ "${frontend_status}" -eq 0 ] ||
      echo "error: sanity FAIL - frontend smoke exited ${frontend_status} (bootstrap-mode pass: ${frontend_bootstrap_status})" >&2
    [ "${sha_stable_status}" -eq 0 ] ||
      echo "error: sanity FAIL - candidate binary mutated during sanity" >&2
  fi
  if [ -n "${evidence_path}" ]; then
    {
      echo "schema=simple-bootstrap-sanity-evidence-v1"
      echo "status=${sanity_status}"
      echo "candidate_sha256_before=${candidate_sha_before}"
      echo "version_status=${version_status}"
      echo "version_output=${version}"
      echo "version_expected=${version_expected}"
      echo "version_expect_status=${version_expect_status}"
      echo "version_match_status=${version_match_status}"
      echo "unsupported_status=${unsupported_status}"
      printf 'unsupported_output_sha256=%s\n' \
        "$(printf '%s' "${unsupported}" | bootstrap_stage3_hash_stream)"
      echo "frontend_smoke_status=${frontend_status}"
      echo "unsupported_match_status=${unsupported_match_status}"
      echo "frontend_smoke_bootstrap_mode_status=${frontend_bootstrap_status}"
      echo "frontend_smoke_output_sha256=$(bootstrap_stage3_hash_file "${frontend_log}")"
      echo "candidate_sha256_after=${candidate_sha_after}"
      echo "sha_stable_status=${sha_stable_status}"
      echo "checks_run=${sanity_checks_run}"
    } >"${evidence_tmp}" || return 1
    mv "${evidence_tmp}" "${evidence_path}"
  fi
  if [ "${sanity_status}" != pass ]; then
    echo "bootstrap-sanity-error: version_status=${version_status} version_output=${version} unsupported_status=${unsupported_status} frontend_status=${frontend_status} candidate_unchanged=$([ "${candidate_sha_before}" = "${candidate_sha_after}" ] && echo true || echo false)" >&2
  fi
  rm -f "${frontend_log}"
  [ "${sanity_status}" = pass ]
)

bootstrap_native_build_main() {
  compiler=$1
  output=$2
  set -- native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
    --entry-closure \
    --low-memory
  set -- "$@" \
    --threads "${selfhost_jobs}" \
    --cache-dir "${native_cache_dir}" \
    --mode one-binary \
    --entry src/app/cli/main.spl \
    --runtime-path "${bootstrap_runtime_authority_path}" \
    -o "${output}"
  env RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_BOOTSTRAP_STAGE4=1 \
    SIMPLE_BOOTSTRAP_LOW_MEMORY=1 \
    SIMPLE_STAGE4_STREAMING_SURFACES=1 \
    SIMPLE_NATIVE_ARENA_DECLS=1 \
    SIMPLE_COMPILER_PHASE_PROFILE="${SIMPLE_COMPILER_PHASE_PROFILE:-1}" \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_NATIVE_BUILD_TARGET="${PLATFORM}" \
    SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}" \
    SIMPLE_NATIVE_BUILD_CACHE_DIR="${native_cache_dir}" \
    SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BINARY="$(absolute_path "${compiler}")" \
    "${compiler}" "$@"
}

# ===========================================================================
# Bootstrap pipeline
# ===========================================================================

seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
native_all_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_native_all${archive_suffix}"
compiler_backfill_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}"
rust_authority_lock_root="${repo_root}/src/compiler_rust/target/.bootstrap-authority-locks"
rust_authority_generation_root="${repo_root}/src/compiler_rust/target/bootstrap.generations"
rust_authority_current_marker="${repo_root}/src/compiler_rust/target/bootstrap.current.env"
rust_authority_compatibility_path="${repo_root}/src/compiler_rust/target/bootstrap"

bootstrap_acquire_rust_authority() {
  [ -z "${rust_target_lock_handle}" ] || return 0
  portable_lock_acquire "${rust_authority_lock_root}" authority \
    "${SIMPLE_BOOTSTRAP_AUTHORITY_LOCK_WAIT_SECONDS:-120}" || {
    echo "error: timed out waiting for shared Rust authority publication" >&2
    return 1
  }
  rust_target_lock_handle=${PORTABLE_LOCK_HANDLE}
}

bootstrap_release_rust_authority() {
  [ -n "${rust_target_lock_handle}" ] || return 0
  portable_lock_release "${rust_target_lock_handle}" || return 1
  rust_target_lock_handle=
}

if [ "${diagnostic_sweep}" -eq 1 ]; then
  if [ "${deploy}" -eq 1 ] || [ "${release_tests}" -eq 1 ] || [ "${full_cli}" -eq 1 ]; then
    echo "error: --diagnostic-sweep is check-only and cannot deploy, release, or relink" >&2
    exit 1
  fi
  if [ ! -x "${seed_bin}" ]; then
    echo "error: diagnostic sweep requires an existing compiler: ${seed_bin}" >&2
    exit 1
  fi
  # Parser and semantic globals cannot safely recover from an arbitrary broken
  # module in-process. Independent compiler processes are therefore the owner
  # boundary; stable per-file cache directories isolate concurrent writers.
  # This mode has no output-artifact or deployment path.
  # shellcheck disable=SC2086
  if sh scripts/check/bootstrap-diagnostic-sweep.shs \
    --compiler="${seed_bin}" --child-compiler="${diagnostic_child_compiler}" \
    --cache-dir="${output_dir}/diagnostic-cache" \
    --evidence-dir="${output_dir}/diagnostic-evidence" \
    --jobs="${jobs}" ${diagnostic_roots}; then
    exit 0
  else
    diagnostic_status=$?
    exit "${diagnostic_status}"
  fi
fi

# Detect stale seed OR stale runtime library by CONTENT, not mtime.
#
# The previous check used `find -newer` (mtime). jj/git operations (reconcile,
# checkout, working-copy snapshots) routinely bump .rs mtimes WITHOUT changing
# content, which made every bootstrap spuriously recompile ~11 Rust crates
# (~5 min of pure waste; measured 2026-06-14: 286s, 0 content changes).
#
# seed_inputs_hash fingerprints everything that determines the seed binary +
# runtime library: all Rust sources, every Cargo.toml, Cargo.lock, the build
# profile/backend/features, and the rustc version. A stamp file beside the seed
# records the fingerprint of the inputs the current seed was built from; we
# rebuild only when the fingerprint differs (or is missing) — never on mtime
# churn. Any doubt (missing stamp, hash failure → empty mismatch) rebuilds: a
# stale seed would silently miscompile, which is worse than a slow build.
seed_stamp="${seed_bin}.inputs.sha256"
seed_fingerprint_tmp="${output_dir}/rust-authority-fingerprint-tmp"
seed_fingerprint_error_manifest=\
"${output_dir}/rust-authority-fingerprint-error.manifest"
seed_fingerprint_error=\
"${output_dir}/rust-authority-fingerprint-error.log"
seed_inputs_hash() {
  seed_fingerprint_phase=$1
  bootstrap_authority_seed_inputs_fingerprint \
    "${seed_fingerprint_phase}" "${seed_fingerprint_tmp}" \
    "${seed_fingerprint_error_manifest}" "${seed_fingerprint_error}" \
    "${repo_root}" \
    "${backend}" "${llvm_features}" "${PATH}" "${PLATFORM}"
}
seed_stale=0
rust_rebuilt=0
compiler_backfill_rebuilt=0
if [ -e "${rust_authority_current_marker}.transaction" ]; then
  bootstrap_acquire_rust_authority || exit 1
  bootstrap_authority_recover_or_refuse "${full_bootstrap}" \
    "${rust_authority_generation_root}" "${rust_authority_current_marker}" \
    "${rust_authority_compatibility_path}" \
    "${rust_target_lock_handle}" || {
    if [ "${full_bootstrap}" -eq 0 ]; then
      echo "error: Rust authority publication is incomplete; run --full-bootstrap to recover" >&2
    else
      echo "error: full bootstrap could not recover Rust authority publication" >&2
    fi
    exit 1
  }
  bootstrap_release_rust_authority || exit 1
fi
# (content-hash staleness gate runs below, after backend/llvm_features settle)

# Detect LLVM 18 availability for LLVM backends.
llvm_features=""
if [ "${backend}" = "llvm-lib" ] || [ "${backend}" = "llvm" ]; then
  # LLVM is resolved once by the shared platform interface
  # (scripts/setup/platform-detect.shs, sourced above), which also exports the
  # LLVM_SYS_<major>0_PREFIX used by the Rust build and the runtime's LLVM path.
  if [ "${LLVM_FOUND:-0}" = "1" ]; then
    echo "LLVM ${LLVM_VERSION} found: ${LLVM_PREFIX} (lib: ${LLVM_LIB})"
    llvm_features="--features llvm"
    # macOS needs LIBRARY_PATH for zstd and other Homebrew libs
    if [ "${host_os}" = "Darwin" ]; then
      brew_prefix="$(brew --prefix 2>/dev/null || true)"
      if [ -n "${brew_prefix}" ]; then
        export HOMEBREW_PREFIX="${brew_prefix}"
        export LIBRARY_PATH="${LIBRARY_PATH:+${LIBRARY_PATH}:}${brew_prefix}/lib"
      fi
      export SDKROOT="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null || true)}"
    fi
  else
    echo "error: LLVM not found (shared platform detection: scripts/setup/platform-detect.shs, versions: ${LLVM_VERSIONS:-18})" >&2
    echo "error: install LLVM or select --backend=cranelift explicitly" >&2
    exit 1
  fi
fi

# Content-hash staleness gate (see seed_inputs_hash above). Runs here so the
# backend/features are final before they enter the fingerprint. If the seed or
# runtime library is missing, the cargo branch below rebuilds regardless.
seed_inputs_fingerprint=not-used-by-admitted-stage4-resume
if [ -z "${resume_stage4_output}" ]; then
  bootstrap_progress_mark fingerprint ""
  seed_inputs_fingerprint=$(seed_inputs_hash pre) || {
    echo "error: failed to fingerprint Rust seed inputs" >&2
    exit 1
  }
fi
if [ -z "${resume_stage4_output}" ] && [ -x "${seed_bin}" ] && [ -f "${native_all_lib}" ]; then
  if ! bootstrap_stage3_verify_seed_stamp "${seed_stamp}" \
    "${seed_inputs_fingerprint}" "${seed_bin}" "${native_all_lib}" \
    "${compiler_backfill_lib}"; then
    seed_stale=1
    if [ "${full_bootstrap}" -eq 1 ]; then
      echo "Seed/runtime stale (Rust source content changed since last build). Full bootstrap will rebuild Rust."
    else
      echo "WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed."
    fi
  else
    echo "Seed/runtime current (input content hash matches); skipping Rust rebuild."
  fi
fi

if [ "${full_bootstrap}" -eq 1 ]; then
  rust_authority_root="${output_dir}/rust-authority-${seed_inputs_fingerprint}"
  rust_authority_target="${rust_authority_root}/target"
  rust_authority_profile_dir="${rust_authority_target}/${PLATFORM}/bootstrap"
  rust_authority_home="${rust_authority_root}/home"
  rust_authority_cargo_home="${rust_authority_root}/cargo-home"
  rust_authority_tmp="${rust_authority_root}/tmp"
  rust_toolchain_authority=$(
    bootstrap_stage3_resolve_rust_toolchain "${repo_root}" "${PATH}"
  ) || {
    echo "error: could not resolve canonical Rust toolchain" >&2
    exit 1
  }
  rust_sysroot=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^rust-sysroot=//p'
  )
  rustc_abs=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^rustc-path=//p'
  )
  cargo_abs=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^cargo-path=//p'
  )
  [ -x "${rustc_abs}" ] && [ -x "${cargo_abs}" ] || {
    echo "error: Rust toolchain binaries missing under sysroot: ${rust_sysroot}" >&2
    exit 1
  }
  mingw_linker="${CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER:-gcc}"
  mingw_cc="${CC_x86_64_pc_windows_gnu:-gcc}"
  mingw_ar="${AR_x86_64_pc_windows_gnu:-ar}"
  cc_abs=$(bootstrap_stage3_target_c_compiler "${PLATFORM}") || {
    echo "error: no C compiler found for Rust authority target ${PLATFORM}" >&2
    exit 1
  }
  windows_include="${INCLUDE:-}"
  windows_lib="${LIB:-}"
  windows_libpath="${LIBPATH:-}"
  # MSYS / Git Bash exports the Windows names in UPPER CASE (SYSTEMROOT,
  # SYSTEMDRIVE, PROGRAMDATA); the mixed-case spellings a native cmd shell has
  # are absent, so reading only those captured EMPTY and the hermetic `env -i`
  # below handed the toolchain a Windows-less environment.
  windows_system_root="${SystemRoot:-${SYSTEMROOT:-${WINDIR:-${windir:-}}}}"
  # SystemDrive is REQUIRED for the MSVC lane. Without it every drive-rooted
  # LIB entry fails to resolve and link.exe reports `LNK1181: cannot open
  # input file 'kernel32.lib'` even though LIB is correct and the file exists
  # (bisected 2026-08-24: adding SystemDrive alone flips the identical rustc
  # invocation from exit 1 to exit 0). ProgramData is forwarded for the same
  # class of drive-rooted resolution.
  windows_system_drive="${SystemDrive:-${SYSTEMDRIVE:-}}"
  windows_program_data="${ProgramData:-${PROGRAMDATA:-}}"
  windows_temp="${TEMP:-${rust_authority_tmp}}"
  rust_llvm_authority=$(
    bootstrap_stage3_resolve_llvm_build_authority \
      "${PATH}" "${llvm_features}"
  ) || {
    echo "error: could not resolve deterministic LLVM build authority" >&2
    exit 1
  }
  rust_llvm_status=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-build-status=//p'
  )
  rust_llvm_major=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-major=//p'
  )
  rust_llvm_prefix=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-prefix=//p'
  )
  rust_llvm_sdkroot=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-sdkroot=//p'
  )
  rust_llvm_homebrew_prefix=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-homebrew-prefix=//p'
  )
  rust_llvm_library_path=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-library-path=//p'
  )
fi

rust_authority_workspace_prepared=0
prepare_rust_authority_workspace() {
  if [ "${rust_authority_workspace_prepared}" -eq 1 ]; then
    return 0
  fi

  rm -rf "${rust_authority_root}"
  mkdir -p "${rust_authority_target}" "${rust_authority_home}" \
    "${rust_authority_cargo_home}" "${rust_authority_tmp}"
  vendored_sources_absolute=$(
    CDPATH= cd -- "${repo_root}/src/compiler_rust/vendor" && pwd -P
  )
  if [ "${os}" = "windows" ]; then
    vendored_sources_absolute=$(cygpath -m "${vendored_sources_absolute}") || {
      echo "error: could not convert vendored Cargo source path for Windows" >&2
      exit 1
    }
  fi
  cargo_authority_config="${rust_authority_cargo_home}/config.toml"
  awk -v vendored_sources="${vendored_sources_absolute}" '
    {
      config_line = $0
      sub(/\r$/, "", config_line)
    }
    config_line == "directory = \"vendor\"" {
      print "directory = \"" vendored_sources "\""
      replaced += 1
      next
    }
    { print }
    END { if (replaced != 1) exit 1 }
  ' "${repo_root}/src/compiler_rust/.cargo/config.toml" \
    >"${cargo_authority_config}" || {
    echo "error: could not create private offline Cargo configuration" >&2
    exit 1
  }
  rust_authority_workspace_prepared=1
}

run_rust_authority_cargo() {
  rust_authority_log=$1
  rust_authority_lto=$2
  shift 2
  if [ -n "${progress_log}" ]; then
    bootstrap_progress_mark "rust-${rust_authority_log}" \
      "$(absolute_path "${log_dir}/${rust_authority_log}.log")"
  fi
  if [ "${os}" = "windows" ]; then
    set -- "$@" --target "${PLATFORM}"
  fi
  prepare_rust_authority_workspace
  if [ "${rust_llvm_status:-disabled}" = enabled ]; then
    if [ "${rust_authority_lto}" = off ]; then
      run_logged "${rust_authority_log}" env -i \
        HOME="$(absolute_path "${rust_authority_home}")" \
        CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
        CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
        TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
        RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
        CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
        CC_x86_64_pc_windows_gnu="${mingw_cc}" \
        AR_x86_64_pc_windows_gnu="${mingw_ar}" \
        INCLUDE="${windows_include}" LIB="${windows_lib}" \
        LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
        SystemDrive="${windows_system_drive}" \
        ProgramData="${windows_program_data}" \
        TEMP="${windows_temp}" \
        "LLVM_SYS_${rust_llvm_major}0_PREFIX=${rust_llvm_prefix}" \
        "HOMEBREW_PREFIX=${rust_llvm_homebrew_prefix}" \
        "LIBRARY_PATH=${rust_llvm_library_path}" \
        "SDKROOT=${rust_llvm_sdkroot}" CARGO_PROFILE_BOOTSTRAP_LTO=off \
        "${cargo_abs}" "$@"
    else
      run_logged "${rust_authority_log}" env -i \
        HOME="$(absolute_path "${rust_authority_home}")" \
        CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
        CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
        TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
        RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
        CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
        CC_x86_64_pc_windows_gnu="${mingw_cc}" \
        AR_x86_64_pc_windows_gnu="${mingw_ar}" \
        INCLUDE="${windows_include}" LIB="${windows_lib}" \
        LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
        SystemDrive="${windows_system_drive}" \
        ProgramData="${windows_program_data}" \
        TEMP="${windows_temp}" \
        "LLVM_SYS_${rust_llvm_major}0_PREFIX=${rust_llvm_prefix}" \
        "HOMEBREW_PREFIX=${rust_llvm_homebrew_prefix}" \
        "LIBRARY_PATH=${rust_llvm_library_path}" \
        "SDKROOT=${rust_llvm_sdkroot}" \
        "${cargo_abs}" "$@"
    fi
  elif [ "${rust_authority_lto}" = off ]; then
    run_logged "${rust_authority_log}" env -i \
      HOME="$(absolute_path "${rust_authority_home}")" \
      CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
      CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
      TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
      RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
      CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
      CC_x86_64_pc_windows_gnu="${mingw_cc}" \
      AR_x86_64_pc_windows_gnu="${mingw_ar}" \
      INCLUDE="${windows_include}" LIB="${windows_lib}" \
      LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
      SystemDrive="${windows_system_drive}" \
      ProgramData="${windows_program_data}" \
      TEMP="${windows_temp}" \
      CARGO_PROFILE_BOOTSTRAP_LTO=off "${cargo_abs}" "$@"
  else
    run_logged "${rust_authority_log}" env -i \
      HOME="$(absolute_path "${rust_authority_home}")" \
      CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
      CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
      TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
      RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
      CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
      CC_x86_64_pc_windows_gnu="${mingw_cc}" \
      AR_x86_64_pc_windows_gnu="${mingw_ar}" \
      INCLUDE="${windows_include}" LIB="${windows_lib}" \
      LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
      SystemDrive="${windows_system_drive}" \
      ProgramData="${windows_program_data}" \
      TEMP="${windows_temp}" \
      "${cargo_abs}" "$@"
  fi
}

if [ "${full_bootstrap}" -eq 0 ] && [ -z "${resume_stage4_output}" ]; then
  # Default/pure-Simple rebuild: reuse the existing Rust seed and runtime
  # library, never invoke cargo. Whether the existing seed CAN build the changed
  # pure-Simple is proven by Stage 2 below: if the new .spl needs a Rust feature
  # the seed lacks, Stage 2 fails — rerun with --full-bootstrap.
  if [ ! -x "${seed_bin}" ] || [ ! -f "${native_all_lib}" ]; then
    echo "error: bootstrap needs an existing Rust seed and runtime library:" >&2
    echo "  seed:    ${seed_bin}" >&2
    echo "  runtime: ${native_all_lib}" >&2
    echo "Normal bootstrap does not rebuild Rust. Re-run with --full-bootstrap to build them." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ ! -f "${compiler_backfill_lib}" ]; then
    echo "error: full CLI bootstrap needs the compiler backfill archive: ${compiler_backfill_lib}" >&2
    echo "Re-run with --full-bootstrap to build it." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ "${seed_stale}" -eq 1 ]; then
    echo "error: full CLI bootstrap refuses a stale compiler backfill; re-run with --full-bootstrap" >&2
    exit 1
  fi
  if [ "${seed_stale}" -eq 1 ]; then
    echo "WARNING: Rust sources changed; reusing the existing seed because --full-bootstrap was not given."
  fi
  echo "Pure-Simple mode: ${bootstrap_mode}; reusing Rust seed, rebuilding only pure-Simple stages."
elif [ "${full_bootstrap}" -eq 1 ] && bootstrap_stage3_rust_tuple_requires_complete_rebuild \
  "${seed_bin}" "${native_all_lib}" "${compiler_backfill_lib}" \
  "${seed_stale}"; then
  echo "Building Rust seed compiler + runtime library..."
  # Split into two cargo invocations to defeat feature unification:
  # `simple-native-all` enables `driver-hooks` on `simple-runtime`, which gates
  # out the `not(driver-hooks)` `#[no_mangle]` def of rt_cli_run_file. Building
  # both packages in a single `cargo build -p A -p B` call unifies features,
  # leaving the `simple-driver` bin with an undefined `rt_cli_run_file` symbol
  # (the C symbol is provided by `simple-native-all`, which the seed bin does
  # not link). Separate invocations keep simple-runtime's feature set per-bin.
  run_rust_authority_cargo rust-seed-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-driver ${llvm_features}
  run_rust_authority_cargo rust-native-all-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-native-all ${llvm_features}
  # Rebuild simple-runtime LAST with LTO off so deps/libsimple_runtime.a holds
  # machine-code symbol definitions. Under the bootstrap profile's thin-LTO the
  # rlib members export symbols only inside embedded `__bitcode` sections, which
  # the stage4 `-r` capsule link cannot LTO-compile — every runtime root then
  # audits as "0 definitions". The last cargo invocation wins the deps/ archive
  # slot, so this must stay after the driver and native-all builds.
  run_rust_authority_cargo rust-runtime-nolto-build off \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-runtime --features runtime-symbol-table
  rust_rebuilt=1
fi

if [ "${full_bootstrap}" -eq 1 ] \
   && { [ ! -f "${compiler_backfill_lib}" ] || [ "${seed_stale}" -eq 1 ] || [ "${rust_rebuilt}" -eq 1 ]; }; then
  run_rust_authority_cargo rust-compiler-backfill-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-compiler-backfill
  compiler_backfill_rebuilt=1
fi
if [ "${rust_rebuilt}" -eq 1 ] || [ "${compiler_backfill_rebuilt}" -eq 1 ]; then
  seed_inputs_fingerprint_after=$(seed_inputs_hash post) || {
    echo "error: failed to re-fingerprint Rust seed inputs after Cargo" >&2
    exit 1
  }
  if [ "${seed_inputs_fingerprint_after}" != "${seed_inputs_fingerprint}" ]; then
    echo "error: Rust inputs changed during full bootstrap; refusing to publish a stale seed" >&2
    exit 1
  fi
  seed_inputs_fingerprint="${seed_inputs_fingerprint_after}"
  rust_generation_nonce=$(od -An -N16 -tx1 /dev/urandom 2>/dev/null | tr -d ' \n')
  case "${rust_generation_nonce}" in
    [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]) ;;
    *) echo "error: could not generate Rust authority nonce" >&2; exit 1 ;;
  esac
  bootstrap_stage3_prepare_seed_generation \
    "${rust_authority_profile_dir}" "${rust_authority_generation_root}" \
    "${seed_inputs_fingerprint}" "simple${exe_suffix}" \
    "${archive_prefix}simple_native_all${archive_suffix}" \
    "${archive_prefix}simple_compiler_backfill${archive_suffix}" \
    "${rust_generation_nonce}" || {
    echo "error: could not prepare immutable Rust authority generation" >&2
    exit 1
  }
  bootstrap_acquire_rust_authority || exit 1
  seed_inputs_fingerprint_commit=$(seed_inputs_hash commit) || {
    echo "error: failed to fingerprint Rust inputs before authority commit" >&2
    exit 1
  }
  [ "${seed_inputs_fingerprint_commit}" = "${seed_inputs_fingerprint}" ] || {
    echo "error: Rust inputs changed while waiting to publish authority" >&2
    exit 1
  }
  bootstrap_stage3_publish_seed_generation \
    "${BOOTSTRAP_STAGE3_PREPARED_STAGING}" \
    "${BOOTSTRAP_STAGE3_PREPARED_GENERATION}" \
    "${rust_authority_current_marker}" "${seed_inputs_fingerprint}" \
    "${BOOTSTRAP_STAGE3_PREPARED_HASH}" \
    "${seed_inputs_fingerprint_commit}" \
    "${rust_authority_compatibility_path}" || {
    echo "error: could not commit immutable Rust authority generation" >&2
    exit 1
  }
  bootstrap_stage3_resolve_committed_seed \
    "${rust_authority_generation_root}" \
    "${rust_authority_current_marker}" || {
    echo "error: committed Rust authority generation failed verification" >&2
    exit 1
  }
  seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
  native_all_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_native_all${archive_suffix}"
  compiler_backfill_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}"
  seed_stamp="${seed_bin}.inputs.sha256"
fi

# Force manual bootstrap — ensures SIMPLE_RUNTIME_PATH is used for linking
# The full CLI `build bootstrap` command doesn't forward the runtime path
can_full_bootstrap=0

export SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}"
export SIMPLE_BOOTSTRAP=1
echo "Running bootstrap pipeline..."
echo "  runtime:  ${SIMPLE_RUNTIME_PATH}"
echo "  platform: ${PLATFORM}"
echo "  backend:  ${backend}"
echo "  ps-mode:  ${bootstrap_mode}"
echo "  strategy: ${bootstrap_strategy} (${bootstrap_failure_policy})"
echo "  diagnose: ${diagnostics_mode}"
echo "  output:   ${output_dir}"
if [ "${full_bootstrap}" -eq 1 ]; then
  echo "  rust:     full-bootstrap enabled; seed/runtime may be rebuilt"
else
  echo "  rust:     seed/runtime reuse only; cargo disabled"
fi

if [ -n "${resume_stage4_output}" ]; then
  echo "  mode:     admitted Stage 3 → Stage 4 continuation"
  stage3_provenance_dir="${output_dir}/stage3/${PLATFORM}"
  stage3_provenance_manifest="${stage3_provenance_dir}/provenance.env"
  resume_stage4_prepare "${output_dir}" "${repo_root}" "${PLATFORM}" \
    "${bootstrap_receipt_path}" || exit 1
  stage2="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
  stage3_ok=1
elif [ "${can_full_bootstrap}" -eq 1 ]; then
  # Full CLI available — use high-level staged bootstrap
  echo "  mode:     full CLI (build bootstrap)"
  RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}" \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    "${seed_bin}" run src/app/cli/main.spl build bootstrap "--backend=${backend}" "--output=${output_dir}"
else
  # Bootstrap-only or missing — manual staged bootstrap via seed
  echo "  mode:     manual (seed → bootstrap_main → bootstrap_main)"
  if [ ! -x "${seed_bin}" ]; then
    echo "error: Rust seed required for manual bootstrap (${seed_bin})" >&2
    echo "Run: scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap" >&2
    exit 1
  fi

  # Capture the complete source authority before either staged compiler runs.
  # The manifest is emitted only after an identical post-Stage-3 snapshot.
  stage3_provenance_dir="${output_dir}/stage3/${PLATFORM}"
  stage3_provenance_manifest="${stage3_provenance_dir}/provenance.env"
  stage3_source_before="${stage3_provenance_dir}/source-inputs-before.txt"
  stage3_source_after="${stage3_provenance_dir}/source-inputs-after.txt"
  stage3_git_before="${stage3_provenance_dir}/git-state-before.env"
  stage3_git_after="${stage3_provenance_dir}/git-state-after.env"
  stage2_command_transcript="${stage3_provenance_dir}/stage2-command.transcript"
  stage3_command_transcript="${stage3_provenance_dir}/stage3-command.transcript"
  stage2_sanity_evidence="${stage3_provenance_dir}/stage2-sanity.env"
  stage2_receiver_evidence="${stage3_provenance_dir}/stage2-receiver.env"
  stage2_receiver_log="${stage3_provenance_dir}/stage2-receiver.log"
  stage3_sanity_evidence="${stage3_provenance_dir}/stage3-sanity.env"
  stage2_provenance_cache="${stage3_provenance_dir}/stage2-native-cache"
  stage3_provenance_cache="${stage3_provenance_dir}/stage3-native-cache"
  stage2_provenance_home="${stage3_provenance_dir}/stage2-home"
  stage2_provenance_tmp="${stage3_provenance_dir}/stage2-tmp"
  stage3_provenance_home="${stage3_provenance_dir}/stage3-home"
  stage3_provenance_tmp="${stage3_provenance_dir}/stage3-tmp"
  stage2_admitted_dir="${stage3_provenance_dir}/stage2-admitted"
  stage2_admitted_bin="${stage2_admitted_dir}/simple${exe_suffix}"
  stage2_admission_receipt="${stage2_admitted_dir}/admission.env"
  stage2_runtime_authority="${stage3_provenance_dir}/stage2-runtime-authority"
  runtime_origin_before="${stage3_provenance_dir}/runtime-origin-before.txt"
  runtime_origin_after="${stage3_provenance_dir}/runtime-origin-after.txt"
  runtime_admitted_snapshot="${stage3_provenance_dir}/runtime-admitted.txt"
  tool_authority_before="${stage3_provenance_dir}/tool-authority-before.txt"
  tool_authority_after="${stage3_provenance_dir}/tool-authority-after.txt"
  mkdir -p "${stage3_provenance_dir}"
  # A previous fail-closed run may leave its admitted authority deliberately
  # frozen (directories 0500, files 0400/0500). Thaw only this private output
  # tree before replacing it; source/runtime authorities remain untouched.
  chmod -R u+w "${stage3_provenance_dir}" || {
    echo "error: could not thaw previous Stage 3 provenance output" >&2
    exit 1
  }
  rm -f "${stage3_provenance_manifest}" \
    "${stage3_source_before}" "${stage3_source_after}" \
    "${stage3_git_before}" "${stage3_git_after}" \
    "${stage2_command_transcript}" "${stage3_command_transcript}" \
    "${stage2_sanity_evidence}" "${stage2_receiver_evidence}" \
    "${stage2_receiver_log}" "${stage3_sanity_evidence}"
  rm -rf "${stage2_provenance_home}" "${stage2_provenance_tmp}" \
    "${stage3_provenance_home}" "${stage3_provenance_tmp}" \
    "${stage2_admitted_dir}" "${stage2_runtime_authority}"
  # Stage 2/3 native-build caches are content-hash keyed by the pure-Simple
  # driver itself (driver_native_sources_fingerprint scopes each cache entry
  # under the loaded source set's combined hash — see
  # src/compiler/80.driver/driver_aot_native_output.spl), so an unchanged
  # source tree naturally misses on any real change and never serves a stale
  # object. Unconditionally wiping them here defeated ALL cross-run
  # incrementality even when nothing changed. Preserve them by default;
  # --fresh-cache/--clean-release still forces a clean rebuild.
  if [ "${fresh_cache}" -eq 1 ] || [ "${execution_profile}" = "clean-release" ]; then
    echo "  provenance: clearing stage2/stage3 native caches (--fresh-cache/--clean-release)"
    rm -rf "${stage2_provenance_cache}" "${stage3_provenance_cache}"
  else
    # Preserved caches still need a reaper: scope dirs are mint-once and
    # nothing else collects them now that the unconditional wipe is gone.
    bootstrap_native_cache_prune "${stage2_provenance_cache}"
    bootstrap_native_cache_prune "${stage3_provenance_cache}"
  fi
  mkdir -p "${stage2_provenance_home}" "${stage2_provenance_tmp}" \
    "${stage3_provenance_home}" "${stage3_provenance_tmp}"
  bootstrap_acquire_rust_authority || exit 1
  bootstrap_authority_require_owned_lock "${rust_target_lock_handle}" || {
    echo "error: Rust authority lock ownership was lost before legacy normalization" >&2
    exit 1
  }
  runtime_origin_absolute=$(bootstrap_stage3_physical_directory \
    "$(absolute_path src/compiler_rust/target/bootstrap)") || {
    echo "error: missing Rust runtime authority" >&2
    exit 1
  }
  runtime_bootstrap_self_link="${runtime_origin_absolute}/bootstrap"
  if [ -L "${runtime_bootstrap_self_link}" ]; then
    runtime_bootstrap_self_target=$(readlink "${runtime_bootstrap_self_link}") ||
      exit 1
    case "${runtime_bootstrap_self_target}" in
      /*)
        runtime_bootstrap_self_target=$(
          CDPATH= cd -- "${runtime_bootstrap_self_target}" && pwd -P
        ) || exit 1
        ;;
      *)
        runtime_bootstrap_self_target=$(
          CDPATH= cd -- \
            "${runtime_origin_absolute}/${runtime_bootstrap_self_target}" &&
            pwd -P
        ) || exit 1
        ;;
    esac
    [ "${runtime_bootstrap_self_target}" = "${runtime_origin_absolute}" ] || {
      echo "error: unexpected Rust runtime authority symlink" >&2
      exit 1
    }
    rm -f "${runtime_bootstrap_self_link}"
  fi
  runtime_compiler_archive_link="${runtime_origin_absolute}/libsimple_compiler.a"
  if [ -L "${runtime_compiler_archive_link}" ]; then
    runtime_compiler_archive_target=$(readlink \
      "${runtime_compiler_archive_link}") || exit 1
    [ "${runtime_compiler_archive_target}" = "deps/libsimple_compiler.a" ] || {
      echo "error: unexpected Rust compiler archive authority symlink" >&2
      exit 1
    }
    [ -f "${runtime_origin_absolute}/${runtime_compiler_archive_target}" ] || {
      echo "error: missing Rust compiler archive authority target" >&2
      exit 1
    }
    bootstrap_authority_materialize_legacy_file \
      "${rust_target_lock_handle}" "${runtime_compiler_archive_link}" || {
      echo "error: could not materialize Rust compiler archive under authority lock" >&2
      exit 1
    }
  fi
  if [ ! -f "${rust_authority_current_marker}" ]; then
    bootstrap_stage3_verify_seed_stamp "${seed_stamp}" \
      "${seed_inputs_fingerprint}" "${seed_bin}" "${native_all_lib}" \
      "${compiler_backfill_lib}" || {
      echo "error: markerless legacy Rust authority is incomplete or stale" >&2
      echo "Run with --full-bootstrap to publish a complete immutable tuple." >&2
      exit 1
    }
    legacy_generation_nonce=$(od -An -N16 -tx1 /dev/urandom 2>/dev/null | tr -d ' \n')
    legacy_observed_fingerprint=$(seed_inputs_hash commit) || exit 1
    bootstrap_authority_migrate_complete_legacy \
      "${runtime_origin_absolute}" "${rust_authority_generation_root}" \
      "${rust_authority_current_marker}" \
      "${rust_authority_compatibility_path}" \
      "${seed_inputs_fingerprint}" \
      "simple${exe_suffix}" \
      "${archive_prefix}simple_native_all${archive_suffix}" \
      "${archive_prefix}simple_compiler_backfill${archive_suffix}" \
      "${legacy_generation_nonce}" "${rust_target_lock_handle}" \
      "${legacy_observed_fingerprint}" || {
      echo "error: complete legacy Rust authority migration failed" >&2
      exit 1
    }
    runtime_origin_absolute=${BOOTSTRAP_STAGE3_COMMITTED_AUTHORITY}
  fi
  if [ -f "${rust_authority_current_marker}" ]; then
    bootstrap_stage3_resolve_committed_seed \
      "${rust_authority_generation_root}" \
      "${rust_authority_current_marker}" || {
      echo "error: committed Rust authority is not admissible" >&2
      exit 1
    }
    runtime_origin_absolute=${BOOTSTRAP_STAGE3_COMMITTED_AUTHORITY}
  fi
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_origin_before}")" \
    "${runtime_origin_absolute}" || {
    echo "error: could not snapshot Rust runtime authority" >&2
    exit 1
  }
  bootstrap_stage3_copy_authority "${runtime_origin_absolute}" \
    "$(absolute_path "${stage2_runtime_authority}")" || {
    echo "error: could not freeze Stage 2 runtime authority" >&2
    exit 1
  }
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_origin_after}")" \
    "${runtime_origin_absolute}" || exit 1
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_admitted_snapshot}")" \
    "$(absolute_path "${stage2_runtime_authority}")" || exit 1
  cmp -s "${runtime_origin_before}" "${runtime_origin_after}" &&
    cmp -s "${runtime_origin_after}" "${runtime_admitted_snapshot}" || {
    echo "error: Rust runtime authority changed during private admission" >&2
    exit 1
  }
  bootstrap_release_rust_authority || {
    echo "error: could not release Rust authority after private admission" >&2
    exit 1
  }
  bootstrap_authority_pin_stage4 \
    "$(absolute_path "${stage2_runtime_authority}")" \
    "simple${exe_suffix}" \
    "${archive_prefix}simple_native_all${archive_suffix}" \
    "${archive_prefix}simple_compiler_backfill${archive_suffix}" || {
    echo "error: private admitted Rust authority is incomplete" >&2
    exit 1
  }
  stage_runtime_absolute=${BOOTSTRAP_STAGE4_RUNTIME_PATH}
  stage2_seed_absolute=${BOOTSTRAP_STAGE4_SEED}
  seed_bin=${BOOTSTRAP_STAGE4_SEED}
  native_all_lib=${BOOTSTRAP_STAGE4_NATIVE_ALL}
  compiler_backfill_lib=${BOOTSTRAP_STAGE4_BACKFILL}
  seed_stamp="${seed_bin}.inputs.sha256"
  SIMPLE_RUNTIME_PATH=${stage_runtime_absolute}
  bootstrap_runtime_authority_path=${stage_runtime_absolute}
  export SIMPLE_RUNTIME_PATH
  bootstrap_stage3_tool_authority_snapshot \
    "$(absolute_path "${tool_authority_before}")" "${PATH}" \
    "${repo_root}" || {
    echo "error: could not bind bootstrap tool authority" >&2
    exit 1
  }
  bootstrap_stage3_git_state "${repo_root}" "${stage3_git_before}" || {
    echo "error: could not bind Stage 3 git HEAD/dirty state" >&2
    exit 1
  }
  bootstrap_stage3_source_snapshot "${stage3_source_before}" "${repo_root}" || {
    echo "error: could not snapshot Stage 3 source authority" >&2
    exit 1
  }

  # Stage 2: seed compiles bootstrap_main.spl
  # Stage 2 uses the configured backend; LLVM is the default and Cranelift is
  # an explicit supported alternative.
  mkdir -p "${output_dir}/stage2/${PLATFORM}"
  echo "Stage 2: seed → bootstrap_main.spl"
  # Preserve the verified phase-1 (seed) compiler as an immutable lineage snapshot.
  if [ -x "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" ]; then
    sh "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" preserve-phase-binary "${seed_bin}" phase1 || \
      echo "  warning: phase1 snapshot preservation failed (non-fatal)" >&2
  fi
  bootstrap_progress_mark stage2 "$(absolute_path "${log_dir}/stage2-native-build.log")"
  mkdir -p "${stage2_provenance_cache}"
  # Stage 2 failure is reported before Stage 3; no later stage may claim it.
  # the self-hosting frontend now fails closed instead of linking a ret-0 stub
  # (doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md), so a
  # stage-2 build error must not abort the whole pipeline.
  stage2_bin="$(absolute_path \
    "${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}")"
  stage3_bin="$(absolute_path \
    "${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}")"
  native_verbose_arg=""
  if [ "${verbose}" -eq 1 ]; then
    native_verbose_arg="--verbose"
  fi
  stage_build_rust_log="${RUST_LOG:-error}"
  stage2_seed_absolute="$(absolute_path \
    "${stage2_runtime_authority}/simple${exe_suffix}")"
  stage2_output_absolute="${stage2_bin}"
  stage3_output_absolute="${stage3_bin}"
  stage2_admitted_absolute="$(absolute_path "${stage2_admitted_bin}")"
  stage2_admission_receipt_absolute="$(absolute_path \
    "${stage2_admission_receipt}")"
  stage_runtime_absolute="$(absolute_path "${stage2_runtime_authority}")"
  stage2_cache_absolute="$(absolute_path "${stage2_provenance_cache}")"
  stage3_cache_absolute="$(absolute_path "${stage3_provenance_cache}")"
  stage2_home_absolute="$(absolute_path "${stage2_provenance_home}")"
  stage2_tmp_absolute="$(absolute_path "${stage2_provenance_tmp}")"
  stage3_home_absolute="$(absolute_path "${stage3_provenance_home}")"
  stage3_tmp_absolute="$(absolute_path "${stage3_provenance_tmp}")"
  stage_build_path="${PATH:?PATH is required}"
  case "${stage_build_path}" in
    /*) ;;
    *) echo "error: bootstrap PATH must contain absolute entries only" >&2; exit 1 ;;
  esac
  if printf '%s\n' "${stage_build_path}" | grep -Eq '(^|:)([^/]|$)'; then
    echo "error: bootstrap PATH must contain absolute entries only" >&2
    exit 1
  fi
  bootstrap_link_library_path=""
  bootstrap_link_compat_sha256=absent
  if [ "${os}" = "linux" ]; then
    bootstrap_unwind_link_name=$(
      "${cc_abs:-cc}" -print-file-name=libunwind.so 2>/dev/null || true
    )
    bootstrap_unwind_runtime=$(
      "${cc_abs:-cc}" -print-file-name=libunwind.so.8 2>/dev/null || true
    )
    if [ "${bootstrap_unwind_link_name}" = "libunwind.so" ] &&
       [ -f "${bootstrap_unwind_runtime}" ]; then
      bootstrap_link_compat_dir="${stage3_provenance_dir}/link-compat"
      rm -rf "${bootstrap_link_compat_dir}"
      mkdir -p "${bootstrap_link_compat_dir}"
      cp -pL "${bootstrap_unwind_runtime}" \
        "${bootstrap_link_compat_dir}/libunwind.so"
      bootstrap_link_library_path=$(
        absolute_path "${bootstrap_link_compat_dir}"
      )
      bootstrap_link_compat_sha256=$(
        bootstrap_stage3_hash_file \
          "${bootstrap_link_compat_dir}/libunwind.so"
      ) || exit 1
    fi
  fi
  stage2_build_args_sha256=$(
    bootstrap_stage3_args_sha256 \
      "RUST_LOG=${stage_build_rust_log}" \
      "LIBRARY_PATH=${bootstrap_link_library_path}" \
      "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=${bootstrap_link_compat_sha256}" \
      "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
      "SIMPLE_NATIVE_BUILD_RUST=1" \
      "SIMPLE_NO_STUB_FALLBACK=1" \
      "SIMPLE_BUILD_PROGRESS_EVENTS=${build_progress_events}" \
      "SIMPLE_BINARY=${stage2_seed_absolute}" \
      native-build --target "${PLATFORM}" --backend "${backend}" \
      --runtime-bundle core-c-bootstrap \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure --threads "${jobs}" --cache-dir "${stage2_cache_absolute}" \
      ${native_verbose_arg} \
      --mode "${bootstrap_mode}" --entry src/app/cli/bootstrap_main.spl \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage2_bin}"
  )
  stage3_evidence_run_id="stage3-${PLATFORM}-$$"
  stage3_memory_snapshot="${stage3_provenance_dir}/memory-snapshot-v1.events"
  stage3_phase_profile="${stage3_provenance_dir}/phase-profile-v1.events"
  # Narrowly-scoped diagnostic pass-through for Stage 3.  Computed ONCE here and
  # word-split into both the args-hash vector below and the real invocation, so
  # the two can never disagree.  Values are constrained to the literal `1` and
  # names to a fixed print-only allowlist by bootstrap_stage3_diagnostic_env, so
  # unquoted expansion is safe and no glob character can occur.  Empty by
  # default => both uses are byte-identical to before this existed.
  stage3_diagnostic_env=$(bootstrap_stage3_diagnostic_env) || exit 1
  stage3_build_args_sha256=$(
    bootstrap_stage3_args_sha256 \
      "RUST_LOG=${stage_build_rust_log}" \
      "LIBRARY_PATH=${bootstrap_link_library_path}" \
      "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=${bootstrap_link_compat_sha256}" \
      "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
      "SIMPLE_STAGE3_STREAMING_SURFACES=1" \
      "SIMPLE_FRONTEND_CACHE=0" \
      "MALLOC_ARENA_MAX=2" "MALLOC_TRIM_THRESHOLD_=0" \
      "SIMPLE_NATIVE_ARENA_DECLS=1" \
      "SIMPLE_NO_STUB_FALLBACK=1" \
      "SIMPLE_BUILD_PROGRESS_EVENTS=${build_progress_events}" \
      "SIMPLE_COMPILER_PHASE_PROFILE=1" \
      "SIMPLE_COMPILER_PHASE_PROFILE_FILE=${stage3_phase_profile}" \
      "SIMPLE_MEM_SNAPSHOT_FILE=${stage3_memory_snapshot}" \
      "SIMPLE_EVIDENCE_RUN_ID=${stage3_evidence_run_id}" \
      "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1" \
      "SIMPLE_NATIVE_BUILD_TARGET=${PLATFORM}" \
      "SIMPLE_NATIVE_BUILD_THREADS=${selfhost_jobs}" \
      "SIMPLE_NATIVE_BUILD_CACHE_DIR=${stage3_cache_absolute}" \
      "SIMPLE_RUNTIME_PATH=${stage_runtime_absolute}" \
      "SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap" \
      "SIMPLE_BINARY=${stage2_admitted_absolute}" \
      ${stage3_diagnostic_env} \
      native-build --target "${PLATFORM}" --backend "${backend}" \
      --runtime-bundle core-c-bootstrap \
      --threads "${selfhost_jobs}" \
      --cache-dir "${stage3_cache_absolute}" --mode "${bootstrap_mode}" \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage3_bin}" src/app/cli/bootstrap_main.spl
  )
  rm -f "${stage2_bin}" "${stage3_bin}"
  bootstrap_stage3_directory_snapshot \
    "${stage3_provenance_dir}/runtime-before-stage2.txt" \
    "${stage_runtime_absolute}" || exit 1
  cmp -s "${runtime_admitted_snapshot}" \
    "${stage3_provenance_dir}/runtime-before-stage2.txt" || exit 1
  set +e
  bootstrap_stage3_run_transcribed \
    "$(absolute_path "${stage2_command_transcript}")" "${repo_root}" \
    "$(absolute_path "${log_dir}/stage2-native-build.log")" \
    "${stage2_home_absolute}" "${stage2_tmp_absolute}" "${stage_build_path}" \
    RUST_LOG="${stage_build_rust_log}" \
    LIBRARY_PATH="${bootstrap_link_library_path}" \
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256="${bootstrap_link_compat_sha256}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_BINARY="${stage2_seed_absolute}" -- \
    "${stage2_seed_absolute}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --threads "${jobs}" \
    ${native_verbose_arg} \
    --cache-dir "${stage2_cache_absolute}" \
    --mode "${bootstrap_mode}" \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "${stage_runtime_absolute}" \
    -o "${stage2_bin}"
  stage2_status=$?
  set -e
  bootstrap_stage3_directory_snapshot \
    "${stage3_provenance_dir}/runtime-after-stage2.txt" \
    "${stage_runtime_absolute}" || exit 1
  cmp -s "${runtime_admitted_snapshot}" \
    "${stage3_provenance_dir}/runtime-after-stage2.txt" || {
    echo "error: frozen runtime authority changed during Stage 2" >&2
    exit 1
  }
  echo "  stage2-native-build log: ${log_dir}/stage2-native-build.log"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    echo "  Stage 2: running bootstrap compiler sanity"
    if ! bootstrap_stage_sanity "${stage2_bin}" \
      "$(absolute_path "${stage2_sanity_evidence}")" \
      "${stage2_home_absolute}" "${stage2_tmp_absolute}" \
      "${stage_build_path}"; then
      echo "error: Stage 2 bootstrap compiler sanity failed" >&2
      stage2_status=2
      # Preserve, do not destroy: the old `rm -f` deleted the only copy of the
      # artifact and with it all post-mortem value. Renaming keeps the failed
      # candidate off every downstream `-x "${stage2_bin}"` guard (which is what
      # the delete was actually for) while leaving it on disk for diagnosis.
      rm -f "${stage2_bin}.rejected"
      if mv "${stage2_bin}" "${stage2_bin}.rejected"; then
        echo "  rejected Stage 2 binary preserved: ${stage2_bin}.rejected" >&2
      else
        rm -f "${stage2_bin}"
      fi
    fi
  fi
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    echo "  Stage 2: proving struct receiver/runtime capability"
    stage2_receiver_sha_before=$(bootstrap_stage3_hash_file "${stage2_bin}")
    set +e
    env HOME="${stage2_home_absolute}" TMPDIR="${stage2_tmp_absolute}" \
      PATH="${stage_build_path}" LC_ALL=C LANG=C \
      SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      sh "${repo_root}/scripts/check/check-bootstrap-stage2-struct-receiver.shs" \
        "${stage2_bin}" "${stage_runtime_absolute}" "${PLATFORM}" "${backend}" \
        >"${stage2_receiver_log}" 2>&1
    stage2_receiver_status=$?
    set -e
    stage2_receiver_sha_after=$(bootstrap_stage3_hash_file "${stage2_bin}")
    bootstrap_stage3_directory_snapshot \
      "${stage3_provenance_dir}/runtime-after-stage2-receiver.txt" \
      "${stage_runtime_absolute}" || exit 1
    receiver_status=fail
    if [ "${stage2_receiver_status}" -eq 0 ] &&
      [ "${stage2_receiver_sha_before}" = "${stage2_receiver_sha_after}" ] &&
      cmp -s "${runtime_admitted_snapshot}" \
        "${stage3_provenance_dir}/runtime-after-stage2-receiver.txt"; then
      receiver_status=pass
    fi
    {
      echo "schema=simple-bootstrap-stage2-receiver-evidence-v1"
      echo "status=${receiver_status}"
      echo "probe_exit=${stage2_receiver_status}"
      echo "candidate_sha256_before=${stage2_receiver_sha_before}"
      echo "candidate_sha256_after=${stage2_receiver_sha_after}"
      echo "runtime_snapshot_sha256=$(bootstrap_stage3_hash_file "${runtime_admitted_snapshot}")"
      echo "probe_log=${stage2_receiver_log}"
      echo "probe_log_sha256=$(bootstrap_stage3_hash_file "${stage2_receiver_log}")"
    } >"${stage2_receiver_evidence}"
    if [ "${receiver_status}" != pass ]; then
      echo "error: Stage 2 struct receiver/runtime capability failed" >&2
      stage2_status=3
      stage2_rejected_dir="${output_dir}/stage2-rejected/${PLATFORM}"
      stage2_rejected_bin="${stage2_rejected_dir}/simple${exe_suffix}"
      stage2_rejected_receipt="${stage2_rejected_dir}/rejection.env"
      mkdir -p "${stage2_rejected_dir}"
      mv "${stage2_bin}" "${stage2_rejected_bin}"
      chmod 400 "${stage2_rejected_bin}"
      {
        echo "schema=simple-bootstrap-rejected-stage2-v1"
        echo "status=rejected"
        echo "reason=stage2-struct-receiver-failed"
        echo "candidate=${stage2_rejected_bin}"
        echo "candidate_sha256=$(bootstrap_stage3_hash_file "${stage2_rejected_bin}")"
        echo "sanity_evidence=${stage2_sanity_evidence}"
        echo "receiver_evidence=${stage2_receiver_evidence}"
      } >"${stage2_rejected_receipt}"
      chmod 400 "${stage2_rejected_receipt}"
    fi
  fi
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    bootstrap_stage3_tool_authority_snapshot \
      "$(absolute_path "${tool_authority_after}")" "${PATH}" "${repo_root}" || exit 1
    bootstrap_stage3_git_state "${repo_root}" "${stage3_git_after}" || exit 1
    bootstrap_stage3_source_snapshot "${stage3_source_after}" "${repo_root}" || exit 1
    if ! cmp -s "${tool_authority_before}" "${tool_authority_after}" ||
       ! cmp -s "${stage3_source_before}" "${stage3_source_after}" ||
       ! grep -qx 'status=pass' "${stage2_sanity_evidence}" ||
       ! grep -qx 'status=pass' "${stage2_receiver_evidence}"; then
      echo "error: refused incomplete Stage 2 admission provenance" >&2
      stage2_status=4
    else
      stage2_origin_sha_before=$(bootstrap_stage3_hash_file "${stage2_bin}")
      mkdir -p "${stage2_admitted_dir}"
      cp -p "${stage2_bin}" "${stage2_admitted_bin}"
      chmod 500 "${stage2_admitted_bin}"
      stage2_origin_sha_after=$(bootstrap_stage3_hash_file "${stage2_bin}")
      [ "${stage2_origin_sha_before}" = "${stage2_origin_sha_after}" ] &&
        [ "${stage2_origin_sha_before}" = \
          "$(bootstrap_stage3_hash_file "${stage2_admitted_bin}")" ] || {
        echo "error: Stage 2 compiler changed during private admission" >&2
        exit 1
      }
      # Re-snapshot after publication: a concurrent source edit invalidates
      # the private copy and prevents a stop-after-stage2 false admission.
      bootstrap_stage3_source_snapshot "${stage3_source_after}" "${repo_root}" || exit 1
      if ! cmp -s "${stage3_source_before}" "${stage3_source_after}"; then
        chmod u+w "${stage2_admitted_bin}"
        rm -f "${stage2_admitted_bin}"
        rmdir "${stage2_admitted_dir}" 2>/dev/null || true
        echo "error: refused incomplete Stage 2 admission provenance" >&2
        stage2_status=4
      elif ! bootstrap_stage3_write_stage2_admission_receipt \
        "${stage2_admission_receipt_absolute}" \
        "${stage2_admitted_absolute}" "$(absolute_path "${stage3_source_before}")" \
        "$(absolute_path "${runtime_admitted_snapshot}")" \
        "$(absolute_path "${tool_authority_before}")" \
        "${stage2_build_args_sha256}" \
        "$(absolute_path "${stage2_sanity_evidence}")" \
        "$(absolute_path "${stage2_receiver_evidence}")"; then
        chmod u+w "${stage2_admitted_bin}"
        rm -f "${stage2_admitted_bin}" "${stage2_admission_receipt}"
        rmdir "${stage2_admitted_dir}" 2>/dev/null || true
        echo "error: could not publish immutable Stage 2 admission receipt" >&2
        stage2_status=4
      else
        if [ "${bootstrap_stage2_trust_root}" -eq 1 ]; then
          stage2_parent_dir=$(dirname -- "${stage2_bin}")
          stage2_parent_sanity="${stage2_parent_dir}/stage2-sanity.receipt"
          stage2_parent_provenance="${stage2_parent_dir}/stage2-provenance.receipt"
          stage2_parent_sanity_tmp="${stage2_parent_sanity}.tmp.$$"
          stage2_parent_provenance_tmp="${stage2_parent_provenance}.tmp.$$"
          {
            echo 'schema=simple-bootstrap-stage2-parent-sanity-v1'
            echo 'stage2-sanity: pass'
            echo "candidate_sha256=${stage2_origin_sha_before}"
            echo "admission_receipt_path=${stage2_admission_receipt_absolute}"
            echo "admission_receipt_sha256=$(bootstrap_stage3_hash_file "${stage2_admission_receipt_absolute}")"
          } >"${stage2_parent_sanity_tmp}"
          {
            echo 'schema=simple-bootstrap-stage2-parent-provenance-v1'
            echo 'stage2-provenance: pure-simple'
            echo 'authority=explicit-full-bootstrap-stage2-trust-root'
            echo "candidate_sha256=${stage2_origin_sha_before}"
            echo "admission_receipt_path=${stage2_admission_receipt_absolute}"
            echo "source_snapshot_sha256=$(bootstrap_stage3_hash_file "${stage3_source_before}")"
            echo "runtime_snapshot_sha256=$(bootstrap_stage3_hash_file "${runtime_admitted_snapshot}")"
            echo "tool_authority_sha256=$(bootstrap_stage3_hash_file "${tool_authority_before}")"
            echo "admission_receipt_sha256=$(bootstrap_stage3_hash_file "${stage2_admission_receipt_absolute}")"
          } >"${stage2_parent_provenance_tmp}"
          chmod 400 "${stage2_parent_sanity_tmp}" "${stage2_parent_provenance_tmp}"
          mv -f "${stage2_parent_sanity_tmp}" "${stage2_parent_sanity}"
          mv -f "${stage2_parent_provenance_tmp}" "${stage2_parent_provenance}"
        fi
        # Preserve the admitted phase-2 compiler as an immutable lineage snapshot.
        if [ -x "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" ]; then
          sh "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" preserve-phase-binary "${stage2_admitted_bin}" phase2 || \
            echo "  warning: phase2 snapshot preservation failed (non-fatal)" >&2
        fi
        chmod 500 "${stage2_admitted_dir}"
      fi
    fi
  fi
  if [ "${stage2_status}" -ne 0 ]; then
    # A failing stage must say WHY. Before this, stage2 could exit 1 with a
    # 0-byte stage2-native-build.log and no error text anywhere, and the three
    # distinct causes (wrapper precondition refusal / compiler died unflushed /
    # exit-125 post-run verification) were indistinguishable and all silent.
    # The classification is a separate guard so it is exercisable by
    # `--selftest` without running a bootstrap.
    # doc/08_tracking/bug/bootstrap_stage2_silent_exit1_empty_log_2026-08-17.md
    sh "${repo_root}/scripts/check/check-stage-log-diagnosable.shs" \
      --stage stage2 \
      --status "${stage2_status}" \
      --log "${log_dir}/stage2-native-build.log" \
      --transcript "${stage3_provenance_dir}/stage2-command.transcript" >&2
    stage2_diag_status=$?
    if [ "${stage2_diag_status}" -ne 0 ]; then
      echo "error: stage2 failed with NO diagnostic text (see the block above);" >&2
      echo "       this is itself a defect — a stage that dies must leave evidence." >&2
    fi
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage2 failed (exit ${stage2_status}); refusing seed fallback" >&2
      exit "${stage2_status}"
    fi
    echo "  warning: stage2 native-build failed (exit ${stage2_status}); Stage 3/full CLI unavailable" >&2
    echo "  warning: see doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md" >&2
  fi

  if [ "${stop_after_stage2}" -eq 1 ]; then
    [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_admitted_bin}" ] || {
      echo "error: --stop-after-stage2 requires a successful admitted Stage 2 compiler" >&2
      exit 1
    }
    echo "Stage 2 admitted; stopping before Stage 3 as requested."
    exit 0
  fi

  # Stage 3: stage2 recompiles bootstrap_main.spl (self-host verification)
  # Note: Stage3 is optional — the stage2 binary may lack features needed for
  # pure in-process self-hosting. When Stage 3 fails, the wrapper stops before
  # Stage 4.
  mkdir -p "${output_dir}/stage3/${PLATFORM}"
  echo "Stage 3: stage2 → bootstrap_main.spl (self-host)"
  bootstrap_progress_mark stage3 "$(absolute_path "${log_dir}/stage3-native-build.log")"
  # See the cache-preservation note above (~line 1300): this cache is
  # content-hash scoped by the driver itself, so keep it across runs unless
  # a clean rebuild was explicitly requested.
  if [ "${fresh_cache}" -eq 1 ] || [ "${execution_profile}" = "clean-release" ]; then
    rm -rf "${stage3_provenance_cache}"
  fi
  mkdir -p "${stage3_provenance_cache}"

  stage3_ok=0
  rm -f "${stage3_bin}"
  stage2_admitted_sha_before_stage3=absent
  if [ "${stage2_status}" -eq 0 ]; then
    stage2_admitted_sha_before_stage3=$(
      bootstrap_stage3_hash_file "${stage2_admitted_absolute}"
    ) || exit 1
    bootstrap_stage3_directory_snapshot \
      "${stage3_provenance_dir}/runtime-before-stage3.txt" \
      "${stage_runtime_absolute}" || exit 1
    cmp -s "${runtime_admitted_snapshot}" \
      "${stage3_provenance_dir}/runtime-before-stage3.txt" || exit 1
  fi
  # STAGE 3 MUST USE THE BARE POSITIONAL `.spl` SHAPE. Do NOT add `--entry`,
  # `--entry-closure`, or `--source` here (see
  # doc/08_tracking/bug/stage3_entry_flag_delegates_to_rust_seed_2026-08-04.md).
  # `run_native_build_bootstrap` (src/app/cli/bootstrap_main.spl) routes to the
  # pure-Simple in-process CompilerDriver ONLY for a single `.spl` positional
  # with no `--source`. An explicit `--entry` outside the Stage 4 allowlist, or
  # ANY `--source`, falls through to `run_rt_native_build` -> the Rust seed FFI,
  # which silently turns the self-host verification into a second seed build.
  # The positional branch already seeds SIMPLE_NATIVE_BUILD_ENTRY and
  # SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0, so entry-closure discovery still
  # happens -- inside the self-hosted driver, which is the point of Stage 3.
  # Stage 2 above is a seed build by design and keeps its --entry/--source form.
  set +e
  [ ! -e "${stage3_memory_snapshot}" ] && [ ! -L "${stage3_memory_snapshot}" ] || exit 1
  [ ! -e "${stage3_phase_profile}" ] && [ ! -L "${stage3_phase_profile}" ] || exit 1
  [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ] && \
  bootstrap_stage3_run_transcribed \
    "$(absolute_path "${stage3_command_transcript}")" "${repo_root}" \
    "$(absolute_path "${log_dir}/stage3-native-build.log")" \
    "${stage3_home_absolute}" "${stage3_tmp_absolute}" "${stage_build_path}" \
    RUST_LOG="${stage_build_rust_log}" \
    LIBRARY_PATH="${bootstrap_link_library_path}" \
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256="${bootstrap_link_compat_sha256}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_STAGE3_STREAMING_SURFACES=1 \
    SIMPLE_FRONTEND_CACHE=0 \
    MALLOC_ARENA_MAX=2 \
    MALLOC_TRIM_THRESHOLD_=0 \
    SIMPLE_NATIVE_ARENA_DECLS=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_COMPILER_PHASE_PROFILE=1 \
    SIMPLE_COMPILER_PHASE_PROFILE_FILE="${stage3_phase_profile}" \
    SIMPLE_MEM_SNAPSHOT_FILE="${stage3_memory_snapshot}" \
    SIMPLE_EVIDENCE_RUN_ID="${stage3_evidence_run_id}" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_NATIVE_BUILD_TARGET="${PLATFORM}" \
    SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}" \
    SIMPLE_NATIVE_BUILD_CACHE_DIR="${stage3_cache_absolute}" \
    SIMPLE_RUNTIME_PATH="${stage_runtime_absolute}" \
    SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
    SIMPLE_BINARY="${stage2_admitted_absolute}" \
    ${stage3_diagnostic_env} -- \
    "${stage2_admitted_absolute}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --threads "${selfhost_jobs}" \
    --cache-dir "${stage3_cache_absolute}" \
    --mode "${bootstrap_mode}" \
    --runtime-path "${stage_runtime_absolute}" \
    -o "${stage3_bin}" src/app/cli/bootstrap_main.spl
  stage3_status=$?
  set -e
  # Stage 3 self-host provenance gate (fail-closed).
  # `Build complete: N compiled, M cached, K failed` and `Linked: ... via
  # clang++` are emitted ONLY by src/compiler_rust/native_all/src/lib.rs. The
  # pure-Simple in-process CompilerDriver path prints neither -- it is silent on
  # success and prints `error: in-process native-build: ...` on failure. So
  # either marker in the Stage 3 log proves the Rust seed, not the Stage 2
  # self-hosted compiler, produced the Stage 3 binary. Without this gate the
  # delegation is completely silent and Stage 3 reads as a successful
  # self-host while actually being a second seed build.
  stage3_provenance_log="${log_dir}/stage3-native-build.log"
  if [ -f "${stage3_provenance_log}" ] && \
    grep -qE '^(Build complete: [0-9]+ compiled|Linked: .* via clang)' \
      "${stage3_provenance_log}"; then
    echo "error: Stage 3 was built by the Rust seed (rt_native_build), not the" >&2
    echo "       Stage 2 self-hosted compiler -- the self-host verification is" >&2
    echo "       vacuous. The Stage 3 native-build args must be the bare" >&2
    echo "       positional .spl form (no --entry / --entry-closure / --source)." >&2
    echo "       See doc/08_tracking/bug/stage3_entry_flag_delegates_to_rust_seed_2026-08-04.md" >&2
    echo "       Evidence: ${stage3_provenance_log}" >&2
    exit 1
  fi
  if [ "${stage2_admitted_sha_before_stage3}" != absent ]; then
    [ "${stage2_admitted_sha_before_stage3}" = \
      "$(bootstrap_stage3_hash_file "${stage2_admitted_absolute}")" ] || {
      echo "error: admitted Stage 2 compiler changed during Stage 3" >&2
      exit 1
    }
    bootstrap_stage3_directory_snapshot \
      "${stage3_provenance_dir}/runtime-after-stage3.txt" \
      "${stage_runtime_absolute}" || exit 1
    cmp -s "${runtime_admitted_snapshot}" \
      "${stage3_provenance_dir}/runtime-after-stage3.txt" || {
      echo "error: frozen runtime authority changed during Stage 3" >&2
      exit 1
    }
  fi

  echo "  stage3-native-build log: ${log_dir}/stage3-native-build.log"
  if [ "${stage3_status}" -eq 0 ] && [ -x "${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}" ]; then
    if bootstrap_stage_sanity "${stage3_bin}" \
      "$(absolute_path "${stage3_sanity_evidence}")" \
      "${stage3_home_absolute}" "${stage3_tmp_absolute}" \
      "${stage_build_path}"; then
      stage3_ok=1
      echo "  Stage 3 succeeded and passed bootstrap compiler sanity"
      # Preserve the verified phase-3 compiler as an immutable lineage snapshot.
      if [ -x "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" ]; then
        sh "${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh" preserve-phase-binary "${stage3_bin}" phase3 || \
          echo "  warning: phase3 snapshot preservation failed (non-fatal)" >&2
      fi
    else
      stage3_status=2
      rm -f "${stage3_bin}"
      echo "error: Stage 3 bootstrap compiler sanity failed" >&2
    fi
  fi
  if [ "${stage3_ok}" -ne 1 ]; then
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage3 failed; refusing seed fallback" >&2
      if [ "${stage3_status}" -ne 0 ]; then
        exit "${stage3_status}"
      fi
      exit 2
    fi
    if [ "${stage3_status}" -eq 0 ]; then
      echo "  warning: stage3 self-host produced no executable; Stage 4 unavailable"
    elif [ "${stage3_status}" -gt 128 ]; then
      # A signal death is not a compile failure. earlyoom(1) is userspace, so an
      # out-of-memory kill leaves nothing in dmesg and used to surface here as a
      # bare "failed (exit 143)" -- which reads as a compiler defect. Name it.
      stage3_signal=$((stage3_status - 128))
      echo "  warning: stage3 self-host was KILLED by signal ${stage3_signal} ($(kill -l "${stage3_signal}" 2>/dev/null || echo unknown)), not a compile failure; Stage 4 unavailable"
      if [ "${stage3_signal}" -eq 15 ] || [ "${stage3_signal}" -eq 9 ]; then
        echo "  hint: check for an out-of-memory reaper (earlyoom/systemd-oomd: 'journalctl -t earlyoom'); host memory pressure, not the source, is the usual cause"
      fi
    else
      echo "  warning: stage3 self-host failed (exit ${stage3_status}); Stage 4 unavailable"
    fi
  else
    bootstrap_stage3_tool_authority_snapshot \
      "$(absolute_path "${tool_authority_after}")" "${PATH}" \
      "${repo_root}" || exit 1
    cmp -s "${tool_authority_before}" "${tool_authority_after}" || {
      echo "error: bootstrap tool authority changed during Stage 2/3" >&2
      exit 1
    }
    bootstrap_stage3_git_state "${repo_root}" "${stage3_git_after}" || {
      echo "error: could not re-bind Stage 3 git HEAD/dirty state" >&2
      exit 1
    }
    bootstrap_stage3_source_snapshot "${stage3_source_after}" "${repo_root}" || {
      echo "error: could not snapshot Stage 3 source authority after build" >&2
      exit 1
    }
    BSTAGE3_ROOT="${repo_root}"
    BSTAGE3_MANIFEST="$(absolute_path "${stage3_provenance_manifest}")"
    BSTAGE3_PLATFORM="${PLATFORM}"
    BSTAGE3_BACKEND="${backend}"
    BSTAGE3_MODE="${bootstrap_mode}"
    BSTAGE3_SEED="${stage2_seed_absolute}"
    BSTAGE3_SEED_STAMP="${stage2_seed_absolute}.inputs.sha256"
    BSTAGE3_NATIVE_ALL="${stage_runtime_absolute}/${archive_prefix}simple_native_all${archive_suffix}"
    BSTAGE3_BACKFILL="${stage_runtime_absolute}/${archive_prefix}simple_compiler_backfill${archive_suffix}"
    BSTAGE3_RUNTIME_ORIGIN_BEFORE="$(absolute_path "${runtime_origin_before}")"
    BSTAGE3_RUNTIME_ORIGIN_AFTER="$(absolute_path "${runtime_origin_after}")"
    BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT="$(absolute_path "${runtime_admitted_snapshot}")"
    BSTAGE3_TOOL_AUTHORITY="$(absolute_path "${tool_authority_after}")"
    BSTAGE3_TOOL_AUTHORITY_BEFORE="$(absolute_path "${tool_authority_before}")"
    BSTAGE3_STAGE2="$(absolute_path "${stage2_bin}")"
    BSTAGE3_STAGE2_ADMITTED="${stage2_admitted_absolute}"
    BSTAGE3_STAGE2_ADMISSION="${stage2_admission_receipt_absolute}"
    BSTAGE3_STAGE3="$(absolute_path "${stage3_bin}")"
    BSTAGE3_SOURCE_BEFORE="$(absolute_path "${stage3_source_before}")"
    BSTAGE3_SOURCE_AFTER="$(absolute_path "${stage3_source_after}")"
    BSTAGE3_STAGE2_LOG="$(absolute_path "${log_dir}/stage2-native-build.log")"
    BSTAGE3_STAGE3_LOG="$(absolute_path "${log_dir}/stage3-native-build.log")"
    BSTAGE3_STAGE2_ARGS_SHA256="${stage2_build_args_sha256}"
    BSTAGE3_STAGE3_ARGS_SHA256="${stage3_build_args_sha256}"
    BSTAGE3_STAGE2_THREADS="${jobs}"
    BSTAGE3_STAGE3_THREADS="${selfhost_jobs}"
    BSTAGE3_STAGE2_CACHE_DIR="${stage2_cache_absolute}"
    BSTAGE3_STAGE3_CACHE_DIR="${stage3_cache_absolute}"
    BSTAGE3_RUNTIME_PATH="${stage_runtime_absolute}"
    BSTAGE3_STAGE2_COMMAND_OUTPUT="${stage2_bin}"
    BSTAGE3_STAGE3_COMMAND_OUTPUT="${stage3_bin}"
    BSTAGE3_BOOTSTRAP_SCRIPT="${bootstrap_script_path}"
    BSTAGE3_HELPER="${bootstrap_provenance_helper}"
    BSTAGE3_HELPER_SHA256_BEFORE="${bootstrap_provenance_helper_sha256_before}"
    BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE=\
"${bootstrap_provenance_bundle_fingerprint_before}"
    BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE="${bootstrap_script_sha256_before}"
    BSTAGE3_SEED_INPUTS_FINGERPRINT="${seed_inputs_fingerprint}"
    BSTAGE3_SEED_FEATURES="${llvm_features}"
    BSTAGE3_GIT_BEFORE="$(absolute_path "${stage3_git_before}")"
    BSTAGE3_GIT_AFTER="$(absolute_path "${stage3_git_after}")"
    BSTAGE3_STAGE2_TRANSCRIPT="$(absolute_path "${stage2_command_transcript}")"
    BSTAGE3_STAGE3_TRANSCRIPT="$(absolute_path "${stage3_command_transcript}")"
    BSTAGE3_STAGE2_SANITY="$(absolute_path "${stage2_sanity_evidence}")"
    BSTAGE3_STAGE2_RECEIVER="$(absolute_path "${stage2_receiver_evidence}")"
    BSTAGE3_STAGE3_SANITY="$(absolute_path "${stage3_sanity_evidence}")"
    BSTAGE3_LOCK="$(absolute_path "${bootstrap_lock}")"
    BSTAGE3_RUST_LOG="${stage_build_rust_log}"
    export BSTAGE3_ROOT BSTAGE3_MANIFEST BSTAGE3_PLATFORM BSTAGE3_BACKEND \
      BSTAGE3_MODE BSTAGE3_SEED BSTAGE3_NATIVE_ALL BSTAGE3_BACKFILL \
      BSTAGE3_RUNTIME_ORIGIN_BEFORE BSTAGE3_RUNTIME_ORIGIN_AFTER \
      BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT \
      BSTAGE3_TOOL_AUTHORITY BSTAGE3_TOOL_AUTHORITY_BEFORE \
      BSTAGE3_SEED_STAMP BSTAGE3_HELPER BSTAGE3_HELPER_SHA256_BEFORE \
      BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE \
      BSTAGE3_STAGE2 BSTAGE3_STAGE2_ADMITTED BSTAGE3_STAGE2_ADMISSION \
      BSTAGE3_STAGE3 \
      BSTAGE3_SOURCE_BEFORE \
      BSTAGE3_SOURCE_AFTER BSTAGE3_STAGE2_LOG BSTAGE3_STAGE3_LOG \
      BSTAGE3_STAGE2_ARGS_SHA256 BSTAGE3_STAGE3_ARGS_SHA256 \
      BSTAGE3_STAGE2_THREADS BSTAGE3_STAGE3_THREADS \
      BSTAGE3_STAGE2_CACHE_DIR BSTAGE3_STAGE3_CACHE_DIR \
      BSTAGE3_RUNTIME_PATH BSTAGE3_STAGE2_COMMAND_OUTPUT \
      BSTAGE3_STAGE3_COMMAND_OUTPUT \
      BSTAGE3_BOOTSTRAP_SCRIPT BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE \
      BSTAGE3_SEED_INPUTS_FINGERPRINT BSTAGE3_SEED_FEATURES \
      BSTAGE3_GIT_BEFORE BSTAGE3_GIT_AFTER \
      BSTAGE3_STAGE2_TRANSCRIPT BSTAGE3_STAGE3_TRANSCRIPT \
      BSTAGE3_STAGE2_SANITY BSTAGE3_STAGE2_RECEIVER \
      BSTAGE3_STAGE3_SANITY BSTAGE3_LOCK \
      BSTAGE3_RUST_LOG
    bootstrap_stage3_write_manifest || {
      echo "error: refusing Stage 3 without canonical provenance" >&2
      exit 1
    }
    echo "  Stage 3 provenance: ${stage3_provenance_manifest}"
  fi

  if [ "${stop_after_stage3}" -eq 1 ]; then
    [ "${stage3_ok:-0}" -eq 1 ] && [ -x "${stage3_bin}" ] || {
      echo "error: --stop-after-stage3 requires a successful Stage 3 compiler" >&2
      exit 2
    }
    stage3_candidate="$(bootstrap_stage3_canonical_file "$(absolute_path "${stage3_bin}")")" || {
      echo "error: Stage 3 stop candidate path is not canonical" >&2
      exit 1
    }
    bootstrap_stage3_verify_manifest \
      "$(absolute_path "${stage3_provenance_manifest}")" "${repo_root}" \
      "${stage3_candidate}" || {
      echo "error: --stop-after-stage3 refused unverified Stage 3 provenance" >&2
      exit 1
    }
    echo "Stage 3 stop complete: provenance-verified compiler ${stage3_candidate}"
    exit 0
  fi

  stage2_capability_ok=0
  stage2_capability_bin="${output_dir}/stage2-capability-${PLATFORM}${exe_suffix}"
  stage2_capability_cache="${output_dir}/stage2-capability-cache"
  rm -f "${stage2_capability_bin}"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    set +e
    env SIMPLE_BOOTSTRAP=1 \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      "${stage2_bin}" native-build \
      --target "${PLATFORM}" \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads 1 \
      --cache-dir "${stage2_capability_cache}" \
      --mode "${bootstrap_mode}" \
      --entry test/04_smoke/windows_native_hello.spl \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage2_capability_bin}" \
      >"${log_dir}/stage2-capability.log" 2>&1
    stage2_capability_status=$?
    set -e
    if [ "${stage2_capability_status}" -eq 0 ] && [ -x "${stage2_capability_bin}" ]; then
      if stage2_capability_output="$(run_timeout 30 "${stage2_capability_bin}" 2>/dev/null)"; then
        if [ "${stage2_capability_output}" = "windows native hello" ]; then
          stage2_capability_ok=1
          echo "  Stage 2 native-build capability passed"
        fi
      fi
    fi
  fi
  if [ "${stage2_capability_ok}" -ne 1 ]; then
    echo "  warning: Stage 2 native-build capability failed; using seed for stage 4" >&2
    echo "  warning: see ${log_dir}/stage2-capability.log" >&2
  fi
fi

# Locate stage outputs — check new layout first, fall back to flat
if [ -x "${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}" ]; then
  stage2="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
elif [ -x "${output_dir}/simple_stage2" ]; then
  stage2="${output_dir}/simple_stage2"
  stage3="${output_dir}/simple_stage3"
else
  stage2=""
  stage3=""
fi

if [ ! -x "${stage2}" ]; then
  echo "warning: stage2 binary was not produced; Stage 3/full CLI unavailable" >&2
  stage3_ok=0
fi

# Decide which compiler to use for stage 4
stage4_is_seed=0
if [ "${stage3_ok:-0}" -eq 1 ] && [ -x "${stage3}" ]; then
  hash2=$(hash_file "${stage2}")
  hash3=$(hash_file "${stage3}")
  echo "stage2 sha256: ${hash2}"
  echo "stage3 sha256: ${hash3}"
  if [ "${hash2}" != "${hash3}" ]; then
    echo "warning: stage2 and stage3 hashes differ (expected when runtime is embedded)"
    echo "  Using verified Stage 3 for stage 4"
  else
    echo "Bootstrap verification passed."
  fi
  stage_for_build="${stage3}"
else
  echo "Stage 3 unavailable — no provenance-verified compiler for Stage 4"
  stage_for_build=""
  stage4_is_seed=1
fi

# Fast iteration stops after the pure-Simple dynload stages. Relinking the
# complete CLI is explicit because it is the dominant cost and is unnecessary
# for ordinary compiler/app/lib edits that are consumed through dynload caches.
if [ "${full_cli}" -eq 0 ]; then
  echo "Pure-Simple dynload build complete; full CLI relink skipped."
  echo "  cache: ${native_cache_dir}"
  echo "  use --full-cli, --deploy, or --mode=one-binary to relink"
  if [ "${stage3_ok:-0}" -eq 0 ]; then
    exit 2
  fi
  exit 0
fi

if [ "${stage4_is_seed}" -eq 1 ]; then
  echo "error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback" >&2
  exit 2
fi
# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo "Stage 4: compiling full CLI (main.spl) with bootstrap compiler..."
bootstrap_progress_mark stage4-fingerprint ""
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
stage4_source_revision_before="$(stage4_source_revision "${repo_root}")" || {
  echo "error: could not fingerprint Stage 4 source authority" >&2
  exit 1
}
prepare_native_cache stage4
stage4_parent="$(bootstrap_stage3_canonical_file "$(absolute_path "${stage_for_build}")")" || {
  echo "error: Stage 4 parent compiler path is not canonical" >&2
  exit 1
}
full_bin="$(bootstrap_stage3_canonical_path "$(absolute_path "${full_dir}/simple${exe_suffix}")")" || {
  echo "error: Stage 4 output path is not canonical" >&2
  exit 1
}
rm -f "${full_bin}" "${full_bin}.provenance.env"
bootstrap_progress_mark stage4 "$(absolute_path "${log_dir}/stage4-native-build.log")"
run_logged stage4-native-build bootstrap_native_build_main \
  "${stage4_parent}" "${full_bin}"

if grep -Eq '\[stmt_get_tag\] OOB|\[flat-bridge\] missing (stmt|expr) tag' "${log_dir}/stage4-native-build.log"; then
  echo "error: Stage 4 emitted stale flat-AST index diagnostics" >&2
  exit 1
fi

if [ ! -x "${full_bin}" ]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

bootstrap_progress_mark stage4-smoke "$(absolute_path "${log_dir}/stage4-native-build.log")"
if [ -z "${resume_stage4_output}" ]; then
  install -m755 "${seed_bin}" "${full_dir}/simple_seed${exe_suffix}"
fi

stage4_smoke="$(run_timeout 30 "${full_bin}" -c 'print(1+1)' 2>/dev/null)"
if [ "${stage4_smoke}" != "2" ]; then
  echo "error: stage4 binary failed smoke test (-c 'print(1+1)' -> '${stage4_smoke}')" >&2
  exit 1
fi

# `-c` can succeed by delegating to the sibling Rust seed even when the newly
# linked full CLI cannot read or compile source files itself. MCP/LSP startup
# needs the latter, so reject such candidates before deployment.
if ! run_timeout 60 env SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    "${full_bin}" check src/app/cli/bootstrap_main.spl >/dev/null 2>&1; then
  echo "error: stage4 binary failed source-check smoke (MCP/LSP would not start)" >&2
  exit 1
fi

if ! simple_binary_is_valid "${full_bin}"; then
  echo "error: stage4 binary failed the current frontend candidate gate" >&2
  exit 1
fi

run_logged stage4-redeploy-gate run_timeout_kill 180 sh \
  scripts/check/cert/redeploy_gate/redeploy_gate.shs "${full_bin}"

run_logged stage4-essential-tools-smoke run_timeout_kill 180 env \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  sh scripts/check/check-bootstrap-essential-tools-smoke.shs

stage4_provenance="${full_bin}.provenance.env"
stage4_write_candidate_provenance \
  "${full_bin}" "${stage4_provenance}" "${repo_root}" \
  "${bootstrap_script_path}" "${stage4_parent}" \
  "$(absolute_path "${stage3_provenance_manifest}")" \
  "${stage4_source_revision_before}" "${bootstrap_script_sha256_before}" \
  "${stage4_provenance_helper_sha256_before}" \
  "$(absolute_path "${bootstrap_lock}")" \
  "$(absolute_path "${log_dir}/stage4-native-build.log")" \
  "$(absolute_path "${log_dir}/stage4-essential-tools-smoke.log")" || {
    echo "error: refusing Stage 4 without canonical candidate provenance" >&2
    exit 1
  }
stage4_verify_candidate_provenance \
  "${stage4_provenance}" "${full_bin}" "${repo_root}" || {
    echo "error: Stage 4 candidate provenance did not re-verify" >&2
    exit 1
  }
stage3_acceptance_sanity=$(bootstrap_stage3_manifest_value \
  stage3_sanity_evidence_path "${stage3_provenance_manifest}") || {
  echo "error: Stage 3 acceptance lacks its sanity receipt" >&2
  exit 1
}
bootstrap_stage3_verify_sanity_evidence_receipt \
  "${stage3_acceptance_sanity}" "${stage3}" || {
  echo "error: Stage 3 acceptance sanity receipt did not re-verify" >&2
  exit 1
}
stage3_current_acceptance_status=verified
stage3_acceptance_receipt="${full_bin}.stage3-acceptance.env"
[ ! -L "${stage3_acceptance_receipt}" ] || {
  echo "error: refusing symlinked Stage 3 acceptance receipt" >&2
  exit 1
}
stage3_acceptance_tmp="${stage3_acceptance_receipt}.tmp.$$"
{
  echo "schema=simple-bootstrap-stage3-current-acceptance-v1"
  echo "status=${stage3_current_acceptance_status}"
  echo "stage3_provenance_path=$(absolute_path "${stage3_provenance_manifest}")"
  echo "stage3_provenance_sha256=$(bootstrap_stage3_hash_file "${stage3_provenance_manifest}")"
  echo "stage3_sanity_path=${stage3_acceptance_sanity}"
  echo "stage3_sanity_sha256=$(bootstrap_stage3_hash_file "${stage3_acceptance_sanity}")"
  echo "stage4_candidate_path=${full_bin}"
  echo "stage4_candidate_sha256=$(bootstrap_stage3_hash_file "${full_bin}")"
  echo "stage4_provenance_path=${stage4_provenance}"
  echo "stage4_provenance_sha256=$(bootstrap_stage3_hash_file "${stage4_provenance}")"
  echo "completed_gate=stage4-essential-tools-smoke"
} >"${stage3_acceptance_tmp}" || exit 1
chmod 400 "${stage3_acceptance_tmp}" || exit 1
mv "${stage3_acceptance_tmp}" "${stage3_acceptance_receipt}" || exit 1
echo "  Stage 4 provenance: ${stage4_provenance}"
echo "  Stage 3 current acceptance: ${stage3_acceptance_receipt}"

echo "Stage 4b: compiling cached UI backend..."
bootstrap_progress_mark stage4b "$(absolute_path "${log_dir}/stage4b-ui-backend.log")"
ui_backend_bin="${full_dir}/simple_ui_backend${exe_suffix}"
prepare_native_cache stage4b-ui-backend
run_logged stage4b-ui-backend env RUST_LOG="${RUST_LOG:-error}" \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_STUB_MISSING_RT=1 \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  "${full_bin}" native-build \
    --backend "${backend}" \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads "${jobs}" --cache-dir "${native_cache_dir}" \
  --mode "${bootstrap_mode}" --entry src/app/ui/main.spl \
  --runtime-path "${stage_runtime_absolute}" \
  -o "${ui_backend_bin}"
[ -x "${ui_backend_bin}" ] || { echo "error: failed to compile cached UI backend" >&2; exit 1; }
echo "Full CLI binary: ${full_bin}"

# ===========================================================================
# Stage 5: Compile MCP servers (optional, skip with --no-mcp)
# ===========================================================================

mcp_build_ok=1
if [ "${build_mcp}" -eq 1 ]; then
  echo "Stage 5: compiling MCP servers..."
  bootstrap_progress_mark stage5 "$(absolute_path "${log_dir}/stage51-mcp-native-build.log")"

  # Build both servers before failing so both logs are available. The shared
  # fresh-artifact smoke below is the single fail-closed Stage 5 gate.
  mcp_stage=0
  for mcp_entry in "simple_mcp_server:src/app/mcp/main.spl" \
                    "simple_lsp_mcp_server:src/app/simple_lsp_mcp/main.spl"; do
    mcp_stage=$((mcp_stage + 1))
    mcp_name="${mcp_entry%%:*}"
    mcp_spl="${mcp_entry#*:}"
    mcp_log="stage5${mcp_stage}-mcp-native-build"

    echo "  Stage 5${mcp_stage}: ${mcp_name}"
    prepare_native_cache "stage5${mcp_stage}"
    rm -f "${full_dir}/${mcp_name}${exe_suffix}"
    set +e
    env RUST_LOG="${RUST_LOG:-error}" \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
      SIMPLE_NO_STUB_FALLBACK=1 \
      SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
      SIMPLE_BINARY="$(absolute_path "${stage_for_build}")" \
      "${stage_for_build}" native-build \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads "${jobs}" \
      --cache-dir "${native_cache_dir}" \
      --mode "${bootstrap_mode}" \
      --entry "${mcp_spl}" \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${full_dir}/${mcp_name}${exe_suffix}" \
      >"${log_dir}/${mcp_log}.log" 2>&1
    mcp_status=$?
    set -e
    echo "  ${mcp_log} log: ${log_dir}/${mcp_log}.log"
    if [ "${mcp_status}" -ne 0 ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} build failed (exit ${mcp_status})"
    elif [ ! -s "${full_dir}/${mcp_name}${exe_suffix}" ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} produced a zero-byte file"
    else
      printf '%s\n' "$(hash_file "${full_dir}/${mcp_name}${exe_suffix}")" \
        >"${full_dir}/${mcp_name}${exe_suffix}.sha256"
      echo "  ${mcp_name}: ${full_dir}/${mcp_name}${exe_suffix}"
    fi
  done

  if [ "${mcp_build_ok}" -ne 1 ]; then
    echo "error: Stage 5 MCP server build failed; refusing stale artifacts" >&2
    exit 1
  fi

  echo "Stage 5 smoke: fresh MCP initialize/list/call gate"
  if ! env \
    SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    MCP_SERVER="$(absolute_path "${full_dir}/simple_mcp_server${exe_suffix}")" \
    LSP_MCP_SERVER="$(absolute_path "${full_dir}/simple_lsp_mcp_server${exe_suffix}")" \
    MCP_NATIVE_BOOTSTRAP_FRESH=1 \
    sh scripts/check/check-mcp-native-smoke.shs; then
    echo "error: fresh Stage 5 MCP server smoke failed" >&2
    exit 1
  fi
else
  echo "Skipping MCP server builds (--no-mcp)"
fi

# ===========================================================================
# Deploy
# ===========================================================================

resume_stage4_verify_immutable || exit 1
if [ "${deploy}" -eq 1 ]; then
  bootstrap_progress_mark deploy ""
  deploy_dir="bin/release/${PLATFORM}"
  if [ -L "bin" ] || [ -L "bin/release" ]; then
    echo "ERROR: deploy refused - symlinked deployment parent" >&2
    exit 1
  fi
  mkdir -p "${deploy_dir}"
  if [ -L "${deploy_dir}" ]; then
    echo "ERROR: deploy refused - symlinked deployment directory: ${deploy_dir}" >&2
    exit 1
  fi
  deploy_lock_root="${deploy_dir}/.bootstrap-deploy-locks"
  if ! portable_lock_acquire "${deploy_lock_root}" deployment \
    "${SIMPLE_BOOTSTRAP_LOCK_WAIT_SECONDS:-30}"; then
    echo "ERROR: deploy refused - deployment is locked: ${deploy_dir}" >&2
    exit 1
  fi
  deploy_lock_handle=${PORTABLE_LOCK_HANDLE}

  # Deploy gate: never swap bin/simple to the self-hosted stage4 binary unless
  # a working seed driver exists at the delegate path. Without it the stage4
  # self-exec guard blocks `bin/simple test` host-wide (see
  # doc/08_tracking/bug/stage4_deploy_no_seed_test_runner_blocked_2026-06-11.md).
  seed_probe() {
    [ -x "$1" ] || return 1
    out="$(run_timeout 30 "$1" -c 'print(1+1)' 2>/dev/null)" || return 1
    [ "${out}" = "2" ]
  }
  if [ -z "${resume_stage4_output}" ]; then
    seed_delegate="${deploy_dir}/simple_seed${exe_suffix}"
    seed_src="${full_dir}/simple_seed${exe_suffix}"
    if ! seed_probe "${seed_src}"; then
      echo "ERROR: deploy refused — current seed driver failed smoke test: ${seed_src}." >&2
      exit 1
    fi
    install -m755 "${seed_src}" "${seed_delegate}"
    echo "Installed current seed delegate: ${seed_src} -> ${seed_delegate}"
  fi

  # Identity gate: bin/simple MUST be the pure-Simple self-hosted compiler and
  # never the Rust seed/driver (default tooling rule, .claude/rules/bootstrap.md).
  # Behavioural probes cannot tell them apart: the seed passes -c 'print(1+1)',
  # passes `test` 2-pass/1-fail, emits a .smf, and produces a running LLVM ELF.
  # Size and banner have BOTH failed as identity signals — a 154,185,152-byte
  # binary was the Rust driver while a 22,300,688-byte one was self-hosted.
  # The discriminator is a diagnostic string that only the pure-Simple compiler
  # sources carry into the emitted binary; it is absent from every Rust-driver
  # build (see src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
  # and doc/08_tracking/bug/
  # bin_simple_bootstrap_main_stage_deployed_no_subcommands_2026-08-01.md).
  selfhost_identity_marker='enum construction: unregistered enum'
  selfhost_identity_ok() {
    [ -f "$1" ] || return 1
    if command -v strings >/dev/null 2>&1; then
      strings -a "$1" 2>/dev/null | grep -q "${selfhost_identity_marker}"
    else
      grep -a -q "${selfhost_identity_marker}" "$1" 2>/dev/null
    fi
  }
  if ! selfhost_identity_ok "${full_bin}"; then
    echo "ERROR: deploy refused — Stage 4 output is not the pure-Simple self-hosted compiler." >&2
    echo "  candidate: ${full_bin}" >&2
    echo "  identity probe found no self-hosted compiler marker (absent = Rust driver)." >&2
    echo "  Refusing to install a Rust seed/driver as ${deploy_dir}/simple${exe_suffix}." >&2
    exit 1
  fi
  echo "Identity gate: Stage 4 output verified pure-Simple self-hosted"

  deployed_bin="${deploy_dir}/simple${exe_suffix}"
  prev_bin="${deploy_dir}/simple${exe_suffix}.pre_deploy"
  deploy_receipt="${deploy_dir}/bootstrap-deploy-receipt.env"
  deploy_tmp="${deploy_dir}/.simple${exe_suffix}.deploy.$$"
  receipt_tmp="${deploy_dir}/.bootstrap-deploy-receipt.$$"
  rm -f "${deploy_receipt}"
  backup_created=0
  if [ -e "${deployed_bin}" ]; then
    if [ ! -f "${deployed_bin}" ] || [ -L "${deployed_bin}" ] || \
       ! selfhost_identity_ok "${deployed_bin}" || \
       [ "$(run_timeout 30 "${deployed_bin}" -c 'print(1+1)' 2>/dev/null)" != "2" ]; then
      echo "ERROR: deploy refused - current compiler is not a safe known-good backup." >&2
      exit 1
    fi
    prev_tmp="${deploy_dir}/.simple${exe_suffix}.pre_deploy.$$"
    install -m755 "${deployed_bin}" "${prev_tmp}"
    mv "${prev_tmp}" "${prev_bin}"
    backup_created=1
  else
    rm -f "${prev_bin}"
  fi
  install -m755 "${full_bin}" "${deploy_tmp}"
  mv "${deploy_tmp}" "${deployed_bin}"
  echo "Deployed full CLI binary to ${deployed_bin}"

  # Post-swap smoke: the deployed binary must evaluate code; restore on failure.
  if smoke_out="$(run_timeout 30 "${deployed_bin}" -c 'print(1+1)' 2>/dev/null)"; then
    :
  else
    smoke_out=""
  fi
  if [ "${smoke_out}" != "2" ]; then
    echo "ERROR: deployed binary failed smoke test (-c 'print(1+1)' -> '${smoke_out}')." >&2
    if [ "${backup_created}" -eq 1 ] && [ -x "${prev_bin}" ]; then
      restore_tmp="${deploy_dir}/.simple${exe_suffix}.restore.$$"
      install -m755 "${prev_bin}" "${restore_tmp}"
      mv "${restore_tmp}" "${deployed_bin}"
      echo "Restored previous binary to ${deployed_bin}" >&2
    else
      rm -f "${deployed_bin}"
    fi
    exit 1
  fi
  install -m755 "${ui_backend_bin}" "${deploy_dir}/simple_ui_backend${exe_suffix}"
  echo "Deployed cached UI backend to ${deploy_dir}/simple_ui_backend${exe_suffix}"

  # Deploy MCP servers if they were built successfully
  if [ "${build_mcp}" -eq 1 ] && [ "${mcp_build_ok}" -eq 1 ]; then
    for mcp_bin_name in simple_mcp_server simple_lsp_mcp_server; do
      if [ -x "${full_dir}/${mcp_bin_name}${exe_suffix}" ] && [ -s "${full_dir}/${mcp_bin_name}${exe_suffix}" ]; then
        mcp_deploy_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.deploy.$$"
        mcp_hash_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.sha256.deploy.$$"
        install -m755 "${full_dir}/${mcp_bin_name}${exe_suffix}" "${mcp_deploy_tmp}"
        install -m644 "${full_dir}/${mcp_bin_name}${exe_suffix}.sha256" "${mcp_hash_tmp}"
        mv "${mcp_deploy_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}"
        mv "${mcp_hash_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}.sha256"
        echo "Deployed ${mcp_bin_name} to ${deploy_dir}/${mcp_bin_name}${exe_suffix}"
      fi
    done
  fi

  # Recreate wrapper/launcher entrypoints (bin/simple plus release links)
  if [ "${os}" != "windows" ]; then
    if ! "${repo_root}/scripts/setup/setup.shs"; then
      echo "ERROR: deployment setup failed; restoring previous compiler" >&2
      if [ "${backup_created}" -eq 1 ] && [ -x "${prev_bin}" ]; then
        restore_tmp="${deploy_dir}/.simple${exe_suffix}.setup-restore.$$"
        install -m755 "${prev_bin}" "${restore_tmp}"
        mv "${restore_tmp}" "${deployed_bin}"
      else
        rm -f "${deployed_bin}"
      fi
      exit 1
    fi
  fi

  full_hash="$(hash_file "${full_bin}")"
  current_hash="$(hash_file "${deployed_bin}")"
  if [ "${current_hash}" != "${full_hash}" ]; then
    echo "ERROR: deployed compiler hash differs from admitted Stage 4 candidate" >&2
    echo "  candidate: ${full_hash}" >&2
    echo "  deployed:  ${current_hash}" >&2
    exit 1
  fi
  backup_hash="none"
  [ "${backup_created}" -eq 1 ] && [ -f "${prev_bin}" ] && [ ! -L "${prev_bin}" ] && backup_hash="$(hash_file "${prev_bin}")"
  {
    echo "schema=bootstrap-deploy-receipt-v1"
    echo "platform=${PLATFORM}"
    echo "current_path=${deployed_bin}"
    echo "current_sha256=${current_hash}"
    echo "stage4_candidate_sha256=${full_hash}"
    echo "backup_path=${prev_bin}"
    echo "backup_sha256=${backup_hash}"
    echo "timestamp_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "deployment_status=pass"
    echo "stage3_current_acceptance_status=${stage3_current_acceptance_status}"
    echo "stage3_current_acceptance_receipt=${stage3_acceptance_receipt}"
    echo "platform_acceptance_claimed=false"
  } > "${receipt_tmp}"
  chmod 644 "${receipt_tmp}"
  mv "${receipt_tmp}" "${deploy_receipt}"
  echo "Deployment receipt: ${deploy_receipt}"

  if [ "${release_tests}" -eq 1 ]; then
    echo "Stage 6: running release whole-test gate..."
    bootstrap_progress_mark stage6 ""
    run_logged stage6-whole-tests "${deployed_bin}" test test --whole --mode=interpreter
  fi
fi

resume_stage4_finalize || exit 1

echo "Final binary: ${full_bin}"

# ===========================================================================
# Exit status — reflect self-host verification result
# ===========================================================================

# Invariant net. A stage-3 failure sets stage4_is_seed=1, which refuses the seed
# fallback and exits 2 BEFORE Stage 4 and before any deploy, so reaching this
# point with stage3_ok=0 is a control-flow regression, not a known limitation.
# The message this block used to print ("Stage 4 used the Rust seed instead of
# the self-hosted compiler") described behaviour the script no longer has, and
# reading it as live was what led a lane to believe a failed self-host could
# still deploy. Keep the exit-2 contract, but report it as the invariant break
# it would be.
if [ "${stage3_ok:-0}" -eq 0 ]; then
  echo ""
  echo "ERROR: internal invariant broken — reached completion with stage3_ok=0." >&2
  echo "  A failed self-host must have exited at the seed-fallback refusal." >&2
  echo "  Treat any binary deployed by this run as unverified." >&2
  exit 2
fi
[ "${stage3_current_acceptance_status}" = verified ] || {
  echo "ERROR: current Stage 3 acceptance was not bound to verified Stage 4 evidence." >&2
  exit 2
}

# Refresh the textual evidence consumed by the lightweight push hook only
# after every requested bootstrap phase and the Stage-3/4 acceptance binding
# have succeeded. An ad-hoc successful bootstrap therefore admits the next
# push without moving expensive compilation into the hook.
if ! sh "${repo_root}/scripts/check/check-bootstrap-must-pass.shs" \
  --record-bootstrap-success \
  --output-dir "${output_dir}" \
  --stage4-binary "${full_bin}" \
  --stage4-provenance "${full_bin}.provenance.env"; then
  echo "ERROR: bootstrap completed but mandatory-check evidence was not recorded." >&2
  exit 1
fi
bootstrap_progress_mark complete ""
