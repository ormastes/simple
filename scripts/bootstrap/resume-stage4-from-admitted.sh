#!/bin/sh
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
  jobs_receipt=$(bootstrap_stage3_canonical_file \
    "$(bootstrap_stage3_manifest_value stage3_jobs_receipt_path "$manifest")") || return 1
  jobs_receipt_sha=$(bootstrap_stage3_manifest_value \
    stage3_jobs_receipt_sha256 "$manifest") || return 1
  [ "$(bootstrap_stage3_hash_file "$jobs_receipt")" = "$jobs_receipt_sha" ] || {
    echo "error: admitted Stage 3 effective jobs receipt hash changed" >&2
    return 1
  }
  admitted_jobs=$(bootstrap_stage3_manifest_value \
    stage3_jobs_effective "$manifest") || return 1
  bootstrap_build_jobs_verify_receipt "$jobs_receipt" "$admitted_jobs" || {
    echo "error: admitted Stage 3 effective jobs receipt did not verify" >&2
    return 1
  }
  case "${bootstrap_build_jobs_source:-default}" in
    default)
      jobs=$admitted_jobs
      selfhost_jobs=$admitted_jobs
      bootstrap_build_jobs_effective=$admitted_jobs
      ;;
    env|cli)
      [ "$jobs" = "$admitted_jobs" ] || {
        echo "error: explicit Stage 4 jobs do not match admitted Stage 3 jobs" >&2
        return 1
      }
      ;;
    *) return 1 ;;
  esac
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
  identity="${receipt}.current-tree.$$"; resume_stage4_work=$identity
  stage4_write_current_tree_identity "$identity" "$root" || return 1
  stage4_verify_stage3_identity_fields "$identity" "$manifest" "$root" || return 1
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
    echo lineage_path="${scheduler_lineage_admission:?scheduler lineage is required}"
    echo lineage_sha256="${scheduler_lineage_sha256:?scheduler lineage hash is required}"
    echo bootstrap_lock_path="$lock"
    echo bootstrap_lock_owner_pid="$$"
    echo build_jobs_effective="$jobs"
    echo build_jobs_receipt_path="$jobs_receipt"
    echo build_jobs_receipt_sha256="$jobs_receipt_sha"
    echo immutable_snapshot_path="$resume_stage4_before"
    echo immutable_snapshot_sha256="$(bootstrap_stage3_hash_file "$resume_stage4_before")"
    echo repository_root="$(bootstrap_stage3_manifest_value repository_root "$identity")"
    echo source_revision_kind="$(bootstrap_stage3_manifest_value source_revision_kind "$identity")"
    echo source_revision="$(bootstrap_stage3_manifest_value source_revision "$identity")"
    echo source_roots="$(bootstrap_stage3_manifest_value source_roots "$identity")"
    echo stage3_source_snapshot_sha256="$(bootstrap_stage3_manifest_value stage3_source_snapshot_sha256 "$identity")"
    echo git_state_sha256="$(bootstrap_stage3_manifest_value git_state_sha256 "$identity")"
    echo git_head="$(bootstrap_stage3_manifest_value git_head "$identity")"
    echo git_dirty_fingerprint="$(bootstrap_stage3_manifest_value git_dirty_fingerprint "$identity")"
    echo stage3_producer_path="$(bootstrap_stage3_manifest_value stage3_producer_path "$identity")"
    echo stage3_producer_sha256="$(bootstrap_stage3_manifest_value stage3_producer_sha256 "$identity")"
  } >"${receipt}.tmp.$$"
  mv "${receipt}.tmp.$$" "$receipt"
  rm -f "$identity"; resume_stage4_work=
  STAGE4_CONTINUATION_RECEIPT=$receipt
  export STAGE4_CONTINUATION_RECEIPT
}

resume_stage4_verify_immutable() {
  [ -n "${resume_stage4_before:-}" ] || return 0
  current_manifest=$(bootstrap_stage3_canonical_file \
    "$(bootstrap_stage3_manifest_value stage3_provenance_path "$resume_stage4_receipt")") || return 1
  stage4_verify_current_tree_identity "$resume_stage4_receipt" "$repo_root" || {
    echo "error: current source/tree identity no longer matches Stage 4 continuation" >&2; return 1;
  }
  stage4_verify_stage3_identity_fields \
    "$resume_stage4_receipt" "$current_manifest" "$repo_root" || {
    echo "error: Stage 3 producer/source identity no longer matches Stage 4 continuation" >&2; return 1;
  }
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
  [ -f "$full_bin" ] && [ ! -L "$full_bin" ] &&
    [ -f "${full_bin}.provenance.env" ] && [ ! -L "${full_bin}.provenance.env" ] || return 1
  tmp="${resume_stage4_receipt}.tmp.$$"; resume_stage4_work=$tmp
  sed 's/^status=prepared$/status=pass/' "$resume_stage4_receipt" >"$tmp" || return 1
  {
    echo immutable_status=pass
    echo immutable_after_path="$after"
    echo immutable_after_sha256="$(bootstrap_stage3_hash_file "$after")"
    echo stage4_output_sha256="$(bootstrap_stage3_hash_file "$full_bin")"
    echo stage4_provenance_sha256="$(bootstrap_stage3_hash_file "${full_bin}.provenance.env")"
    echo stage4_output_path="$full_bin"
    echo stage4_provenance_path="${full_bin}.provenance.env"
  } >>"$tmp" || return 1
  if [ "${SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE:-0}" = 1 ]; then
    [ "${deploy:-0}" -eq 0 ] || return 1
    echo publication_status=quarantined >>"$tmp" || return 1
    echo deploy_receipt_path=not-published >>"$tmp" || return 1
    echo deploy_receipt_sha256=not-published >>"$tmp" || return 1
  else
    deploy_receipt="$repo_root/bin/release/$PLATFORM/bootstrap-deploy-receipt.env"
    [ -f "$deploy_receipt" ] && [ ! -L "$deploy_receipt" ] || return 1
    echo publication_status=deployed >>"$tmp" || return 1
    echo deploy_receipt_path="$deploy_receipt" >>"$tmp" || return 1
    echo deploy_receipt_sha256="$(bootstrap_stage3_hash_file "$deploy_receipt")" >>"$tmp" || return 1
  fi
  mv "$tmp" "$resume_stage4_receipt"; resume_stage4_work=
}
