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
