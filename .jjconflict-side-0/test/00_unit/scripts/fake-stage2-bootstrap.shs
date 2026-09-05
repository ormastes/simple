#!/usr/bin/dash
set -eu
[ "${SIMPLE_BOOTSTRAP_STAGE2_RUNNER_PRIVATE:-}" = 1 ]
[ "${SIMPLE_BOOTSTRAP_OUTER_LOCK_PROOF:-}" = descriptor-verified-v1 ]
[ "${SIMPLE_BOOTSTRAP_OUTER_LOCK_CONTROL_FD:-}" = 7 ]
IFS= read -r lock_schema <&7
IFS= read -r lock_status <&7
IFS= read -r lock_dev <&7
IFS= read -r lock_ino <&7
lock_trailer=
if IFS= read -r lock_trailer <&7 || [ -n "$lock_trailer" ]; then exit 93; fi
exec 7<&-
[ "$lock_schema" = schema=simple-stage2-lock-control-v1 ]
[ "$lock_status" = status=verified-before-fork ]
lock_dev_value=${lock_dev#lock_dev=}
lock_ino_value=${lock_ino#lock_ino=}
[ "$lock_dev_value" != "$lock_dev" ] && [ "$lock_ino_value" != "$lock_ino" ] || exit 93
case "$lock_dev_value:$lock_ino_value" in *[!0-9:]*|:*|*:|*:0) exit 93 ;; esac
[ "${SIMPLE_BOOTSTRAP_DELEGATED_REPO_ROOT:-}" = /proc/self/fd/8 ]
[ "$(CDPATH= cd -- "${SIMPLE_BOOTSTRAP_DELEGATED_REPO_ROOT}" && pwd -P)" = \
  "$(pwd -P)" ]
case "${SIMPLE_BOOTSTRAP_DELEGATED_SCRIPT_PATH:-}" in /proc/self/fd/6) ;; *) exit 92 ;; esac
[ "${SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED:-}" = 1 ]
[ "${SIMPLE_BOOTSTRAP_STAGE2_TRANSACTION_ROOT:-}" = /proc/self/fd/10 ]
[ "${SIMPLE_BOOTSTRAP_STAGE2_EVIDENCE_DIR:-}" = /proc/self/fd/10/evidence ]
for inherited_path in /proc/self/fd/*; do
  inherited_fd=${inherited_path##*/}
  case "$inherited_fd" in
    0|1|2|6|8|10|20|21|22|23|24|25|26|27|28|29|30|31|32|33|34|35|36|37|38|39|40|41|42) ;;
    3)
      # dash opens fd 3 transiently while expanding /proc/self/fd/*.  The
      # directory stream is closed before this loop body.  Admit only that
      # already-closed snapshot entry; a persistent fd 3 is inherited leakage.
      [ ! -e /proc/self/fdinfo/3 ] || {
        printf 'unexpected_fd=%s\n' "$inherited_fd" \
          >/proc/self/fd/10/evidence/fd-leak.env
        exit 98
      }
      ;;
    *)
      printf 'unexpected_fd=%s\n' "$inherited_fd" \
        >/proc/self/fd/10/evidence/fd-leak.env
      exit 98
      ;;
  esac
done
for helper_name in SESSION PLANNER_ADMISSION CACHE_POLICY JOBS_POLICY \
  PROVENANCE_FACADE PROVENANCE_AUTHORITY PROVENANCE_COMMAND PROVENANCE_SANITY \
  PROVENANCE_MANIFEST_WRITE PROVENANCE_MANIFEST_VERIFY PROVENANCE_SELF_TEST \
  PORTABLE_LOCK_ATOMIC PORTABLE_PROCESS_LOCK AUTHORITY_WIRING STAGE4_PROVENANCE \
  RESUME_STAGE4 PROGRESS_WATCH PLATFORM_DETECT CANDIDATE_FRONTEND PRESERVE_PHASE \
  STAGE2_RECEIVER STAGE_LOG COMPILER_DEADLINE; do
  eval "helper_path=\${SIMPLE_BOOTSTRAP_STAGE2_HELPER_${helper_name}:-}"
  [ -n "${helper_path}" ] || exit 99
  helper_line=
  IFS= read -r helper_line <"${helper_path}" || exit 100
  [ "${helper_line}" = immutable-stage2-helper-capsule-v1 ] || exit 100
done
[ ! -e /proc/self/fd/9 ]
[ ! -e /proc/self/fd/7 ]
[ "${SIMPLE_STAGE3_OUTER_LOCK_HELD:-}" = 1 ]
[ "${SIMPLE_BOOTSTRAP_BUILD_JOBS:-}" = 16 ]
[ "${SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS:-}" = 16 ]
[ "${SIMPLE_NO_STUB_FALLBACK:-}" = 1 ]
[ "${SIMPLE_BOOTSTRAP_STAGE2_COMPILER_WALL_MS:-}" = 500 ]
[ "$#" -eq 7 ]
[ "$1" = --full-bootstrap ]
[ "$2" = --stop-after-stage2 ]
[ "$3" = --strategy=normal ]
[ "$4" = --backend=cranelift ]
[ "$5" = --mode=dynload ]
[ "$6" = --jobs=16 ]
case "$7" in --output=/*) output=${7#--output=} ;; *) exit 91 ;; esac
[ "$output" = /proc/self/fd/10/output ]
[ -d "$output" ]
[ -d "${SIMPLE_BOOTSTRAP_STAGE2_EVIDENCE_DIR}" ]
[ -d "$HOME" ] && [ "$HOME" = /proc/self/fd/10/home ]
[ -d "$TMPDIR" ] && [ "$TMPDIR" = /proc/self/fd/10/tmp ]
[ -d "$SIMPLE_NATIVE_BUILD_CACHE_DIR" ] &&
  [ "$SIMPLE_NATIVE_BUILD_CACHE_DIR" = /proc/self/fd/10/cache ]
printf '%s\n' payload-output-v1 >"$output/payload.out"
printf '%s\n' payload-evidence-v1 >"$SIMPLE_BOOTSTRAP_STAGE2_EVIDENCE_DIR/payload.env"
printf '%s\n' payload-home-v1 >"$HOME/payload.home"
printf '%s\n' payload-tmp-v1 >"$TMPDIR/payload.tmp"
printf '%s\n' payload-cache-v1 >"$SIMPLE_NATIVE_BUILD_CACHE_DIR/payload.cache"
if [ "${FAKE_STAGE2_BEHAVIOR:-success}" = post-compiler-delay ]; then
  sleep 1
fi
if [ "${FAKE_STAGE2_BEHAVIOR:-success}" = payload-failure ]; then
  exit 17
fi
