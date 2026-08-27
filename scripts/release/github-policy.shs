#!/bin/sh
# Render, verify, or explicitly apply the GitHub projection of spipe-vcs/3.
set -eu

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || exit 2
RULESET_DIR="$ROOT/.github/rulesets"
ENVIRONMENT_FILE="$ROOT/.github/release-environment.json"
REVIEW_BROKER_FILE="$ROOT/.github/review-admission-broker.json"
DEFAULT_REPO=ormastes/simple

usage() {
    echo "usage: $0 render | review-plan | verify-review RECEIPT SESSION [owner/repo] | verify-live [owner/repo] | apply-live --yes [owner/repo]" >&2
    exit 2
}

review_plan() {
    require_tools
    jq -S '{schema,configured,implementation_status,signed_receipt_protocol,status_context,github_app_integration_id,
      environment_protection_rule_app_id,planned_ruleset_required_check,
      planned_environment_custom_protection,authorized_dispatcher,ruleset_profiles,
      environments,normal_mode,fallback_mode,fallback_reason,apply_live,
      blocking_reason}' "$REVIEW_BROKER_FILE"
}

review_ruleset_for_base() {
    case $1 in
        main|integration/main) printf '%s\n' "$RULESET_DIR/spipe-vcs-v3-main.json" ;;
        release/*) printf '%s\n' "$RULESET_DIR/spipe-vcs-v3-release-lines.json" ;;
        *) echo "github-policy: unsupported protected PR base: $1" >&2; return 1 ;;
    esac
}

validate_review_receipt() {
    _receipt=$1
    _session=$2
    _repo=$3
    require_tools
    [ -f "$_receipt" ] || { echo "github-policy: review receipt is missing" >&2; return 1; }
    jq -e '
      def sha256: type == "string" and test("^[0-9a-f]{64}$");
      def sha: type == "string" and test("^[0-9a-f]{40}$");
      def timestamp: type == "string" and
        test("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$");
      def common_keys: ["audit_receipt_sha256","expires_at","head_sha","issued_at",
        "mode","pull_request_number","repository","required_checks","schema","session_id"];
      .schema == "spipe-review-admission/1" and
      (.mode == "independent_verifier" or .mode == "owner_attested_fallback") and
      (.repository | type == "string") and
      (.pull_request_number | type == "number" and . > 0) and
      (.session_id | type == "string" and test("^[A-Za-z0-9][A-Za-z0-9._/-]{0,127}$")) and
      (.head_sha | sha) and (.required_checks | type == "array" and length > 0) and
      all(.required_checks[];
        (keys | sort) == (["context","integration_id"] | sort) and
        (.context | type == "string" and length > 0) and
        (.integration_id | type == "number" and . > 0)) and
      (.issued_at | timestamp) and (.expires_at | timestamp) and
      (.audit_receipt_sha256 | sha256) and
      ((.issued_at | fromdateiso8601) <= now) and
      ((.expires_at | fromdateiso8601) > now) and
      (((.expires_at | fromdateiso8601) - (.issued_at | fromdateiso8601)) <= 86400) and
      if .mode == "independent_verifier" then
        (keys | sort) == ((common_keys + ["review_receipt_sha256","verifier"]) | sort) and
        (.review_receipt_sha256 | sha256) and
        (.verifier | keys | sort) == (["effort","identity","kind","verdict"] | sort) and
        .verifier.kind == "high_capability_model" and
        (.verifier.identity | type == "string" and length > 0) and
        (.verifier.effort as $effort |
          (["high","xhigh","max","ultra"] | index($effort) != null)) and
        .verifier.verdict == "pass"
      else
        (keys | sort) == ((common_keys + ["attestor","reason","unavailable_verifier_receipt_sha256"]) | sort) and
        .reason == "no eligible independent reviewer" and
        .attestor == {type:"User",id:2378857} and
        (.unavailable_verifier_receipt_sha256 | sha256)
      end' "$_receipt" >/dev/null || {
        echo "github-policy: invalid closed spipe-review-admission/1 receipt" >&2
        return 1
    }

    _pr=$(jq -r '.pull_request_number' "$_receipt")
    _provider_pr=$(gh api "repos/$_repo/pulls/$_pr") || return 1
    _head=$(printf '%s' "$_provider_pr" | jq -er '.head.sha') || return 1
    _base=$(printf '%s' "$_provider_pr" | jq -er '.base.ref') || return 1
    jq -e --arg repo "$_repo" --arg session "$_session" --arg head "$_head" \
      --argjson pr "$_pr" '
        .repository == $repo and .session_id == $session and
        .pull_request_number == $pr and .head_sha == $head' \
      "$_receipt" >/dev/null || {
        echo "github-policy: receipt does not match the server-resolved current PR head/session" >&2
        return 1
    }

    _ruleset=$(review_ruleset_for_base "$_base") || return 1
    _required=$(jq -cS '[.rules[] | select(.type == "required_status_checks") |
      .parameters.required_status_checks[] |
      select(.context != "SPipe Review Admission") | {context,integration_id}]' "$_ruleset")
    jq -e --argjson required "$_required" '.required_checks == $required' \
      "$_receipt" >/dev/null || {
        echo "github-policy: receipt required checks do not match the protected base projection" >&2
        return 1
    }
    _checks=$(gh api --paginate --slurp \
      "repos/$_repo/commits/$_head/check-runs?per_page=100") || return 1
    printf '%s' "$_checks" | jq -e --arg head "$_head" --argjson required "$_required" '
      [ .[].check_runs[] |
        {name,status,conclusion,head_sha,app:{id:.app.id}} ] as $runs |
      all($required[]; . as $check |
        ([ $runs[] | select(.name == $check.context and
          .app.id == $check.integration_id and .head_sha == $head and
          .status == "completed" and .conclusion == "success") ] | length) == 1)' \
      >/dev/null || {
        echo "github-policy: server-resolved PR head lacks an exact configured successful check" >&2
        return 1
    }
    printf '%s\n' "$_head"
}

require_tools() {
    command -v jq >/dev/null 2>&1 || { echo "github-policy: jq is required" >&2; exit 2; }
    command -v gh >/dev/null 2>&1 || { echo "github-policy: gh is required" >&2; exit 2; }
}

manifest_files() {
    find "$RULESET_DIR" -maxdepth 1 -type f -name 'spipe-vcs-v3-*.json' -print | LC_ALL=C sort
}

environment_files() {
    printf '%s\n' \
        "$ROOT/.github/protected-integration-environment.json" \
        "$ROOT/.github/release-environment.json" \
        "$ROOT/.github/npm-release-environment.json"
}

normalize_ruleset() {
    jq -S '
      {name,target,enforcement,conditions,rules,bypass_actors:(.bypass_actors // [])}
      | .rules |= map(
          if .type == "pull_request" then
            .parameters.dismissal_restriction //= {allowed_actors:[],enabled:false}
            | .parameters.ignore_approvals_from_contributors //= false
            | .parameters.require_extra_approval_for_unattributed_changes //= true
            | .parameters.required_reviewers //= []
          else . end)' "$1"
}

normalize_environment() {
    jq -S '{
        wait_timer:(([.protection_rules[]? | select(.type == "wait_timer") | .wait_timer] | first) // 0),
        prevent_self_review:(([.protection_rules[]? | select(.type == "required_reviewers") | .prevent_self_review] | first) // false),
        reviewers:([.protection_rules[]? | select(.type == "required_reviewers") | .reviewers[]? | {type,id:.reviewer.id}] | sort_by(.type,.id)),
        deployment_branch_policy
    }' "$1"
}

render() {
    _tmp=$(mktemp) || exit 2
    trap 'rm -f "$_tmp"' EXIT INT TERM
    for _file in $(manifest_files); do
        normalize_ruleset "$_file" >>"$_tmp"
    done
    jq -s -S '.' "$_tmp"
}

live_ruleset_by_name() {
    _repo=$1
    _name=$2
    gh api --paginate "repos/$_repo/rulesets" |
        jq -r --arg name "$_name" '.[] | select(.name == $name) | .id' |
        head -1
}

verify_live() {
    _repo=$1
    require_tools
    _fail=0
    for _file in $(manifest_files); do
        _name=$(jq -r '.name' "$_file")
        _id=$(live_ruleset_by_name "$_repo" "$_name")
        if [ -z "$_id" ]; then
            echo "github-policy: MISSING ruleset $_name" >&2
            _fail=1
            continue
        fi
        _expected=$(mktemp) || exit 2
        _actual=$(mktemp) || exit 2
        _actual_raw=$(mktemp) || exit 2
        normalize_ruleset "$_file" >"$_expected"
        gh api "repos/$_repo/rulesets/$_id" >"$_actual_raw"
        normalize_ruleset "$_actual_raw" >"$_actual"
        if ! cmp -s "$_expected" "$_actual"; then
            echo "github-policy: DRIFT ruleset $_name" >&2
            diff -u "$_expected" "$_actual" >&2 || true
            _fail=1
        else
            echo "github-policy: PASS ruleset $_name"
        fi
        rm -f "$_expected" "$_actual" "$_actual_raw"
    done
    _expected_names=$(mktemp) || exit 2
    _live_names=$(mktemp) || exit 2
    for _file in $(manifest_files); do jq -r '.name' "$_file"; done | LC_ALL=C sort >"$_expected_names"
    gh api --paginate "repos/$_repo/rulesets" |
        jq -r '.[] | .name | select(startswith("spipe-vcs-v3-"))' |
        LC_ALL=C sort >"$_live_names"
    if ! cmp -s "$_expected_names" "$_live_names"; then
        echo "github-policy: DRIFT duplicate or extra managed ruleset" >&2
        _fail=1
    fi
    rm -f "$_expected_names" "$_live_names"
    for _environment_file in $(environment_files); do
        _environment=$(basename "$_environment_file" -environment.json)
        _expected_env=$(mktemp) || exit 2
        _actual_env=$(mktemp) || exit 2
        jq -S '{wait_timer,prevent_self_review,reviewers,deployment_branch_policy}' \
            "$_environment_file" >"$_expected_env"
        if ! gh api "repos/$_repo/environments/$_environment" >"$_actual_env" 2>/dev/null; then
            echo "github-policy: MISSING environment $_environment" >&2
            _fail=1
        elif ! normalize_environment "$_actual_env" | cmp -s "$_expected_env" -; then
            echo "github-policy: DRIFT environment $_environment" >&2
            _fail=1
        else
            echo "github-policy: PASS environment $_environment"
        fi
        rm -f "$_expected_env" "$_actual_env"
    done
    _immutable=$(gh api "repos/$_repo/immutable-releases" --jq '.enabled')
    if [ "$_immutable" != true ]; then
        echo "github-policy: DRIFT immutable releases disabled" >&2
        _fail=1
    else
        echo "github-policy: PASS immutable releases"
    fi
    [ "$_fail" -eq 0 ]
}

apply_live() {
    require_tools
    echo "github-policy: live apply unsupported until an external signed review broker protocol is implemented" >&2
    exit 1
}

case ${1:-} in
    render)
        render
        ;;
    review-plan)
        review_plan
        ;;
    verify-review)
        [ "$#" -ge 3 ] || usage
        validate_review_receipt "$2" "$3" "${4:-$DEFAULT_REPO}" >/dev/null
        echo "github-policy: PASS review receipt"
        ;;
    verify-live)
        verify_live "${2:-$DEFAULT_REPO}"
        ;;
    apply-live)
        [ "${2:-}" = --yes ] || usage
        apply_live "${3:-$DEFAULT_REPO}"
        ;;
    *) usage ;;
esac
