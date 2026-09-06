#!/bin/sh
# Render, verify, or explicitly apply the GitHub projection of spipe-vcs/3.
set -eu

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || exit 2
RULESET_DIR="$ROOT/.github/rulesets"
ENVIRONMENT_FILE="$ROOT/.github/release-environment.json"
DEFAULT_REPO=ormastes/simple

usage() {
    echo "usage: $0 render | verify-live [owner/repo] | apply-live --yes [owner/repo]" >&2
    exit 2
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
    _repo=$1
    require_tools
    _actor=$(gh api user --jq '.id')
    [ "$_actor" = 2378857 ] || {
        echo "github-policy: authenticated actor $_actor is not creation authority 2378857" >&2
        exit 1
    }
    for _file in $(manifest_files); do
        _name=$(jq -r '.name' "$_file")
        _id=$(live_ruleset_by_name "$_repo" "$_name")
        if [ -n "$_id" ]; then
            gh api --method PUT "repos/$_repo/rulesets/$_id" --input "$_file" >/dev/null
            echo "github-policy: updated ruleset $_name"
        else
            gh api --method POST "repos/$_repo/rulesets" --input "$_file" >/dev/null
            echo "github-policy: created ruleset $_name"
        fi
    done
    for _environment_file in $(environment_files); do
        _environment=$(basename "$_environment_file" -environment.json)
        gh api --method PUT "repos/$_repo/environments/$_environment" --input "$_environment_file" >/dev/null
        echo "github-policy: configured environment $_environment"
    done
    gh api --method PUT "repos/$_repo/immutable-releases" >/dev/null
    echo "github-policy: enabled immutable releases"
    verify_live "$_repo"
}

case ${1:-} in
    render)
        render
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
