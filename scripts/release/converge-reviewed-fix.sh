#!/bin/sh
# Prepare one reviewed main/release fix in an isolated branch and worktree.
set -eu

usage() {
    cat >&2 <<'EOF'
usage: converge-reviewed-fix.sh \
  --direction main-to-release|release-to-main \
  --release-line X.Y --commit 40-hex-sha \
  --review-receipt FILE --change-id ID --work-id ID --session-id ID \
  [--adaptation-reason none|TOKEN] \
  [--remote origin] [--worktree-root DIR] [--receipt FILE]

The command fetches the exact remote source and target heads before creating a
private work/* branch and linked worktree.  It never pushes or updates main or
release/*.
EOF
    exit 2
}

fail() {
    echo "converge-reviewed-fix: $*" >&2
    exit 1
}

value=
take_value() {
    [ "$#" -ge 2 ] || usage
    value=$2
}

direction=
release_line=
source_commit=
review_receipt=
work_id=
change_id=
adaptation_reason=none
session_id=
remote=origin
worktree_root=
receipt_path=

while [ "$#" -gt 0 ]; do
    case $1 in
        --direction) take_value "$@"; direction=$value; shift 2 ;;
        --direction=*) direction=${1#*=}; shift ;;
        --release-line) take_value "$@"; release_line=$value; shift 2 ;;
        --release-line=*) release_line=${1#*=}; shift ;;
        --commit) take_value "$@"; source_commit=$value; shift 2 ;;
        --commit=*) source_commit=${1#*=}; shift ;;
        --review-receipt) take_value "$@"; review_receipt=$value; shift 2 ;;
        --review-receipt=*) review_receipt=${1#*=}; shift ;;
        --work-id) take_value "$@"; work_id=$value; shift 2 ;;
        --work-id=*) work_id=${1#*=}; shift ;;
        --change-id) take_value "$@"; change_id=$value; shift 2 ;;
        --change-id=*) change_id=${1#*=}; shift ;;
        --adaptation-reason) take_value "$@"; adaptation_reason=$value; shift 2 ;;
        --adaptation-reason=*) adaptation_reason=${1#*=}; shift ;;
        --session-id) take_value "$@"; session_id=$value; shift 2 ;;
        --session-id=*) session_id=${1#*=}; shift ;;
        --remote) take_value "$@"; remote=$value; shift 2 ;;
        --remote=*) remote=${1#*=}; shift ;;
        --worktree-root) take_value "$@"; worktree_root=$value; shift 2 ;;
        --worktree-root=*) worktree_root=${1#*=}; shift ;;
        --receipt) take_value "$@"; receipt_path=$value; shift 2 ;;
        --receipt=*) receipt_path=${1#*=}; shift ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

case $release_line in
    ''|*[!0-9.]*|.*|*.|*.*.*) fail "release line must be X.Y" ;;
esac
major=${release_line%%.*}
minor=${release_line#*.}
case $major:$minor in
    ''|*:|*[!0-9:]*) fail "release line must be X.Y" ;;
esac
case $source_commit in
    [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]* ) ;;
    *) fail "commit must be a lowercase 40-hex SHA" ;;
esac
[ "${#source_commit}" -eq 40 ] || fail "commit must be a lowercase 40-hex SHA"
case $source_commit in *[!0-9a-f]*) fail "commit must be a lowercase 40-hex SHA" ;; esac
case $work_id in ''|*[!a-zA-Z0-9.-]*) fail "invalid work ID" ;; esac
case $change_id in ''|*[!a-zA-Z0-9.-]*) fail "invalid change ID" ;; esac
case $adaptation_reason in ''|*[!a-zA-Z0-9._-]*) fail "invalid adaptation reason token" ;; esac
case $session_id in ''|*[!a-zA-Z0-9.-]*) fail "invalid session ID" ;; esac
case $remote in ''|*[!a-zA-Z0-9._-]*) fail "invalid remote name" ;; esac
[ -f "$review_receipt" ] || fail "review receipt is missing"

root=$(git rev-parse --show-toplevel 2>/dev/null) || fail "not in a Git worktree"
root=$(CDPATH= cd -- "$root" && pwd -P)
[ -z "$(git -C "$root" status --porcelain --untracked-files=normal)" ] ||
    fail "coordinator worktree is dirty; refusing shared-state preparation"
git -C "$root" remote get-url "$remote" >/dev/null 2>&1 || fail "remote does not exist: $remote"

review_snapshot=$(mktemp) || exit 2
trap 'rm -f "$review_snapshot"' EXIT INT TERM
cp "$review_receipt" "$review_snapshot" || fail "cannot snapshot review receipt"
chmod a-w "$review_snapshot" || fail "cannot seal review receipt snapshot"

# Until the canonical Simple SDN parser is available as an admitted release
# tool, accept only this closed, ordered review-receipt projection.  This is a
# typed object check, not a global key scrape; extra mappings/fields fail.
awk -v commit="$source_commit" -v change="$change_id" '
  BEGIN {
    expected[1] = "review:"
    expected[2] = "  schema: spipe-review-receipt/1"
    expected[3] = "  source_commit_sha: " commit
    expected[4] = "  change_id: " change
    expected[5] = "  kind: fix"
    expected[6] = "  verdict: approved"
  }
  { if ($0 != expected[NR]) exit 2 }
  END { if (NR != 6) exit 2 }
' "$review_snapshot" || fail "review receipt is not the closed spipe-review-receipt/1 projection"

sha256_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    elif command -v sha256 >/dev/null 2>&1; then
        sha256 -q "$1"
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    else
        return 1
    fi
}
review_sha256=$(sha256_file "$review_snapshot") || fail "no SHA-256 tool is available"

case $direction in
    main-to-release)
        source_branch=main
        target_branch="release/$release_line"
        kind=backport
        ;;
    release-to-main)
        source_branch="release/$release_line"
        target_branch=main
        kind=forwardport
        ;;
    *) fail "direction must be main-to-release or release-to-main" ;;
esac

common_dir=$(git -C "$root" rev-parse --git-common-dir)
case $common_dir in /*) ;; *) common_dir="$root/$common_dir" ;; esac
common_dir=$(CDPATH= cd -- "$common_dir" && pwd -P)
ref_base="refs/spipe/convergence/$session_id"
created=0
branch_created=0
keep_worktree=0
receipt_tmp=
worktree=
branch=
cleanup_refs() {
    git --git-dir="$common_dir" update-ref -d "$ref_base/source" >/dev/null 2>&1 || true
    git --git-dir="$common_dir" update-ref -d "$ref_base/target" >/dev/null 2>&1 || true
}
cleanup_all() {
    _status=$1
    trap - EXIT INT TERM
    cleanup_refs
    rm -f "$review_snapshot"
    [ -z "$receipt_tmp" ] || rm -f "$receipt_tmp"
    if [ "$created" -eq 1 ] && [ "$keep_worktree" -eq 0 ]; then
        git -C "$worktree" cherry-pick --abort >/dev/null 2>&1 || true
        if [ -e "$worktree" ] &&
           ! git -C "$root" worktree remove --force "$worktree" >/dev/null 2>&1; then
            echo "converge-reviewed-fix: cleanup incomplete; inspect $worktree" >&2
            _status=1
        fi
        if [ "$branch_created" -eq 1 ] &&
           ! git --git-dir="$common_dir" branch -D "$branch" >/dev/null 2>&1; then
            echo "converge-reviewed-fix: cleanup incomplete; inspect branch $branch" >&2
            _status=1
        fi
    fi
    exit "$_status"
}
trap 'cleanup_all $?' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# This bounded fetch is deliberately the first repository mutation.  Source
# selection, branch creation, and cherry-pick all consume these exact snapshots.
git -C "$root" fetch --no-tags "$remote" \
    "+refs/heads/$source_branch:$ref_base/source" \
    "+refs/heads/$target_branch:$ref_base/target" >/dev/null ||
    fail "fresh source/target fetch failed"
source_tip=$(git --git-dir="$common_dir" rev-parse "$ref_base/source^{commit}")
target_tip=$(git --git-dir="$common_dir" rev-parse "$ref_base/target^{commit}")
git --git-dir="$common_dir" merge-base --is-ancestor "$source_commit" "$source_tip" ||
    fail "selected commit is not reachable from freshly fetched $source_branch"
if git --git-dir="$common_dir" merge-base --is-ancestor "$source_commit" "$target_tip"; then
    fail "selected commit is already an ancestor of freshly fetched $target_branch"
fi

short=$(printf '%s' "$source_commit" | cut -c1-12)
branch="work/$kind/$release_line-$work_id-$session_id-$short"
git --git-dir="$common_dir" show-ref --verify --quiet "refs/heads/$branch" &&
    fail "work branch already exists: $branch"
if [ -z "$worktree_root" ]; then
    worktree_parent=$(dirname "$root")
    worktree_parent=$(CDPATH= cd -- "$worktree_parent" && pwd -P)
    worktree_root=$worktree_parent/.worktrees
    [ ! -L "$worktree_root" ] || fail "default worktree root must not be a symlink"
    mkdir -p "$worktree_root"
else
    [ -d "$worktree_root" ] || fail "explicit worktree root must already exist"
    [ ! -L "$worktree_root" ] || fail "worktree root must not be a symlink"
fi
case $worktree_root in
    /*) ;;
    *) fail "worktree root must be an absolute path outside the coordinator worktree" ;;
esac
case $worktree_root in *[!a-zA-Z0-9/._-]*) fail "worktree root contains unsupported receipt characters" ;; esac
case "$worktree_root/" in
    "$root/"*) fail "worktree root must not be inside the coordinator worktree" ;;
esac
worktree_root=$(CDPATH= cd -- "$worktree_root" && pwd -P)
case "$worktree_root/" in
    "$root/"*) fail "resolved worktree root must not be inside the coordinator worktree" ;;
esac
case "$worktree_root/" in "$common_dir/"*) fail "worktree root must not be inside Git administration data" ;; esac
git -C "$root" worktree list --porcelain | sed -n 's/^worktree //p' |
while IFS= read -r registered_worktree; do
    [ -d "$registered_worktree" ] || continue
    registered_worktree=$(CDPATH= cd -- "$registered_worktree" && pwd -P)
    case "$worktree_root/" in
        "$registered_worktree/"*) fail "worktree root is inside a registered worktree" ;;
    esac
done
worktree="$worktree_root/$session_id-$kind-$short"
[ ! -e "$worktree" ] || fail "worktree path already exists: $worktree"

git --git-dir="$common_dir" branch "$branch" "$target_tip" ||
    fail "could not create isolated work branch"
branch_created=1
created=1
git -C "$root" worktree add "$worktree" "$branch" >/dev/null ||
    fail "could not create isolated worktree"
if ! git -C "$worktree" cherry-pick "$source_commit" >/dev/null; then
    fail "reviewed commit conflicts with target; aborting isolated preparation"
fi
result_commit=$(git -C "$worktree" rev-parse HEAD)
result_tree=$(git -C "$worktree" rev-parse 'HEAD^{tree}')
patch_id=$(git -C "$worktree" show "$source_commit" --pretty=format: --no-ext-diff |
    git patch-id --stable | awk '{print $1}')
if [ -z "$receipt_path" ]; then
    receipt_relative="build/session/$session_id/receipts/reviewed-fix-preparation.sdn"
else
    case $receipt_path in
        /*|..|../*|*/../*|*/..) fail "receipt path must stay inside the new worktree" ;;
    esac
    receipt_relative=$receipt_path
fi
receipt_cursor=$worktree
old_ifs=$IFS
IFS=/
for receipt_component in $receipt_relative; do
    IFS=$old_ifs
    receipt_cursor=$receipt_cursor/$receipt_component
    [ ! -L "$receipt_cursor" ] || fail "receipt path traverses a symlink"
    IFS=/
done
IFS=$old_ifs
receipt_path=$worktree/$receipt_relative
receipt_dir=$(dirname "$receipt_path")
mkdir -p "$receipt_dir"
receipt_dir=$(CDPATH= cd -- "$receipt_dir" && pwd -P)
case "$receipt_dir/" in "$worktree/"*) ;; *) fail "resolved receipt path escapes the worktree" ;; esac
receipt_path=$receipt_dir/$(basename "$receipt_path")
[ ! -e "$receipt_path" ] || fail "receipt already exists: $receipt_path"
receipt_tmp=$(mktemp "$receipt_path.tmp.XXXXXX") || fail "cannot create receipt staging file"
cat >"$receipt_tmp" <<EOF
reviewed_fix_preparation:
  schema: spipe-reviewed-fix-preparation/1
  status: prepared
  direction: $direction
  kind: fix
  adaptation_reason: $adaptation_reason
  source_ref: refs/heads/$source_branch
  source_tip_sha: $source_tip
  source_commit_sha: $source_commit
  target_ref: refs/heads/$target_branch
  target_tip_sha: $target_tip
  review_receipt_sha256: $review_sha256
  change_id: $change_id
  patch_id: $patch_id
  session_id: $session_id
  work_id: $work_id
  work_branch: $branch
  worktree: $worktree
  result_commit_sha: $result_commit
  result_tree_sha: $result_tree
  protected_ref_updated: false
  pushed: false
  next_authority: pull_request_or_integration_queue
EOF
chmod a-w "$receipt_tmp" || fail "cannot seal preparation receipt"

# Hard-link publication is create-once on the same filesystem.  An existing
# receipt is never truncated or replaced.
ln "$receipt_tmp" "$receipt_path" || fail "receipt publication raced or target exists"
rm -f "$receipt_tmp"
receipt_tmp=

keep_worktree=1
cleanup_refs
rm -f "$review_snapshot"
trap - EXIT INT TERM
printf '%s\n' \
    "status=prepared" \
    "branch=$branch" \
    "worktree=$worktree" \
    "result_commit=$result_commit" \
    "receipt=$receipt_path"
