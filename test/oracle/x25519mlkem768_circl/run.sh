#!/bin/sh
set -eu
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$script_dir"
go_bin="${SIMPLE_CIRCL_GO:-}"
if [ -z "$go_bin" ] && command -v go >/dev/null 2>&1; then
  go_bin="$(go env GOPATH)/pkg/mod/golang.org/toolchain@v0.0.1-go1.24.0.linux-amd64/bin/go"
fi
if [ ! -x "$go_bin" ]; then
  echo 'ERROR: cached Go 1.24 toolchain unavailable; CIRCL oracle cannot be skipped' >&2
  exit 2
fi
go_version=$("$go_bin" version)
case "$go_version" in
  'go version go1.24.0 '*) ;;
  *)
    echo "ERROR: CIRCL oracle requires cached Go 1.24.0; found: $go_version" >&2
    exit 2
    ;;
esac

# This is deliberately a single independent external implementation check.
# Keep module resolution read-only and offline so a missing cache is a failure,
# never an implicit network download or a changed dependency graph.
exec env GOENV=off GOWORK=off GOPROXY=off GOSUMDB=off GONOSUMDB='*' \
  GOTOOLCHAIN=local GOFLAGS=-mod=readonly "$go_bin" test -count=1 ./...
