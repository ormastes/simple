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
exec env GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local "$go_bin" test ./...
