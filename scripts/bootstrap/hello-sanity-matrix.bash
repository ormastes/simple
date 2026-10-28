#!/usr/bin/env bash
set -euo pipefail
exec sh "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)/hello-sanity-matrix.shs" "$@"
