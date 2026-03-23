#!/bin/sh
set -eu

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"

if [ "$(uname -s)" = "Darwin" ]; then
  exec "$SCRIPT_DIR/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron" "$SCRIPT_DIR" "$@"
fi

exec "$SCRIPT_DIR/node_modules/.bin/electron" "$SCRIPT_DIR" "$@"
