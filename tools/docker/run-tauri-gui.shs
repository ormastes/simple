#!/bin/bash
# Start virtual display + VNC server + Tauri app
set -e

ENTRY_FILE="${1:-examples/ui/test_render.spl}"

echo "[gui-container] Starting Xvfb on :99..."
Xvfb :99 -screen 0 1280x720x24 &
sleep 1

echo "[gui-container] Starting VNC server on port 5900..."
x11vnc -display :99 -forever -nopw -rfbport 5900 &
sleep 1

echo "[gui-container] Starting Tauri shell..."
echo "[gui-container] Entry file: $ENTRY_FILE"
echo "[gui-container] Connect VNC viewer to localhost:5900 to see the window"

cd /app
export WEBKIT_DISABLE_DMABUF_RENDERER=1
exec dbus-run-session -- \
    ./tools/tauri-shell/src-tauri/target/debug/simple-tauri-shell \
    ./bin/simple "$ENTRY_FILE"
