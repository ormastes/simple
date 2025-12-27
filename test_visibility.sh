#!/bin/bash
# Quick test script for TUI visibility

echo "Building TUI mode..."
cargo build -p simple-driver --features tui --quiet

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo "✅ Build successful"
echo ""
echo "Manual Test Instructions:"
echo "========================="
echo ""
echo "Run: ./target/debug/simple --tui"
echo ""
echo "Then type exactly:"
echo "  if x > 0:"
echo "  <Press Enter>"
echo "  <Press Tab>"
echo "  if y > 0:"
echo "  <Press Enter>"
echo "  <Press Tab Tab>"
echo "  <Press Backspace>"
echo "  <Press Ctrl+D to exit>"
echo ""
echo "Expected to see:"
echo "  >>> if x > 0:              ← Line visible after Enter ✓"
echo "  ... ····if y > 0:          ← Dots show 4-space indent ✓"
echo "  ... ········               ← Dots show 8-space indent ✓"
echo "  ... ····                   ← After backspace (4 spaces left) ✓"
echo ""
echo "Starting TUI REPL in 3 seconds..."
sleep 3

exec ./target/debug/simple --tui
