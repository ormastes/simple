#define APP_TITLE "Rust"
#define APP_ID "/sys/apps/rust"
#define APP_CONTENT \
    "Rust\n\n" \
    "[Workspace]\n" \
    "Review crate build state for remote tool integration.\n\n" \
    "[Cargo Pass]\n" \
    "Profile: dev\n" \
    "Outputs: binary, deps, metadata\n\n" \
    "[Operator]\n" \
    "Use this panel to validate Rust-side packaging and tool launch wiring."
#define APP_WIDTH 536
#define APP_HEIGHT 332
#define APP_POS_X 308
#define APP_POS_Y 102
#include "remote_window_runtime.c"
