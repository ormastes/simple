#define APP_TITLE "Simple Loader"
#define APP_ID "/sys/apps/simple_loader"
#define APP_CONTENT \
    "Simple Loader\n\n" \
    "[Launch Plan]\n" \
    "Resolve app path, manifest, and remote entry image.\n\n" \
    "[Checks]\n" \
    "Metadata: OK\n" \
    "Window join: pending compositor attach\n\n" \
    "[Operator]\n" \
    "Use this shell to inspect app startup routing before execution begins."
#define APP_WIDTH 552
#define APP_HEIGHT 344
#define APP_POS_X 220
#define APP_POS_Y 124
#include "remote_window_runtime.c"
