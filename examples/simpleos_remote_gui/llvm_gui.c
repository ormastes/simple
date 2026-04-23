#define APP_TITLE "LLVM"
#define APP_ID "/sys/apps/llvm"
#define APP_CONTENT \
    "LLVM\n\n" \
    "[Toolchain]\n" \
    "Inspect IR lowering and native backend readiness.\n\n" \
    "[Pipeline]\n" \
    "IR -> optimize -> object\n" \
    "Target triple: x86_64-simpleos\n\n" \
    "[Operator]\n" \
    "Track backend status here before swapping in a full native LLVM payload."
#define APP_WIDTH 544
#define APP_HEIGHT 336
#define APP_POS_X 264
#define APP_POS_Y 86
#include "remote_window_runtime.c"
