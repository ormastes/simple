#define APP_TITLE "LLVM"
#define APP_ID "/sys/apps/llvm"
#define APP_WIDTH 544
#define APP_HEIGHT 336
#define APP_POS_X 264
#define APP_POS_Y 86

#define TOOLCHAIN_NAME "LLVM"
#define TOOLCHAIN_VERSION_PATH "/SYS/LLVMVER.TXT"
#define TOOLCHAIN_MANIFEST_PATH "/SYS/LLVMMAN.TXT"
#define TOOLCHAIN_PRIMARY_PATH "/usr/bin/clang"
#define TOOLCHAIN_SECONDARY_PATH "/usr/bin/lld"

#include "toolchain_panel_runtime.c"

#define APP_PRE_WINDOW_HOOK() toolchain_pre_window_hook("llvm")
#define APP_RUNTIME_CONTENT(argc, argv) toolchain_runtime_content(argc, argv)

#include "remote_window_runtime.c"
