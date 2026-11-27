# GNU descriptor-stat Windows header admission order

Status: CLAIMED, repair owner: Codex phase2-test-runner lane. Canonical BugDB
registration remains pending; this Markdown claim is not a database write.

The one renewed GNU runner attempt on release source
8e98695970a813def06ed8ea57fc2276bd20e27c exits 1 while compiling
runtime_native.c. MinGW Clang reports undeclared FILE_ID_INFO and FileIdInfo
at runtime_fd_stat_v1.h:110 and :116. The native pipeline selected 246 objects
and 61 objectless modules. No runner executable was published or test executed.

Evidence: build/phase2-runner-renewed-20261030/runner-native-only/compile.log,
collector.sdn and rss.env. Producer a757895813b3f6e31c31dead703ee4cd3e5434df75a138bfc7ad3ffed6a885fc;
one worker, 14 GiB cap, 8 GiB reserve; native-only --mode one-binary.
Peak RSS 11284772 KiB; exit 1, not the previous SMF memory failure.

The compiler delegates to the runtime C owner correctly: retained diagnostics
identify actual C compilation, not a Simple process/FFI execution failure.
The descriptor-stat header raises _WIN32_WINNT to 0x0602, but runtime_native.c
has already included Windows headers. Header guards prevent that late change
from exposing Windows 8 file identity declarations. Establish the same
existing minimum before the translation unit's first include, while preserving
an explicitly newer minimum and the standalone header's defensive definition.

Validation: production runtime translation-unit MinGW Clang syntax check
PASS (exit 0; one existing pointer-sign warning); standalone descriptor-stat
header syntax check PASS. The existing rt_fd_stat_v1_selfcheck.c compiled
with GNU Clang/LLD, -Wall -Wextra -Werror -pedantic, then executed with exit 0
and rt_fd_stat_v1_selfcheck: PASS. Logs remain under the renewed attempt root.
Parent and small-model source reviews found no P0/P1 issue. No full runner
rebuild is allowed by the one-attempt renewal after its consumed build.
Production qualification and actual runner execution remain open; this source
repair is not an admitted runner or proof of an end-to-end fix.
