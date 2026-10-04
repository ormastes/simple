/* Link against each actual runtime provider; never replace rt_file_lock here. */
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern int64_t rt_file_lock(const uint8_t *, uint64_t, int64_t);
extern _Bool rt_file_unlock(int64_t);
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    if (!strcmp(argv[1], "child")) { Sleep(20000); return 0; }
    int64_t held = rt_file_lock((const uint8_t *)argv[2], strlen(argv[2]), 1);
    if (held < 0) return 3;
    if (!strcmp(argv[1], "acquire")) {
        if (!rt_file_unlock(held)) return 4;
        puts("ACQUIRED"); return 0;
    }
    if (strcmp(argv[1], "parent")) { rt_file_unlock(held); return 2; }
    char self[MAX_PATH], command[2 * MAX_PATH + 64];
    DWORD count = GetModuleFileNameA(NULL, self, sizeof(self));
    if (!count || count >= sizeof(self)) return 5;
    if (snprintf(command, sizeof(command), "\"%s\" child \"%s\"", self, argv[2]) >= sizeof(command)) return 5;
    STARTUPINFOA startup = {0}; PROCESS_INFORMATION child = {0};
    startup.cb = sizeof(startup);
    /* Deliberately request inherited handles: only the lock must not inherit. */
    if (!CreateProcessA(NULL, command, NULL, NULL, TRUE, CREATE_NO_WINDOW, NULL, NULL, &startup, &child)) return 6;
    printf("LOCKED CHILD=%lu\n", (unsigned long)child.dwProcessId); fflush(stdout);
    CloseHandle(child.hThread); CloseHandle(child.hProcess);
    Sleep(20000); rt_file_unlock(held); return 0;
}
