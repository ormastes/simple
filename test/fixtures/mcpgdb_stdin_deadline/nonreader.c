/* Deliberately NOT GDB: negative-only MI setup shim. After the seven owner
 * setup commands it keeps stdin open but never reads another byte. */
#include <stdio.h>
#include <ctype.h>
#ifdef _WIN32
#include <windows.h>
#define pause_ms(n) Sleep(n)
#else
#include <unistd.h>
#define pause_ms(n) usleep((n) * 1000)
#endif
int main(void) {
    char line[8192];
    setvbuf(stdout, NULL, _IONBF, 0);
    for (int command = 0; command < 7; ++command) {
        if (!fgets(line, sizeof line, stdin)) return 2;
        size_t token = 0;
        while (isdigit((unsigned char)line[token])) ++token;
        if (!token) return 3;
        if (command == 6) printf("%.*s^done,value=\"off\"\n", (int)token, line);
        else printf("%.*s^done\n", (int)token, line);
    }
    pause_ms(30000);
    return 4; /* The bounded owner must retire us before this natural exit. */
}
