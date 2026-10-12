/* Source-only native regression. Link real runtime constructors and candidate
 * provider; no synthetic tagged values or application direct host API. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern int64_t rt_string_new(const uint8_t *, uint64_t);
extern int64_t rt_term_write(int64_t);
extern int32_t rt_term_flush(void);
int main(int argc, char **argv) {
    const uint8_t raw[] = {'A',0,0xc3,0xa9,'\n','\r','\n','Z'};
    if (argc != 2) return 2;
    if (strcmp(argv[1], "raw") == 0) {
        if (rt_term_write(rt_string_new(raw, sizeof raw)) != sizeof raw) return 10;
        if (rt_term_write(rt_string_new(raw, 0)) != 0) return 11;
    } else if (strcmp(argv[1], "mixed") == 0) {
        if (fwrite("queued:", 1, 7, stdout) != 7) return 12;
        if (rt_term_write(rt_string_new(raw, sizeof raw)) != sizeof raw) return 13;
        if (fwrite("tail", 1, 4, stdout) != 4) return 14;
    } else if (strcmp(argv[1], "redirect") == 0) {
        if (!freopen("redirected.bin", "wb", stdout)) return 15;
        if (rt_term_write(rt_string_new(raw, sizeof raw)) != sizeof raw) return 16;
    } else return 3;
    return rt_term_flush() == 0 ? 0 : 17;
}
