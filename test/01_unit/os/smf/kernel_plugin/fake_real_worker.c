#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int field(const char *line, int wanted, char *out, size_t cap) {
    int current = 0;
    const char *start = line;
    for (const char *cursor = line;; ++cursor) {
        if (*cursor == '|' || *cursor == '\n' || *cursor == '\0') {
            if (current == wanted) {
                size_t size = (size_t)(cursor - start);
                if (size + 1 > cap) return 0;
                memcpy(out, start, size);
                out[size] = '\0';
                return 1;
            }
            if (*cursor != '|') return 0;
            current++;
            start = cursor + 1;
        }
    }
}

static void respond(const char *line, int kind) {
    char version[32], generation[32], session[32], slot[32], epoch[32], caps[32];
    if (!field(line, 1, version, sizeof version) ||
        !field(line, 3, generation, sizeof generation) ||
        !field(line, 4, session, sizeof session) ||
        !field(line, 5, slot, sizeof slot) ||
        !field(line, 6, epoch, sizeof epoch) ||
        !field(line, 7, caps, sizeof caps)) exit(41);
    printf("KPFW1|%s|%d|%s|%s|%s|%s|%s|0|x\n",
           version, kind, generation, session, slot, epoch, caps);
    fflush(stdout);
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "normal";
    char line[1024];
    if (!fgets(line, sizeof line, stdin)) return 40;
    if (!strncmp(mode, "crash", 5)) return 23;
    if (!strncmp(mode, "timeout", 7)) {
        sleep(30);
        return 24;
    }
    if (!strncmp(mode, "malformed", 9)) {
        puts("not-a-kpf-frame");
        fflush(stdout);
        return 25;
    }
    respond(line, 1);
    while (fgets(line, sizeof line, stdin)) {
        char kind[32];
        if (!field(line, 2, kind, sizeof kind)) return 42;
        if (!strcmp(kind, "2")) respond(line, 3);
        else if (!strcmp(kind, "5")) respond(line, 6);
        else if (!strcmp(kind, "7")) {
            respond(line, 8);
            return 0;
        }
    }
    return 43;
}
