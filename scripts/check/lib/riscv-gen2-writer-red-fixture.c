#include <errno.h>
#include <stdio.h>
#include <string.h>

#define DENIED_WRITE_EXIT 41
#define DENIED_RENAME_EXIT 42
#define UNEXPECTED_IO_EXIT 3

int main(int argc, char **argv) {
    FILE *file;
    if (argc == 3 && strcmp(argv[1], "write") == 0) {
        file = fopen(argv[2], "wb");
        if (file == NULL)
            return errno == EACCES ? DENIED_WRITE_EXIT : UNEXPECTED_IO_EXIT;
        if (fputs("fixture\n", file) < 0 || fclose(file) != 0)
            return UNEXPECTED_IO_EXIT;
        return 0;
    }
    if (argc == 4 && strcmp(argv[1], "rename") == 0) {
        if (rename(argv[2], argv[3]) == 0) return 0;
        return errno == EACCES ? DENIED_RENAME_EXIT : UNEXPECTED_IO_EXIT;
    }
    return 2;
}
