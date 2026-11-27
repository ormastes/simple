/* Exercise the actual native HTTP owner, including socket reads and framing. */
#include "../runtime_native.c"

int main(int argc, char **argv) {
    if (argc != 2) return 64;
    int64_t status = -1;
    uint8_t *body = NULL;
    size_t length = 0;
    char error[256] = {0};
    int ok = rt_http_perform("GET", argv[1], NULL, NULL, 0, 2000,
                             &status, &body, &length,
                             NULL, NULL, NULL, NULL, error, sizeof(error));
    if (!ok) {
        fprintf(stderr, "%s\n", error);
        if (body || length || status != -1) return 3;
        return 2;
    }
    if (status != 200) { free(body); return 4; }
    if (length && fwrite(body, 1, length, stdout) != length) return 5;
    free(body);
    return 0;
}
