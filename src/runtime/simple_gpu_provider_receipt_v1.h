#ifndef SIMPLE_GPU_PROVIDER_RECEIPT_V1_H
#define SIMPLE_GPU_PROVIDER_RECEIPT_V1_H

/* Shared provider admission receipt identity (runtime_gpu <-> runtime_dynload).
 *
 * The build path admits a provider with `admit_provider_with_identity`
 * (src/app/build/targets/provider_receipt.spl), which writes a
 * `provider_admission_receipt_v1` SDN whose `artifact_sha256` is the SHA-256
 * of the admitted provider bytes. When SIMPLE_<BACKEND>_PROVIDER_RECEIPT
 * names that receipt, runtime_dynload.c takes the expected digest from it, so
 * the loader authenticates exactly the artifact that was admitted. A
 * SIMPLE_<BACKEND>_PROVIDER_SHA256 that disagrees with the receipt, or a
 * receipt with no valid digest, refuses the load (fail-closed). */

#include <string.h>

static inline int simple_gpu_receipt_hex_eq_v1(char a, char b) {
    if (a >= 'A' && a <= 'F') a = (char)(a - 'A' + 'a');
    if (b >= 'A' && b <= 'F') b = (char)(b - 'A' + 'a');
    return a == b;
}

/* Copies the receipt's lower-case 64-hex `artifact_sha256` into out_hex
 * (NUL-terminated). Returns 1 when the receipt carries a valid digest and
 * `digest_env` (may be NULL or empty) agrees with it; 0 otherwise. */
static inline int simple_gpu_receipt_expected_digest_v1(
        const char *receipt_text, const char *digest_env, char out_hex[65]) {
    static const char key[] = "artifact_sha256:";
    const char *p;
    size_t i;
    out_hex[0] = '\0';
    if (!receipt_text) return 0;
    for (p = strstr(receipt_text, key); p; p = strstr(p + 1, key))
        if (p == receipt_text || p[-1] == '\n' || p[-1] == '{' ||
                p[-1] == ' ' || p[-1] == ',') break;
    if (!p) return 0;
    p += sizeof(key) - 1;
    while (*p == ' ' || *p == '\t') p++;
    if (*p == '"') p++;
    for (i = 0; i < 64; i++) {
        char c = p[i];
        if (c >= 'A' && c <= 'F') c = (char)(c - 'A' + 'a');
        if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) {
            out_hex[0] = '\0';
            return 0;
        }
        out_hex[i] = c;
    }
    out_hex[64] = '\0';
    if (p[64] != '"' && p[64] != ',' && p[64] != '}' && p[64] != '\n' &&
            p[64] != '\r' && p[64] != '\0' && p[64] != ' ') {
        out_hex[0] = '\0';
        return 0;
    }
    if (digest_env && digest_env[0]) {
        if (strlen(digest_env) != 64) {
            out_hex[0] = '\0';
            return 0;
        }
        for (i = 0; i < 64; i++)
            if (!simple_gpu_receipt_hex_eq_v1(digest_env[i], out_hex[i])) {
                out_hex[0] = '\0';
                return 0;
            }
    }
    return 1;
}

#endif
