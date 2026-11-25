/* The dynamic loader checks the same admission receipt the build path issued.
 *
 * `provider_receipt_to_sdn` (src/app/build/targets/provider_receipt.spl)
 * records `artifact_sha256`; runtime_dynload.c reads that receipt through
 * SIMPLE_<BACKEND>_PROVIDER_RECEIPT and authenticates the provider bytes
 * against it. Pure string logic, so it runs natively on any host:
 *   clang -I src/runtime test/02_integration/runtime/gpu_provider_receipt_identity_v1.c -o t && ./t
 */
#include <stdio.h>
#include <string.h>
#include "simple_gpu_provider_receipt_v1.h"

#define SHA_A "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define SHA_B "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210"

static int failures = 0;

static void expect_digest(const char *name, const char *receipt,
        const char *digest_env, int want_ok, const char *want_hex) {
    char out[65];
    int ok = simple_gpu_receipt_expected_digest_v1(receipt, digest_env, out);
    if (ok != want_ok || (want_ok && strcmp(out, want_hex) != 0)) {
        printf("FAIL: %s (ok=%d)\n", name, ok);
        failures++;
    } else {
        printf("ok: %s\n", name);
    }
}

int main(void) {
    const char *receipt =
        "schema: \"provider_admission_receipt_v1\"\n"
        "group: \"backends_cuda\"\n"
        "artifact_sha256: \"" SHA_A "\"\n"
        "abi_version: 1\n";
    expect_digest("receipt alone supplies the expected digest", receipt, NULL, 1, SHA_A);
    expect_digest("receipt and matching digest env agree", receipt, SHA_A, 1, SHA_A);
    expect_digest("upper-case digest env still matches", receipt,
        "0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF", 1, SHA_A);
    expect_digest("digest env that disagrees with the receipt is refused", receipt, SHA_B, 0, "");
    expect_digest("receipt without artifact_sha256 is refused",
        "schema: \"provider_admission_receipt_v1\"\n", NULL, 0, "");
    expect_digest("short artifact_sha256 is refused",
        "artifact_sha256: \"0123\"\n", NULL, 0, "");
    expect_digest("non-hex artifact_sha256 is refused",
        "artifact_sha256: \"zz23456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\"\n",
        NULL, 0, "");
    expect_digest("missing receipt text is refused", NULL, SHA_A, 0, "");
    /* sdn_encode_canonical emits one inline dict, bare or quoted values. */
    expect_digest("canonical inline receipt, bare digest",
        "{abi_version: 1, artifact_sha256: " SHA_A ", group: backends_cuda}", NULL, 1, SHA_A);
    expect_digest("canonical inline receipt, quoted digest, last key",
        "{abi_version: 1, artifact_sha256: \"" SHA_A "\"}", SHA_A, 1, SHA_A);
    expect_digest("a key that only ends in artifact_sha256 is not the digest",
        "{xartifact_sha256: " SHA_A "}", NULL, 0, "");
    if (failures) return 1;
    printf("PASS: receipt identity shared with the dynamic loader\n");
    return 0;
}
