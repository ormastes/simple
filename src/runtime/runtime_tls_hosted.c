/*
 * Hosted TLS/web ABI supplement.
 *
 * This translation unit is intentionally separate from runtime.c: it is
 * linked only into the hosted web runtime capsule. RSA decryption and random
 * bytes require the selected OpenSSL provider; there is no stub or weak
 * fallback in this file.
 *
 * Returned strings are malloc-owned and NUL terminated, matching the legacy
 * C-string ABI consumed by the hosted Simple runtime.
 */

#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/opensslv.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
#include <openssl/core_names.h>
#include <openssl/params.h>
#endif

const char *rt_byte_char(int64_t value) {
    char *result = (char *)malloc(2);
    if (!result) return NULL;
    result[0] = (char)(unsigned char)(value & 0xff);
    result[1] = '\0';
    return result;
}

int64_t rt_random_i64(void) {
    int64_t result;
    if (RAND_bytes((unsigned char *)&result, (int)sizeof(result)) != 1) {
        /* The ABI has no recoverable error channel. Never return weak or
         * predictable bytes when the system CSPRNG fails. */
        abort();
    }
    return result;
}

const char *rt_rsa_decrypt_with_len(const char *ciphertext, int64_t ct_len,
                                    const char *private_key_pem, int64_t pk_len,
                                    int64_t *out_len) {
    BIO *key_bio = NULL;
    EVP_PKEY *private_key = NULL;
    EVP_PKEY_CTX *context = NULL;
    unsigned char *plaintext = NULL;
    char *empty = NULL;
    const char *result = NULL;
    size_t plaintext_len = 0;
    size_t ciphertext_len;
    size_t key_len;

    if (out_len) *out_len = 0;

    if (!ciphertext || !private_key_pem || ct_len <= 0 || pk_len <= 0) goto done;
    ciphertext_len = (size_t)ct_len;
    key_len = (size_t)pk_len;
    if (ciphertext_len == 0 || ciphertext_len > INT_MAX ||
        key_len == 0 || key_len > INT_MAX) {
        goto done;
    }

    key_bio = BIO_new_mem_buf(private_key_pem, (int)key_len);
    if (!key_bio) goto done;
    private_key = PEM_read_bio_PrivateKey(key_bio, NULL, NULL, NULL);
    if (!private_key) goto done;

    context = EVP_PKEY_CTX_new(private_key, NULL);
    if (!context || EVP_PKEY_decrypt_init(context) <= 0 ||
        EVP_PKEY_CTX_set_rsa_padding(context, RSA_PKCS1_PADDING) <= 0) {
        goto done;
    }
#if defined(OSSL_ASYM_CIPHER_PARAM_IMPLICIT_REJECTION)
    {
        unsigned int implicit_rejection = 0;
        OSSL_PARAM params[] = {
            OSSL_PARAM_construct_uint(OSSL_ASYM_CIPHER_PARAM_IMPLICIT_REJECTION,
                                      &implicit_rejection),
            OSSL_PARAM_construct_end()
        };
        /* OpenSSL 3.2+ defaults to implicit rejection for PKCS#1 v1.5
         * decryption. That can return synthetic plaintext on bad padding,
         * which this legacy ABI cannot distinguish from real plaintext. Keep
         * explicit-error behavior; if the provider cannot honor it, fail. */
        if (EVP_PKEY_CTX_set_params(context, params) <= 0) goto done;
    }
#endif

    if (EVP_PKEY_decrypt(context, NULL, &plaintext_len,
                         (const unsigned char *)ciphertext,
                         ciphertext_len) <= 0 ||
        plaintext_len == SIZE_MAX) {
        goto done;
    }

    plaintext = (unsigned char *)malloc(plaintext_len + 1);
    if (!plaintext) goto done;
    if (EVP_PKEY_decrypt(context, plaintext, &plaintext_len,
                         (const unsigned char *)ciphertext,
                         ciphertext_len) <= 0 ||
        plaintext_len == SIZE_MAX) {
        goto done;
    }
    plaintext[plaintext_len] = '\0';
    result = (const char *)plaintext;
    plaintext = NULL;
    if (out_len) *out_len = (int64_t)plaintext_len;

done:
    free(plaintext);
    EVP_PKEY_CTX_free(context);
    EVP_PKEY_free(private_key);
    BIO_free(key_bio);
    if (!result) {
        empty = (char *)malloc(1);
        if (!empty) return NULL;
        empty[0] = '\0';
        result = empty;
    }
    return result;
}

const char *rt_rsa_decrypt(const char *ciphertext,
                           const char *private_key_pem) {
    if (!ciphertext || !private_key_pem) {
        char *empty = (char *)malloc(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    return rt_rsa_decrypt_with_len(ciphertext, (int64_t)strlen(ciphertext),
                                   private_key_pem,
                                   (int64_t)strlen(private_key_pem), NULL);
}

static int hex_value(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

const char *rt_wire_to_hex(const char *wire, int64_t wire_len) {
    static const char digits[] = "0123456789abcdef";
    char *result;
    size_t length;

    if (!wire || wire_len <= 0) {
        result = (char *)malloc(1);
        if (result) result[0] = '\0';
        return result;
    }
    if ((uint64_t)wire_len > (SIZE_MAX - 1) / 2) return NULL;
    length = (size_t)wire_len;
    result = (char *)malloc(length * 2 + 1);
    if (!result) return NULL;
    for (size_t i = 0; i < length; ++i) {
        unsigned char byte = (unsigned char)wire[i];
        result[i * 2] = digits[byte >> 4];
        result[i * 2 + 1] = digits[byte & 0x0f];
    }
    result[length * 2] = '\0';
    return result;
}

const char *rt_hex_to_wire(const char *hex) {
    char *result;
    size_t hex_len;
    size_t wire_len;

    if (!hex) hex = "";
    hex_len = strlen(hex);
    if ((hex_len & 1u) != 0 || hex_len == SIZE_MAX) goto invalid;
    wire_len = hex_len / 2;
    result = (char *)malloc(wire_len + 1);
    if (!result) return NULL;
    for (size_t i = 0; i < wire_len; ++i) {
        int high = hex_value(hex[i * 2]);
        int low = hex_value(hex[i * 2 + 1]);
        if (high < 0 || low < 0) {
            free(result);
            goto invalid;
        }
        result[i] = (char)((high << 4) | low);
    }
    result[wire_len] = '\0';
    return result;

invalid:
    result = (char *)malloc(1);
    if (result) result[0] = '\0';
    return result;
}
