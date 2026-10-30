#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

const char *rt_byte_char(int64_t value);
const char *rt_wire_to_hex(const char *wire, int64_t wire_len);
const char *rt_hex_to_wire(const char *hex);
int64_t rt_random_i64(void);
const char *rt_rsa_decrypt(const char *ciphertext, const char *private_key_pem);
const char *rt_rsa_decrypt_with_len(const char *ciphertext, int64_t ciphertext_len,
                                    const char *private_key_pem, int64_t key_len,
                                    int64_t *out_len);

static int make_rsa_key(char **private_key_pem, EVP_PKEY **key_out) {
    EVP_PKEY_CTX *keygen = NULL;
    EVP_PKEY *key = NULL;
    BIO *bio = NULL;
    char *pem_copy = NULL;
    char *pem_data = NULL;
    long pem_length;
    int status = 1;

    keygen = EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, NULL);
    if (!keygen || EVP_PKEY_keygen_init(keygen) <= 0 ||
        EVP_PKEY_CTX_set_rsa_keygen_bits(keygen, 2048) <= 0 ||
        EVP_PKEY_keygen(keygen, &key) <= 0) {
        goto done;
    }
    bio = BIO_new(BIO_s_mem());
    if (!bio || PEM_write_bio_PrivateKey(bio, key, NULL, NULL, 0, NULL, NULL) != 1) {
        goto done;
    }
    pem_length = BIO_get_mem_data(bio, &pem_data);
    if (pem_length <= 0 || (uint64_t)pem_length >= SIZE_MAX) goto done;
    pem_copy = (char *)malloc((size_t)pem_length + 1);
    if (!pem_copy) goto done;
    memcpy(pem_copy, pem_data, (size_t)pem_length);
    pem_copy[pem_length] = '\0';

    *private_key_pem = pem_copy;
    *key_out = key;
    pem_copy = NULL;
    key = NULL;
    status = 0;

done:
    free(pem_copy);
    BIO_free(bio);
    EVP_PKEY_free(key);
    EVP_PKEY_CTX_free(keygen);
    return status;
}

/* Generate a PKCS#1 ciphertext whose embedded-NUL shape exercises either the
 * legacy C-string wrapper or its binary-safe explicit-length counterpart. */
static int encrypt_with_nul_shape(EVP_PKEY *key, const unsigned char *plaintext,
                                  size_t plaintext_len, int require_embedded_nul,
                                  unsigned char **ciphertext_out,
                                  size_t *ciphertext_len_out) {
    unsigned char *ciphertext = NULL;
    size_t ciphertext_capacity = 0;
    *ciphertext_out = NULL;
    *ciphertext_len_out = 0;

    for (int attempt = 0; attempt < 64; ++attempt) {
        EVP_PKEY_CTX *context = EVP_PKEY_CTX_new(key, NULL);
        size_t ciphertext_len = 0;
        if (!context || EVP_PKEY_encrypt_init(context) <= 0 ||
            EVP_PKEY_CTX_set_rsa_padding(context, RSA_PKCS1_PADDING) <= 0 ||
            EVP_PKEY_encrypt(context, NULL, &ciphertext_len,
                             plaintext, plaintext_len) <= 0) {
            EVP_PKEY_CTX_free(context);
            free(ciphertext);
            return 1;
        }
        if (ciphertext_len > ciphertext_capacity) {
            unsigned char *resized = (unsigned char *)realloc(ciphertext, ciphertext_len + 1);
            if (!resized) {
                EVP_PKEY_CTX_free(context);
                free(ciphertext);
                return 2;
            }
            ciphertext = resized;
            ciphertext_capacity = ciphertext_len;
        }
        if (EVP_PKEY_encrypt(context, ciphertext, &ciphertext_len,
                             plaintext, plaintext_len) <= 0) {
            EVP_PKEY_CTX_free(context);
            free(ciphertext);
            return 3;
        }
        EVP_PKEY_CTX_free(context);
        if ((memchr(ciphertext, 0, ciphertext_len) != NULL) == require_embedded_nul) {
            ciphertext[ciphertext_len] = 0;
            *ciphertext_out = ciphertext;
            *ciphertext_len_out = ciphertext_len;
            return 0;
        }
    }
    free(ciphertext);
    return 4;
}

int main(void) {
    const char wire[] = {0x00, 0x7f, (char)0x80, (char)0xff};
    const char *byte = rt_byte_char(0x141);
    const char *hex = rt_wire_to_hex(wire, 4);
    const char *decoded = rt_hex_to_wire("007f80ff");
    const char *invalid = rt_hex_to_wire("0xz1");
    volatile int64_t random_value = rt_random_i64();
    (void)random_value;
    if (!byte || (unsigned char)byte[0] != 0x41 || byte[1] != '\0') return 1;
    if (!hex || strcmp(hex, "007f80ff") != 0) return 2;
    if (!decoded || memcmp(decoded, wire, sizeof(wire)) != 0 || decoded[4] != '\0') return 3;
    if (!invalid || invalid[0] != '\0') return 4;
    free((void *)byte);
    free((void *)hex);
    free((void *)decoded);
    free((void *)invalid);

    {
        static const unsigned char plaintext[] = "hosted RSA self-check";
        char *right_pem = NULL;
        char *wrong_pem = NULL;
        unsigned char *legacy_ciphertext = NULL;
        unsigned char *binary_ciphertext = NULL;
        char *decrypted = NULL;
        EVP_PKEY *right_key = NULL;
        EVP_PKEY *wrong_key = NULL;
        size_t legacy_ciphertext_len = 0;
        size_t binary_ciphertext_len = 0;
        int64_t decrypted_len = -1;
        int rc = 10;

        if (make_rsa_key(&right_pem, &right_key) != 0) goto rsa_done;
        if (make_rsa_key(&wrong_pem, &wrong_key) != 0) { rc = 11; goto rsa_done; }
        if (encrypt_with_nul_shape(right_key, plaintext, sizeof(plaintext) - 1,
                                   0, &legacy_ciphertext,
                                   &legacy_ciphertext_len) != 0) {
            rc = 12;
            goto rsa_done;
        }

        decrypted = (char *)rt_rsa_decrypt((const char *)legacy_ciphertext, right_pem);
        if (!decrypted || strcmp(decrypted, (const char *)plaintext) != 0) {
            rc = 13;
            goto rsa_done;
        }
        free(decrypted);
        decrypted = NULL;

        decrypted = (char *)rt_rsa_decrypt((const char *)legacy_ciphertext, wrong_pem);
        if (!decrypted || decrypted[0] != '\0') { rc = 14; goto rsa_done; }
        free(decrypted);
        decrypted = NULL;

        if (encrypt_with_nul_shape(right_key, plaintext, sizeof(plaintext) - 1,
                                   1, &binary_ciphertext,
                                   &binary_ciphertext_len) != 0) {
            rc = 15;
            goto rsa_done;
        }
        decrypted = (char *)rt_rsa_decrypt_with_len(
            (const char *)binary_ciphertext, (int64_t)binary_ciphertext_len,
            right_pem, (int64_t)strlen(right_pem), &decrypted_len);
        if (!decrypted || decrypted_len != (int64_t)(sizeof(plaintext) - 1) ||
            memcmp(decrypted, plaintext, sizeof(plaintext) - 1) != 0 ||
            decrypted[decrypted_len] != '\0') {
            rc = 16;
            goto rsa_done;
        }
        free(decrypted);
        decrypted = NULL;

        decrypted_len = -1;
        decrypted = (char *)rt_rsa_decrypt_with_len(
            (const char *)binary_ciphertext, (int64_t)binary_ciphertext_len,
            wrong_pem, (int64_t)strlen(wrong_pem), &decrypted_len);
        if (!decrypted || decrypted[0] != '\0' || decrypted_len != 0) {
            rc = 17;
            goto rsa_done;
        }
        free(decrypted);
        decrypted = NULL;

        decrypted_len = -1;
        decrypted = (char *)rt_rsa_decrypt_with_len(
            "not-an-rsa-ciphertext", 21, right_pem,
            (int64_t)strlen(right_pem), &decrypted_len);
        if (!decrypted || decrypted[0] != '\0' || decrypted_len != 0) {
            rc = 18;
            goto rsa_done;
        }
        free(decrypted);
        decrypted = NULL;

        decrypted_len = -1;
        decrypted = (char *)rt_rsa_decrypt_with_len(
            (const char *)legacy_ciphertext, (int64_t)legacy_ciphertext_len,
            "not a PEM private key", 21, &decrypted_len);
        if (!decrypted || decrypted[0] != '\0' || decrypted_len != 0) {
            rc = 19;
            goto rsa_done;
        }
        free(decrypted);
        decrypted = NULL;

        decrypted = (char *)rt_rsa_decrypt("not-an-rsa-ciphertext", right_pem);
        if (!decrypted || decrypted[0] != '\0') { rc = 20; goto rsa_done; }
        free(decrypted);
        decrypted = NULL;

        decrypted = (char *)rt_rsa_decrypt((const char *)legacy_ciphertext,
                                           "not a PEM private key");
        if (!decrypted || decrypted[0] != '\0') { rc = 21; goto rsa_done; }
        rc = 0;

rsa_done:
        free(decrypted);
        free(legacy_ciphertext);
        free(binary_ciphertext);
        free(right_pem);
        free(wrong_pem);
        EVP_PKEY_free(right_key);
        EVP_PKEY_free(wrong_key);
        if (rc != 0) return rc;
    }
    return 0;
}
