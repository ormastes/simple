#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void expect_array_bytes(RuntimeValue rv, const uint8_t *expected, uint32_t expected_len)
{
    assert(IS_HEAP(rv));
    RuntimeArray *arr = (RuntimeArray *)DECODE_PTR(rv);
    assert(arr != NULL);
    assert(arr->hdr.type == HEAP_ARRAY);
    assert(arr->hdr.gc_flags == 0);
    assert(arr->len == expected_len);
    for (uint32_t i = 0; i < expected_len; i++) {
        assert(_rt_bytes_get(arr, i) == expected[i]);
    }
}

int main(void)
{
    /* 1. NIST SP 800-38D AES-128-GCM Test Case 1: empty plaintext & empty AAD */
    const uint8_t zero_key[16] = {0};
    const uint8_t zero_nonce[12] = {0};
    const uint8_t nist_tc1_tag[16] = {
        0x58, 0xe2, 0xfc, 0xce, 0xfa, 0x7e, 0x30, 0x61,
        0x36, 0x7f, 0x1d, 0x57, 0xa4, 0xe7, 0x45, 0x5a
    };

    RuntimeValue rv_zero_key_packed = _rt_bytes_new(zero_key, 16);
    RuntimeValue rv_zero_nonce_packed = _rt_bytes_new(zero_nonce, 12);
    RuntimeValue rv_empty = _tls_runtime_array_from_bytes((const uint8_t *)"", 0);
    RuntimeValue rv_tc1_tag = _rt_bytes_new(nist_tc1_tag, 16);

    RuntimeValue dec_tc1 = rt_tls13_aes128_gcm_decrypt(
        rv_zero_key_packed, rv_zero_nonce_packed, rv_empty, rv_empty, rv_tc1_tag
    );
    const uint8_t expected_tc1[1] = {0x01U};
    expect_array_bytes(dec_tc1, expected_tc1, 1);

    /* 2. Round-trip encrypt -> decrypt with BYTE_PACKED inputs and AAD */
    const uint8_t key[16] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f
    };
    const uint8_t nonce[12] = {
        0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5,
        0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab
    };
    const uint8_t aad[5] = {0x17, 0x03, 0x03, 0x00, 0x1a};
    const uint8_t pt[10] = {'S', 'i', 'm', 'p', 'l', 'e', 'O', 'S', '!', 0x17};

    RuntimeValue rv_key = _rt_bytes_new(key, 16);
    RuntimeValue rv_nonce = _rt_bytes_new(nonce, 12);
    RuntimeValue rv_aad = _rt_bytes_new(aad, 5);
    RuntimeValue rv_pt = _rt_bytes_new(pt, 10);

    RuntimeValue ct_and_tag = rt_tls13_aes128_gcm_encrypt(rv_key, rv_nonce, rv_pt, rv_aad);
    assert(IS_HEAP(ct_and_tag));
    RuntimeArray *ct_tag_arr = (RuntimeArray *)DECODE_PTR(ct_and_tag);
    assert(ct_tag_arr->len == 26U);

    uint8_t ct_buf[10];
    uint8_t tag_buf[16];
    for (uint32_t i = 0; i < 10U; i++) ct_buf[i] = _rt_bytes_get(ct_tag_arr, i);
    for (uint32_t i = 0; i < 16U; i++) tag_buf[i] = _rt_bytes_get(ct_tag_arr, 10U + i);

    RuntimeValue rv_ct_tagged = _tls_runtime_array_from_bytes(ct_buf, 10);
    RuntimeValue rv_tag_tagged = _tls_runtime_array_from_bytes(tag_buf, 16);

    RuntimeValue dec_ok = rt_tls13_aes128_gcm_decrypt(
        rv_key, rv_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged
    );
    uint8_t expected_ok[11];
    expected_ok[0] = 0x01U;
    memcpy(expected_ok + 1, pt, 10);
    expect_array_bytes(dec_ok, expected_ok, 11);

    /* 3. Forged tag (1-bit flip) -> [0x00] */
    uint8_t bad_tag[16];
    memcpy(bad_tag, tag_buf, 16);
    bad_tag[15] ^= 0x01U;
    RuntimeValue rv_bad_tag = _rt_bytes_new(bad_tag, 16);
    RuntimeValue dec_forged = rt_tls13_aes128_gcm_decrypt(
        rv_key, rv_nonce, rv_ct_tagged, rv_aad, rv_bad_tag
    );
    const uint8_t expected_forged[1] = {0x00U};
    expect_array_bytes(dec_forged, expected_forged, 1);

    /* 4. Wrong key/nonce/tag lengths (short & oversized) -> [] */
    const uint8_t key17[17] = {0};
    const uint8_t nonce13[13] = {0};
    const uint8_t tag17[17] = {0};
    RuntimeValue rv_short_key = _rt_bytes_new(key, 15);
    RuntimeValue rv_long_key = _rt_bytes_new(key17, 17);
    RuntimeValue rv_short_nonce = _rt_bytes_new(nonce, 11);
    RuntimeValue rv_long_nonce = _rt_bytes_new(nonce13, 13);
    RuntimeValue rv_short_tag = _rt_bytes_new(tag_buf, 15);
    RuntimeValue rv_long_tag = _rt_bytes_new(tag17, 17);

    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_short_key, rv_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_long_key, rv_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_key, rv_short_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_key, rv_long_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_key, rv_nonce, rv_ct_tagged, rv_aad, rv_short_tag),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_key, rv_nonce, rv_ct_tagged, rv_aad, rv_long_tag),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(NIL_VALUE, rv_nonce, rv_ct_tagged, rv_aad, rv_tag_tagged),
        (const uint8_t *)"", 0
    );

    /* 5. Invalid/oversized ciphertext_rv paired with valid TC1 tag -> [] (never [0x01] or [0x00]) */
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_zero_key_packed, rv_zero_nonce_packed, NIL_VALUE, rv_empty, rv_tc1_tag),
        (const uint8_t *)"", 0
    );
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_zero_key_packed, rv_zero_nonce_packed, ENCODE_INT(42), rv_empty, rv_tc1_tag),
        (const uint8_t *)"", 0
    );
    RuntimeArray wrong_type_obj;
    memset(&wrong_type_obj, 0, sizeof(wrong_type_obj));
    wrong_type_obj.hdr.object_type = 1U; /* HEAP_STRING != HEAP_ARRAY */
    wrong_type_obj.len = 0U;
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_zero_key_packed, rv_zero_nonce_packed, ENCODE_PTR(&wrong_type_obj), rv_empty, rv_tc1_tag),
        (const uint8_t *)"", 0
    );
    RuntimeArray wrap_len_obj;
    memset(&wrap_len_obj, 0, sizeof(wrap_len_obj));
    wrap_len_obj.hdr.object_type = HEAP_ARRAY;
    wrap_len_obj.len = 1ULL << 32; /* Must fail 64-bit cap before narrowing to uint32_t(0) */
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_zero_key_packed, rv_zero_nonce_packed, ENCODE_PTR(&wrap_len_obj), rv_empty, rv_tc1_tag),
        (const uint8_t *)"", 0
    );
    /* Valid empty [] + valid TC1 tag still returns [0x01] */
    expect_array_bytes(
        rt_tls13_aes128_gcm_decrypt(rv_zero_key_packed, rv_zero_nonce_packed, rv_empty, rv_empty, rv_tc1_tag),
        expected_tc1, 1
    );
    /* Invalid plaintext_rv to encrypt fails closed with NIL_VALUE */
    assert(rt_tls13_aes128_gcm_encrypt(rv_key, rv_nonce, NIL_VALUE, rv_aad) == NIL_VALUE);
    assert(rt_tls13_aes128_gcm_encrypt(rv_key, rv_nonce, ENCODE_PTR(&wrap_len_obj), rv_aad) == NIL_VALUE);

    printf("PASS rt_tls13_aes128_gcm_decrypt host C harness (5 test groups)\n");
    return 0;
}
