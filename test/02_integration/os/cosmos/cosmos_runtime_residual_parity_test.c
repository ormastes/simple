#include <stdio.h>
#include <stdlib.h>

#include "cosmos_runtime_residual_oracle.h"

#ifdef COSMOS_RUNTIME_RESIDUAL_ORACLE_ONLY
#define cosmos_runtime_residual_memmove cosmos_runtime_residual_oracle_memmove
#define cosmos_runtime_residual_memcmp cosmos_runtime_residual_oracle_memcmp
#define cosmos_runtime_residual_strlen cosmos_runtime_residual_oracle_strlen
#define cosmos_runtime_residual_strcmp cosmos_runtime_residual_oracle_strcmp
#define cosmos_runtime_residual_strncmp cosmos_runtime_residual_oracle_strncmp
#define cosmos_runtime_residual_strncpy cosmos_runtime_residual_oracle_strncpy
static void cosmos_runtime_residual_coverage_reset(void) {}
static unsigned long long cosmos_runtime_residual_coverage_mask(void) {
    return 0x003FFFFFFFFFFFFFULL;
}
static unsigned long long cosmos_runtime_residual_coverage_required(void) {
    return 0x003FFFFFFFFFFFFFULL;
}
static unsigned long long cosmos_runtime_residual_coverage_decisions(void) {
    return 27ULL;
}
#else
#include "cosmos_runtime_residual.h"
#endif

#define LIMIT 1000000U

static unsigned int rows;

static void require(int condition, const char *label) {
    if (!condition) {
        fprintf(stderr, "FAIL row %u: %s\n", rows + 1U, label);
        exit(1);
    }
    rows = rows + 1U;
}

static int bytes_equal(const unsigned char *a, const unsigned char *b,
                       unsigned int size) {
    unsigned int i;
    for (i = 0; i < size; i = i + 1U)
        if (a[i] != b[i]) return 0;
    return 1;
}

static void check_move(void *dst_a, const void *src_a,
                       void *dst_b, const void *src_b,
                       unsigned int size, unsigned char *base_a,
                       unsigned char *base_b, unsigned int extent,
                       const char *label) {
    void *ra = cosmos_runtime_residual_oracle_memmove(dst_a, src_a, size);
    void *rb = cosmos_runtime_residual_memmove(dst_b, src_b, size);
    require(((ra == (void *)0) == (rb == (void *)0)) &&
            (ra == (void *)0 ||
             ((unsigned char *)ra - base_a) ==
                 ((unsigned char *)rb - base_b)) &&
            bytes_equal(base_a, base_b, extent), label);
}

int main(void) {
    unsigned char a[16] = "0123456789";
    unsigned char b[16] = "0123456789";
    unsigned char x[16] = "abcdef";
    unsigned char y[16] = "abcdeg";
    unsigned char da[8] = {0xA5U, 0xA5U, 0xA5U, 0xA5U,
                           0xA5U, 0xA5U, 0xA5U, 0xA5U};
    unsigned char db[8] = {0xA5U, 0xA5U, 0xA5U, 0xA5U,
                           0xA5U, 0xA5U, 0xA5U, 0xA5U};
    unsigned char *long_a;
    unsigned char *long_b;
    unsigned int i;

    cosmos_runtime_residual_coverage_reset();
    require(cosmos_runtime_residual_oracle_memmove(0, a, 1U) ==
            cosmos_runtime_residual_memmove(0, b, 1U), "move-null-dst");
    check_move(a, 0, b, 0, 1U, a, b, sizeof(a), "move-null-src");
    check_move(a, a, b, b, 4U, a, b, sizeof(a), "move-same");
    check_move(a, a + 2, b, b + 2, 0U, a, b, sizeof(a), "move-forward-empty");
    check_move(a, a + 2, b, b + 2, 4U, a, b, sizeof(a), "move-forward");
    check_move(a + 2, a, b + 2, b, 0U, a, b, sizeof(a), "move-backward-empty");
    check_move(a + 2, a, b + 2, b, 6U, a, b, sizeof(a), "move-backward");

    require(cosmos_runtime_residual_oracle_memcmp(0, 0, 3U) ==
            cosmos_runtime_residual_memcmp(0, 0, 3U), "memcmp-null-both");
    require(cosmos_runtime_residual_oracle_memcmp(0, x, 3U) ==
            cosmos_runtime_residual_memcmp(0, x, 3U), "memcmp-null-left");
    require(cosmos_runtime_residual_oracle_memcmp(x, 0, 3U) ==
            cosmos_runtime_residual_memcmp(x, 0, 3U), "memcmp-null-right");
    require(cosmos_runtime_residual_oracle_memcmp(x, y, 0U) ==
            cosmos_runtime_residual_memcmp(x, y, 0U), "memcmp-empty");
    require(cosmos_runtime_residual_oracle_memcmp(x, x, 6U) ==
            cosmos_runtime_residual_memcmp(x, x, 6U), "memcmp-equal");
    require(cosmos_runtime_residual_oracle_memcmp(x, y, 6U) ==
            cosmos_runtime_residual_memcmp(x, y, 6U), "memcmp-different");

    require(cosmos_runtime_residual_oracle_strlen(0) ==
            cosmos_runtime_residual_strlen(0), "strlen-null");
    require(cosmos_runtime_residual_oracle_strlen("") ==
            cosmos_runtime_residual_strlen(""), "strlen-empty");
    require(cosmos_runtime_residual_oracle_strlen("abc") ==
            cosmos_runtime_residual_strlen("abc"), "strlen-text");

    require(cosmos_runtime_residual_oracle_strcmp(0, 0) ==
            cosmos_runtime_residual_strcmp(0, 0), "strcmp-null-both");
    require(cosmos_runtime_residual_oracle_strcmp(0, "a") ==
            cosmos_runtime_residual_strcmp(0, "a"), "strcmp-null-left");
    require(cosmos_runtime_residual_oracle_strcmp("a", 0) ==
            cosmos_runtime_residual_strcmp("a", 0), "strcmp-null-right");
    require(cosmos_runtime_residual_oracle_strcmp("", "") ==
            cosmos_runtime_residual_strcmp("", ""), "strcmp-empty");
    require(cosmos_runtime_residual_oracle_strcmp("abc", "abc") ==
            cosmos_runtime_residual_strcmp("abc", "abc"), "strcmp-equal");
    require(cosmos_runtime_residual_oracle_strcmp("abc", "abd") ==
            cosmos_runtime_residual_strcmp("abc", "abd"), "strcmp-different");

    require(cosmos_runtime_residual_oracle_strncmp(0, 0, 3U) ==
            cosmos_runtime_residual_strncmp(0, 0, 3U), "strncmp-null-both");
    require(cosmos_runtime_residual_oracle_strncmp(0, "a", 3U) ==
            cosmos_runtime_residual_strncmp(0, "a", 3U), "strncmp-null-left");
    require(cosmos_runtime_residual_oracle_strncmp("a", 0, 3U) ==
            cosmos_runtime_residual_strncmp("a", 0, 3U), "strncmp-null-right");
    require(cosmos_runtime_residual_oracle_strncmp("a", "b", 0U) ==
            cosmos_runtime_residual_strncmp("a", "b", 0U), "strncmp-empty");
    require(cosmos_runtime_residual_oracle_strncmp("abc", "abc", 3U) ==
            cosmos_runtime_residual_strncmp("abc", "abc", 3U), "strncmp-equal");
    require(cosmos_runtime_residual_oracle_strncmp("abc", "abd", 3U) ==
            cosmos_runtime_residual_strncmp("abc", "abd", 3U), "strncmp-different");
    require(cosmos_runtime_residual_oracle_strncmp("a", "a", 3U) ==
            cosmos_runtime_residual_strncmp("a", "a", 3U), "strncmp-terminator");

    require(cosmos_runtime_residual_oracle_strncpy(0, "a", 2U) ==
            cosmos_runtime_residual_strncpy(0, "a", 2U), "strncpy-null-dst");
    require(cosmos_runtime_residual_oracle_strncpy((char *)da, 0, 2U) ==
                (char *)da &&
            cosmos_runtime_residual_strncpy((char *)db, 0, 2U) ==
                (char *)db && bytes_equal(da, db, sizeof(da)),
            "strncpy-null-src");
    cosmos_runtime_residual_oracle_strncpy((char *)da, "a", 0U);
    cosmos_runtime_residual_strncpy((char *)db, "a", 0U);
    require(bytes_equal(da, db, sizeof(da)), "strncpy-empty");
    cosmos_runtime_residual_oracle_strncpy((char *)da, "a", 6U);
    cosmos_runtime_residual_strncpy((char *)db, "a", 6U);
    require(bytes_equal(da, db, sizeof(da)), "strncpy-padding");
    cosmos_runtime_residual_oracle_strncpy((char *)da, "abcdef", 3U);
    cosmos_runtime_residual_strncpy((char *)db, "abcdef", 3U);
    require(bytes_equal(da, db, sizeof(da)), "strncpy-no-terminator");

    long_a = (unsigned char *)malloc(LIMIT);
    long_b = (unsigned char *)malloc(LIMIT);
    require(long_a != 0 && long_b != 0, "long-buffer-allocation");
    for (i = 0; i < LIMIT; i = i + 1U) {
        long_a[i] = (unsigned char)'x';
        long_b[i] = (unsigned char)'x';
    }
    require(cosmos_runtime_residual_oracle_strlen((const char *)long_a) ==
            cosmos_runtime_residual_strlen((const char *)long_b), "strlen-limit");
    require(cosmos_runtime_residual_oracle_strcmp((const char *)long_a,
                                                  (const char *)long_a) ==
            cosmos_runtime_residual_strcmp((const char *)long_b,
                                           (const char *)long_b), "strcmp-limit");
    free(long_a);
    free(long_b);

    require(cosmos_runtime_residual_coverage_decisions() == 27ULL,
            "decision-denominator");
    require(cosmos_runtime_residual_coverage_required() ==
            0x003FFFFFFFFFFFFFULL, "outcome-denominator");
    require(cosmos_runtime_residual_coverage_mask() ==
            cosmos_runtime_residual_coverage_required(), "outcome-coverage");
    printf("COSMOS_RUNTIME_RESIDUAL_PARITY_ROWS %u\n", rows);
    printf("COSMOS_RUNTIME_RESIDUAL_SIMPLE_DECISIONS 27/27\n");
    printf("COSMOS_RUNTIME_RESIDUAL_SIMPLE_OUTCOMES 54/54\n");
    return 0;
}
