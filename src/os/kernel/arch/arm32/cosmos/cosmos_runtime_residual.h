#ifndef SIMPLE_OS_COSMOS_RUNTIME_RESIDUAL_H
#define SIMPLE_OS_COSMOS_RUNTIME_RESIDUAL_H

/* Pure-Simple deterministic memory/string exports behind the C ABI shims. */
void *cosmos_runtime_residual_memmove(void *dst, const void *src,
                                      unsigned int size);
int cosmos_runtime_residual_memcmp(const void *left, const void *right,
                                   unsigned int size);
unsigned int cosmos_runtime_residual_strlen(const char *text);
int cosmos_runtime_residual_strcmp(const char *left, const char *right);
int cosmos_runtime_residual_strncmp(const char *left, const char *right,
                                    unsigned int size);
char *cosmos_runtime_residual_strncpy(char *dst, const char *src,
                                      unsigned int size);

void cosmos_runtime_residual_coverage_reset(void);
unsigned long long cosmos_runtime_residual_coverage_mask(void);
unsigned long long cosmos_runtime_residual_coverage_required(void);
unsigned long long cosmos_runtime_residual_coverage_decisions(void);

#endif
