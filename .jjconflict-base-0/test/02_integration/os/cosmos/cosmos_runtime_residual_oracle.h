#ifndef SIMPLE_TEST_COSMOS_RUNTIME_RESIDUAL_ORACLE_H
#define SIMPLE_TEST_COSMOS_RUNTIME_RESIDUAL_ORACLE_H

void *cosmos_runtime_residual_oracle_memmove(void *dst, const void *src,
                                             unsigned int size);
int cosmos_runtime_residual_oracle_memcmp(const void *left, const void *right,
                                          unsigned int size);
unsigned int cosmos_runtime_residual_oracle_strlen(const char *text);
int cosmos_runtime_residual_oracle_strcmp(const char *left,
                                          const char *right);
int cosmos_runtime_residual_oracle_strncmp(const char *left,
                                           const char *right,
                                           unsigned int size);
char *cosmos_runtime_residual_oracle_strncpy(char *dst, const char *src,
                                             unsigned int size);

#endif
