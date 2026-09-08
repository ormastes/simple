#ifndef SLANG_PAGED_KV_PROVIDER_FIXTURE_H
#define SLANG_PAGED_KV_PROVIDER_FIXTURE_H

#include <stdint.h>

/* Test-only request/token seam surrounding the production provider ABI. */
int64_t fixture_request_create(int64_t execution_namespace, int64_t token_capacity);
int64_t fixture_request_close(int64_t request_handle);
int64_t fixture_request_cancel(int64_t request_handle);
int64_t fixture_request_set_token(int64_t request_handle, int64_t index, int64_t token);
int64_t fixture_request_sample(int64_t request_handle);
int64_t fixture_request_cursor(int64_t request_handle);
int64_t fixture_request_page(int64_t request_handle, int64_t index);
int64_t fixture_page_row(int64_t pool_handle, int64_t page_handle, int64_t row);
int64_t fixture_page_valid_rows(int64_t pool_handle, int64_t page_handle);
int64_t fixture_page_is_sealed(int64_t pool_handle, int64_t page_handle);
int64_t fixture_fail_next_copy(void);
int64_t fixture_fail_next_prefill(void);
int64_t fixture_fail_next_commit(void);

#endif
