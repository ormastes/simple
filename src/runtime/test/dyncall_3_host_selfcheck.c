#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>

int64_t rt_call_ptr_3(int64_t addr, int64_t a1, int64_t a2, int64_t a3);
int64_t rt_dyncall_3(int64_t fn_ptr, int64_t arg0, int64_t arg1, int64_t arg2);

static const int64_t expected_interface = INT64_MIN + INT64_C(0x1234567);
static const int64_t expected_request = INT64_C(0x23456789abcdef01);
static const int64_t expected_response = INT64_MIN + INT64_C(0x3456789);
static const int64_t expected_return = INT64_MIN + INT64_C(0x456789a);

static int64_t vector_call_fixture(int64_t interface_handle,
        int64_t request_address, int64_t response_address) {
    if (interface_handle != expected_interface ||
            request_address != expected_request ||
            response_address != expected_response)
        return INT64_C(0x13579bdf);
    return expected_return;
}

int main(void) {
    const int64_t interface_handle = expected_interface;
    const int64_t request_address = expected_request;
    const int64_t response_address = expected_response;
    const int64_t function_address = (int64_t)(uintptr_t)vector_call_fixture;
    const int64_t expected = rt_call_ptr_3(function_address,
        interface_handle, request_address, response_address);
    const int64_t actual = rt_dyncall_3(function_address,
        interface_handle, request_address, response_address);

    if (expected != expected_return || actual != expected_return || actual != expected) {
        fprintf(stderr, "dyncall_3 valid mismatch: expected=%" PRId64
                " actual=%" PRId64 "\n", expected, actual);
        return 1;
    }
    if (rt_dyncall_3(0, interface_handle, request_address,
            response_address) != -1) {
        fputs("dyncall_3 null pointer did not return -1\n", stderr);
        return 1;
    }
    if (rt_dyncall_3(-1, interface_handle, request_address,
            response_address) != -1) {
        fputs("dyncall_3 negative pointer did not return -1\n", stderr);
        return 1;
    }
    puts("PASS dyncall_3_host_selfcheck");
    return 0;
}
