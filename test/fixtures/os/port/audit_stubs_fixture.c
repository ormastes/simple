/* Fixture for audit_stubs_spec.spl — provides deterministic auto_stub_* symbols. */
#include <stddef.h>

/* 2 each, 6 prefixes = 12 symbols */
void auto_stub_gpu_memcpy(void) {}
void auto_stub_gpu_memset(void) {}
void auto_stub_cuda_launch_kernel(void) {}
void auto_stub_cuda_device_count(void) {}
void auto_stub_vulkan_create_instance(void) {}
void auto_stub_vulkan_destroy_instance(void) {}
void auto_stub_net_socket(void) {}
void auto_stub_net_connect(void) {}
void auto_stub_tls_handshake(void) {}
void auto_stub_tls_shutdown(void) {}
void auto_stub_sqlite3_open(void) {}
void auto_stub_sqlite3_close(void) {}
