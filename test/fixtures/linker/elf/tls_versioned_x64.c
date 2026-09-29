extern __thread long imported_tls_v1;
__asm__(".symver imported_tls_v1, imported_tls@TLS_1.0");

long read_versioned_tls(void) {
    return imported_tls_v1;
}

void _start(void) {
    read_versioned_tls();
}
