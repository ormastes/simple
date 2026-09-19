/* Initial-exec TLS fixture: R_X86_64_GOTTPOFF / R_AARCH64_TLSIE_*. */
extern __thread int tls_counter;
int tls_read(void) { return tls_counter; }
