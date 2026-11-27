/* armv7 initial-exec TLS: _start loads tv1 through a TLS_IE32 GOT slot. */
__attribute__((tls_model("initial-exec"))) extern __thread int tv1;
int _start(void) { return tv1; }
