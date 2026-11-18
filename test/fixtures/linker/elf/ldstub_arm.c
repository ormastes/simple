/* Link-time stand-in for ld-linux-armhf.so.3 (same soname): only exports
   __tls_get_addr so specs can link GD/LD code without the real loader. */
void *__tls_get_addr(void *p) { return p; }
