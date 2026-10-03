__thread long global_tls = 7;
static __thread long local_tls = 3;
__attribute__((visibility("hidden"))) __thread long hidden_tls = 5;
void _start(void) { global_tls = local_tls + hidden_tls; }
