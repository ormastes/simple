__thread long local_tls = 7;

long read_tls(void) {
    return local_tls;
}

void _start(void) {
    read_tls();
}
