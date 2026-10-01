extern __thread long imported_tls;

long read_imported_tls(void) {
    return imported_tls;
}

void _start(void) {
    read_imported_tls();
}
