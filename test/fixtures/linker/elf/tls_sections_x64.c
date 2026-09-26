__thread long initialized_tls = 7;
__thread long zero_tls;

void _start(void) {
    zero_tls = initialized_tls;
}
