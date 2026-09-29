extern const char *short_message(void);

const char *long_message(void) {
    return "prefix-suffix";
}

volatile const char *string_sink;

void _start(void) {
    string_sink = long_message();
    string_sink = short_message();
}
