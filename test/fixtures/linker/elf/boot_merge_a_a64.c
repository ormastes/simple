extern const char *other_message(void);
extern const char *tail_message(void);

const char *first_message(void) {
    return "boot-merge-shared-string";
}

volatile const char *string_sink;

void _start(void) {
    string_sink = first_message();
    string_sink = other_message();
    string_sink = tail_message();
    string_sink = "only-in-a";
}
