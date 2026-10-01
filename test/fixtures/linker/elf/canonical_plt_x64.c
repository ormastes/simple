extern long add_val(long value);

long (*selected_add)(long) = add_val;

void _start(void) {
    selected_add(40);
}
