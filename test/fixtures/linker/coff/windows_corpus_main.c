extern int windows_value;
extern int windows_add_one(int value);

int _start(void) {
    volatile int scratch[8];
    scratch[0] = windows_value;
    int result = windows_add_one(scratch[0]);
    return result + scratch[0];
}
