extern int remote_value;
extern int remote_add_one(int value);

int _start(void) {
    return remote_add_one(remote_value);
}
