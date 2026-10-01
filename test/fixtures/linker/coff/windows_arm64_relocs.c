extern int arm64_external(int value);
extern int arm64_data;

int arm64_call_and_load(int value) {
    return arm64_external(value) + arm64_data;
}

int *arm64_address(void) {
    return &arm64_data;
}
