/* COFF linker fixture: entry object. Freestanding, no CRT, no imports. */
extern int add_val(int x);
extern int base;
static const char msg[] = "hi\n";
const char *msg_ptr = msg;   /* IMAGE_REL_AMD64_ADDR64 in .data */

int entry(void) {
    /* REL32 call to add_val (other object), REL32 loads of msg_ptr/base */
    return add_val(40) + base + (int)msg_ptr[0];
}
