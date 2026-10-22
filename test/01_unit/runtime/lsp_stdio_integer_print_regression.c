#include <stdint.h>
extern int64_t rt_value_int_wide(int64_t);
extern int64_t print_raw(int64_t);
extern int64_t rt_stdout_write_text(const char*);
int main(void){print_raw(rt_value_int_wide(42));rt_stdout_write_text("\n");print_raw(rt_value_int_wide(-7));rt_stdout_write_text("\n");return 0;}
