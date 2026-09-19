#include <unistd.h>
__attribute__((noinline)) int never_called_fn(int x) { return x * 7 + 1; }
__attribute__((used)) static const char keep[] = "k";
int dead_data_marker = 12345;
int main(void){ write(1,"hi from libc\n",13); return 42; }
