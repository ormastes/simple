extern int fa(int);
void _start(void) { int r = fa(4); __asm__ volatile("mov r0, %0\n mov r7, #0\n svc #0" :: "r"(r) : "r0", "r7"); }
