/* Minimal stand-in for the unified kernel's C/Simple layer. Exercises exactly
 * the crt0.S boot contract: PL011 at the fixed QEMU virt address, .bss access,
 * .data access, and a rodata pointer (absolute relocation => proves relocation
 * landed at the link address). */
static volatile unsigned int * const UART = (unsigned int *)0x09000000UL;
static void puts_(const char *s){ while(*s) *UART = (unsigned char)*s++; }
static char bss_probe[64];
static const char rodata_msg[] = "[probe] rodata-ok\r\n";
static const char *const rodata_ptr = rodata_msg;   /* absolute reloc */
static unsigned long data_probe = 0xDEADBEEFUL;
void rt_arm64_handle_user_svc(void){}
void _c_start(void){
    puts_("[probe] c-start\r\n");
    if(bss_probe[0]==0 && bss_probe[63]==0) puts_("[probe] bss-zeroed\r\n");
    if(data_probe==0xDEADBEEFUL) puts_("[probe] data-ok\r\n");
    puts_(rodata_ptr);
    puts_("[probe] SIMPLEOS-ARM64-REALFW-BOOT-OK\r\n");
    for(;;) __asm__ volatile("wfe");
}
