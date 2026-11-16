static const char msg[] = "hello internal linker\n";
static int counter = 3;
#if defined(__x86_64__)
static long sys3(long n,long a,long b,long c){long r;__asm__ volatile("syscall":"=a"(r):"a"(n),"D"(a),"S"(b),"d"(c):"rcx","r11","memory");return r;}
#define NR_WRITE 1
#define NR_EXIT 60
#elif defined(__i386__)
static long sys3(long n,long a,long b,long c){long r;__asm__ volatile("int $0x80":"=a"(r):"a"(n),"b"(a),"c"(b),"d"(c):"memory");return r;}
#define NR_WRITE 4
#define NR_EXIT 1
#elif defined(__aarch64__)
static long sys3(long n,long a,long b,long c){register long x8 __asm__("x8")=n;register long x0 __asm__("x0")=a;register long x1 __asm__("x1")=b;register long x2 __asm__("x2")=c;__asm__ volatile("svc 0":"+r"(x0):"r"(x8),"r"(x1),"r"(x2):"memory");return x0;}
#define NR_WRITE 64
#define NR_EXIT 93
#elif defined(__riscv)
static long sys3(long n,long a,long b,long c){register long a7 __asm__("a7")=n;register long a0 __asm__("a0")=a;register long a1 __asm__("a1")=b;register long a2 __asm__("a2")=c;__asm__ volatile("ecall":"+r"(a0):"r"(a7),"r"(a1),"r"(a2):"memory");return a0;}
#define NR_WRITE 64
#define NR_EXIT 93
#elif defined(__arm__)
static long sys3(long n,long a,long b,long c){register long r7 __asm__("r7")=n;register long r0 __asm__("r0")=a;register long r1 __asm__("r1")=b;register long r2 __asm__("r2")=c;__asm__ volatile("svc 0":"+r"(r0):"r"(r7),"r"(r1),"r"(r2):"memory");return r0;}
#define NR_WRITE 4
#define NR_EXIT 1
#endif
extern int helper(int);
void _start(void){ for(int i=0;i<counter;i++) sys3(NR_WRITE,1,(long)msg,sizeof msg-1); sys3(NR_EXIT,helper(40),0,0); for(;;){} }
