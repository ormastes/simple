#include "arm32_user_transition_contract.h"
#include <stdint.h>
#include <stddef.h>

enum { PAGE_FREE = 0, PAGE_L1 = 1, PAGE_L2 = 2 };
typedef struct PageOwnerV13 {
    uint32_t address_space_id;
    uint16_t l1_index;
    uint8_t kind;
    uint8_t span;
} PageOwnerV13;

static uint8_t g_user_table_arena[ARM32_USER_TABLE_ARENA_BYTES]
    __attribute__((aligned(16384), section(".arm32.user_tables.v13")));
static PageOwnerV13 g_user_table_ledger[ARM32_USER_TABLE_PAGE_COUNT];
static int g_user_table_ready;
static uint8_t g_user_frame_arena[ARM32_USER_FRAME_ARENA_BYTES]
 __attribute__((aligned(4096),section(".arm32.user_frames.v15")));
static uint32_t g_user_frame_owner[ARM32_USER_FRAME_PAGE_COUNT];
static int g_user_frame_ready;
typedef struct GuardLeaseV15 {
    uint32_t root, guard_va, original_section, l2;
    uint8_t active;
} GuardLeaseV15;
static GuardLeaseV15 g_guard_leases[ARM32_MAX_CPU_SLOTS];
static uint8_t g_token_key[16];
static Arm32UserHandoffTokenV1 *g_active_tokens[ARM32_MAX_CPU_SLOTS];
static uint8_t g_stdout[ARM32_MAX_CPU_SLOTS][ARM32_STDOUT_CAPTURE_BYTES];
static uint16_t g_stdout_len[ARM32_MAX_CPU_SLOTS];
static int g_token_registry_ready;

static void bytes_zero(volatile uint8_t *p, uint32_t n)
{
    while (n--) *p++ = 0;
}

uint32_t arm32_user_table_arena_start_v13(void)
{
    return (uint32_t)(uintptr_t)g_user_table_arena;
}

uint32_t arm32_user_table_arena_end_v13(void)
{
    return arm32_user_table_arena_start_v13() + ARM32_USER_TABLE_ARENA_BYTES;
}

int arm32_user_table_arena_init_v13(uint32_t identity_start,
                                    uint32_t identity_end)
{
    uint32_t start = arm32_user_table_arena_start_v13();
    uint32_t end = arm32_user_table_arena_end_v13();
    if (g_user_table_ready || (start & 0x3fffu) || end < start ||
        start < identity_start || end > identity_end) return 0;
    bytes_zero(g_user_table_arena, sizeof g_user_table_arena);
    bytes_zero((volatile uint8_t *)g_user_table_ledger,
               sizeof g_user_table_ledger);
    g_user_table_ready = 1;
    return 1;
}

int arm32_user_frame_arena_init_v15(uint32_t start,uint32_t end)
{
    uint32_t a=(uint32_t)(uintptr_t)g_user_frame_arena,b=a+sizeof g_user_frame_arena;
    if(g_user_frame_ready||(a&0xfffu)||b<a||a<start||b>end) return 0;
    bytes_zero(g_user_frame_arena,sizeof g_user_frame_arena);
    bytes_zero((volatile uint8_t *)g_user_frame_owner,sizeof g_user_frame_owner);
    g_user_frame_ready=1; return 1;
}
static uint32_t frame_alloc(uint32_t asid,uint32_t count)
{
    uint32_t i,j;
    if(!g_user_frame_ready||!asid||!count) return 0;
    for(i=0;i+count<=ARM32_USER_FRAME_PAGE_COUNT;++i) {
        for(j=0;j<count&&!g_user_frame_owner[i+j];++j) {}
        if(j!=count){i+=j;continue;}
        for(j=0;j<count;++j)g_user_frame_owner[i+j]=asid;
        bytes_zero(&g_user_frame_arena[i*4096u],count*4096u);
        return (uint32_t)(uintptr_t)&g_user_frame_arena[i*4096u];
    } return 0;
}
int arm32_user_frames_free_v15(uint32_t asid)
{
    uint32_t i,found=0;if(!g_user_frame_ready||!asid)return 0;
    for(i=0;i<ARM32_USER_FRAME_PAGE_COUNT;++i)if(g_user_frame_owner[i]==asid){
        bytes_zero(&g_user_frame_arena[i*4096u],4096);g_user_frame_owner[i]=0;found=1;}
    return found;
}
static uint16_t rd16(const uint8_t *p){return (uint16_t)p[0]|(uint16_t)p[1]<<8;}
static uint32_t rd32(const uint8_t *p){return (uint32_t)rd16(p)|(uint32_t)rd16(p+2)<<16;}
int arm32_stage_elf32_v15(uint32_t asid,uint32_t kernel_root,uint32_t cpu,
 const uint8_t *elf,uint32_t len,Arm32StagedImageV15 *out)
{
    uint32_t root=0,phoff,phnum,phentsz,i,mapped=0,user_sp=0x7ff00000u;
    uint32_t svc_pair,guard,svc_top;
    if(!out||!elf||len<52||elf[0]!=0x7f||elf[1]!='E'||elf[2]!='L'||elf[3]!='F'||
       elf[4]!=1||elf[5]!=1||rd16(elf+18)!=40||!asid) return 0;
    phoff=rd32(elf+28);phentsz=rd16(elf+42);phnum=rd16(elf+44);
    if(phentsz<32||!phnum||phnum>32||phoff>len||phnum>(len-phoff)/phentsz)return 0;
    if(!arm32_user_l1_create_v1(asid,&root))return 0;
    for(i=0;i<phnum;++i){const uint8_t *p=elf+phoff+i*phentsz;uint32_t off,va,fs,ms,fl,pos;
        if(rd32(p)!=1)continue;off=rd32(p+4);va=rd32(p+8);fs=rd32(p+16);ms=rd32(p+20);fl=rd32(p+24);
        if(fs>ms||off>len||fs>len-off||!ms||(va&0xfffu)||(off&0xfffu)||va>=0x80000000u||
           ms>0x80000000u-va||(fl&2u&&fl&1u))goto fail;
        for(pos=0;pos<ms;pos+=4096u){uint32_t pa=frame_alloc(asid,1),n=0,j,flags=ARM32_MAP_USER;
            if(!pa)goto fail;if(pos<fs){n=fs-pos;if(n>4096)n=4096;for(j=0;j<n;++j)((uint8_t *)(uintptr_t)pa)[j]=elf[off+pos+j];}
            if(fl&2u)flags|=ARM32_MAP_WRITE;if(fl&1u)flags|=ARM32_MAP_EXEC;
            if(!arm32_user_l1_map_v1(root,va+pos,pa,flags))goto fail;mapped++;}
    }
    {uint32_t pa=frame_alloc(asid,1);if(!pa||!arm32_user_l1_map_v1(root,user_sp-4096u,pa,ARM32_MAP_USER|ARM32_MAP_WRITE))goto fail;mapped++;}
    svc_pair=frame_alloc(asid,2);if(!svc_pair)goto fail;guard=svc_pair;svc_top=svc_pair+8192u;
    if(!arm32_kernel_guard_page_install_v15(kernel_root,guard,cpu))goto fail;
    out->entry=rd32(elf+24);out->user_sp=user_sp;out->user_root=root;out->address_space_id=asid;
    out->svc_stack_top=svc_top;out->svc_guard_va=guard;out->mapped_pages=mapped;out->reserved=0;return 1;
fail:
    if(root)arm32_user_l1_destroy_v1(root,asid);arm32_user_frames_free_v15(asid);return 0;
}

static uint32_t alloc_pages(uint32_t asid, uint32_t l1_index,
                            uint8_t kind, uint32_t count, uint32_t alignment)
{
    uint32_t i, j;
    if (!g_user_table_ready || !asid || !count) return 0;
    for (i = 0; i + count <= ARM32_USER_TABLE_PAGE_COUNT; ++i) {
        uint32_t address = arm32_user_table_arena_start_v13() + i * 4096u;
        if (address & (alignment - 1u)) continue;
        for (j = 0; j < count && g_user_table_ledger[i + j].kind == PAGE_FREE; ++j) {}
        if (j != count) { i += j; continue; }
        for (j = 0; j < count; ++j) {
            g_user_table_ledger[i + j].address_space_id = asid;
            g_user_table_ledger[i + j].l1_index = (uint16_t)l1_index;
            g_user_table_ledger[i + j].kind = kind;
            g_user_table_ledger[i + j].span = (uint8_t)(count - j);
        }
        bytes_zero(&g_user_table_arena[i * 4096u], count * 4096u);
        return address;
    }
    return 0;
}

uint32_t arm32_user_table_alloc_l1_v13(uint32_t asid)
{
    return alloc_pages(asid, 0xffffu, PAGE_L1, ARM32_USER_L1_PAGES, 16384u);
}

uint32_t arm32_user_table_alloc_l2_v13(uint32_t asid, uint32_t l1_index)
{
    if (l1_index >= 4096u) return 0;
    return alloc_pages(asid, l1_index, PAGE_L2, 1, 4096u);
}

int arm32_user_table_free_space_v13(uint32_t asid, uint32_t root)
{
    uint32_t i, root_index, found_root = 0;
    uint32_t start = arm32_user_table_arena_start_v13();
    if (!g_user_table_ready || !asid || root < start || root >= arm32_user_table_arena_end_v13() ||
        (root & 0x3fffu)) return 0;
    root_index = (root - start) / 4096u;
    for (i = 0; i < ARM32_USER_L1_PAGES; ++i)
        if (g_user_table_ledger[root_index + i].kind == PAGE_L1 &&
            g_user_table_ledger[root_index + i].address_space_id == asid) found_root++;
    if (found_root != ARM32_USER_L1_PAGES) return 0;
    for (i = 0; i < ARM32_USER_TABLE_PAGE_COUNT; ++i) {
        if (g_user_table_ledger[i].address_space_id == asid) {
            bytes_zero(&g_user_table_arena[i * 4096u], 4096u);
            bytes_zero((volatile uint8_t *)&g_user_table_ledger[i],
                       sizeof g_user_table_ledger[i]);
        }
    }
    return 1;
}

static uint32_t read_ttbr0(void)
{
    uint32_t value;
#if defined(__arm__)
    __asm__ volatile("mrc p15, 0, %0, c2, c0, 0" : "=r"(value));
#else
    value = 0;
#endif
    return value & 0xffffc000u;
}

int arm32_user_l1_create_v1(uint32_t address_space_id, uint32_t *root_out)
{
    uint32_t root, kernel_root, i;
    if (!root_out || !g_user_table_ready || !address_space_id) return 0;
    root = arm32_user_table_alloc_l1_v13(address_space_id);
    if (!root) return 0;
    kernel_root = read_ttbr0();
    if (!kernel_root || kernel_root == root) {
        arm32_user_table_free_space_v13(address_space_id, root);
        return 0;
    }
    for (i=2048;i<4096;++i) ((uint32_t *)(uintptr_t)root)[i] =
        ((const uint32_t *)(uintptr_t)kernel_root)[i];
    *root_out = root;
    return 1;
}

static PageOwnerV13 *owner_for_address(uint32_t address)
{
    uint32_t start = arm32_user_table_arena_start_v13();
    if (address < start || address >= arm32_user_table_arena_end_v13()) return 0;
    return &g_user_table_ledger[(address-start)/4096u];
}

static void free_one_table_page(uint32_t address,uint32_t asid)
{
    PageOwnerV13 *o=owner_for_address(address);
    if(o&&o->address_space_id==asid&&o->kind==PAGE_L2) {
        bytes_zero((volatile uint8_t *)(uintptr_t)address,4096);
        bytes_zero((volatile uint8_t *)o,sizeof *o);
    }
}

int arm32_kernel_guard_page_install_v15(uint32_t root,uint32_t guard,uint32_t cpu)
{
    const uint32_t owner=0xfffffff0u; uint32_t idx,section,l2,base,attrs,i;
    GuardLeaseV15 *lease;
    if(!arm32_cpu_slot_valid_v12(cpu)||(guard&0xfffu)||!root||(root&0x3fffu)) return 0;
    lease=&g_guard_leases[cpu]; if(lease->active) return 0;
    idx=guard>>20; section=((uint32_t *)(uintptr_t)root)[idx];
    if((section&3u)!=2u) return 0;
    l2=arm32_user_table_alloc_l2_v13(owner,idx); if(!l2) return 0;
    base=section&0xfff00000u; attrs=arm32_section_attrs_to_small_v15(section);
    for(i=0;i<256;++i) ((uint32_t *)(uintptr_t)l2)[i]=(base+i*4096u)|attrs;
    ((uint32_t *)(uintptr_t)l2)[(guard>>12)&255u]=0;
    lease->root=root; lease->guard_va=guard; lease->original_section=section;
    lease->l2=l2; lease->active=1;
    ((uint32_t *)(uintptr_t)root)[idx]=(l2&ARM32_L1_COARSE_BASE_MASK)|ARM32_L1_COARSE_PAGE_TABLE;
#if defined(__arm__)
    __asm__ volatile("dsb sy\n\tmcr p15,0,%0,c8,c7,1\n\tdsb sy\n\tisb"::"r"(guard):"memory");
#endif
    return 1;
}

int arm32_kernel_guard_page_restore_v15(uint32_t root,uint32_t guard,uint32_t cpu)
{
    const uint32_t owner=0xfffffff0u; GuardLeaseV15 *l;
    if(!arm32_cpu_slot_valid_v12(cpu)) return 0; l=&g_guard_leases[cpu];
    if(!l->active||l->root!=root||l->guard_va!=guard||
       (((uint32_t *)(uintptr_t)root)[guard>>20]&ARM32_L1_COARSE_BASE_MASK)!=l->l2) return 0;
    ((uint32_t *)(uintptr_t)root)[guard>>20]=l->original_section;
#if defined(__arm__)
    __asm__ volatile("dsb sy\n\tmcr p15,0,%0,c8,c7,1\n\tdsb sy\n\tisb"::"r"(guard):"memory");
#endif
    free_one_table_page(l->l2,owner); bytes_zero((volatile uint8_t *)l,sizeof *l); return 1;
}

int arm32_user_l1_map_v1(uint32_t root, uint32_t va, uint32_t pa, uint32_t flags)
{
    uint32_t l1i, l2i, l1e, l2, attrs;
    PageOwnerV13 *root_owner, *l2_owner;
    if (!arm32_user_map_flags_valid_v12(flags) || (root & 0x3fffu) ||
        (va & 0xfffu) || (pa & 0xfffu) || va >= 0x80000000u) return 0;
    root_owner=owner_for_address(root);
    if (!root_owner || root_owner->kind != PAGE_L1 || !root_owner->address_space_id) return 0;
    l1i=va>>20; l2i=(va>>12)&255u;
    l1e=((uint32_t *)(uintptr_t)root)[l1i];
    if ((l1e&3u)==2u) return 0;
    if ((l1e&3u)==0u) {
        l2=arm32_user_table_alloc_l2_v13(root_owner->address_space_id,l1i);
        if (!l2) return 0;
        ((uint32_t *)(uintptr_t)root)[l1i]=(l2&ARM32_L1_COARSE_BASE_MASK)|ARM32_L1_COARSE_PAGE_TABLE;
    } else if ((l1e&3u)==1u) l2=l1e&ARM32_L1_COARSE_BASE_MASK;
    else return 0;
    l2_owner=owner_for_address(l2);
    if (!l2_owner || l2_owner->kind!=PAGE_L2 ||
        l2_owner->address_space_id!=root_owner->address_space_id ||
        l2_owner->l1_index!=l1i) return 0;
    if (((uint32_t *)(uintptr_t)l2)[l2i]!=0) return 0;
    attrs=arm32_user_l2_attrs_v12(flags);
    if (!attrs) return 0;
    ((uint32_t *)(uintptr_t)l2)[l2i]=(pa&ARM32_L2_BASE_MASK)|attrs;
#if defined(__arm__)
    __asm__ volatile("dsb sy\n\tmcr p15,0,%0,c8,c7,1\n\tdsb sy\n\tisb"::"r"(va):"memory");
#endif
    return 1;
}

int arm32_user_l1_destroy_v1(uint32_t root, uint32_t asid)
{
    if (read_ttbr0()==root) return 0;
#if defined(__arm__)
    __asm__ volatile("dsb sy\n\tmcr p15,0,%0,c8,c7,0\n\tdsb sy\n\tisb"::"r"(root):"memory");
#endif
    return arm32_user_table_free_space_v13(asid,root);
}

static uint64_t load64le(const uint8_t *p)
{
    uint64_t x = 0; unsigned i;
    for (i = 0; i < 8; ++i) x |= (uint64_t)p[i] << (8u * i);
    return x;
}
static uint64_t rol64(uint64_t x, unsigned n) { return (x << n) | (x >> (64u - n)); }
#define SIPROUND do { v0+=v1; v1=rol64(v1,13); v1^=v0; v0=rol64(v0,32); \
 v2+=v3; v3=rol64(v3,16); v3^=v2; v0+=v3; v3=rol64(v3,21); v3^=v0; \
 v2+=v1; v1=rol64(v1,17); v1^=v2; v2=rol64(v2,32); } while (0)

static uint64_t siphash24_bytes(const uint8_t key[16], const uint8_t *msg, unsigned len)
{
    uint64_t k0=load64le(key), k1=load64le(key+8), m, b=((uint64_t)len)<<56;
    uint64_t v0=0x736f6d6570736575ULL^k0, v1=0x646f72616e646f6dULL^k1;
    uint64_t v2=0x6c7967656e657261ULL^k0, v3=0x7465646279746573ULL^k1;
    unsigned i, tail = len & 7u;
    for (i=0;i+8<=len;i+=8) { m=load64le(msg+i); v3^=m; SIPROUND; SIPROUND; v0^=m; }
    while (tail) { --tail; b |= (uint64_t)msg[i + tail] << (8u * tail); }
    v3^=b; SIPROUND; SIPROUND; v0^=b; v2^=0xff; SIPROUND; SIPROUND; SIPROUND; SIPROUND;
    return v0^v1^v2^v3;
}

uint64_t arm32_token_siphash24_v13(const uint8_t key[16], const uint8_t msg[72])
{
    return siphash24_bytes(key, msg, 72);
}

int arm32_token_siphash24_kat_v13(void)
{
    uint8_t key[16], msg[15]; unsigned i;
    for (i=0;i<16;++i) key[i]=(uint8_t)i;
    for (i=0;i<15;++i) msg[i]=(uint8_t)i;
    /* Aumasson/Bernstein canonical SipHash-2-4 vector, length 15. */
    return siphash24_bytes(key, msg, 15) == UINT64_C(0xa129ca6149be45e5);
}

uint32_t arm32_platform_cpu_id_v12(void)
{
    uint32_t mpidr;
#if defined(__arm__)
    __asm__ volatile("mrc p15,0,%0,c0,c0,5":"=r"(mpidr));
#else
    mpidr=0;
#endif
    return mpidr&0xffu;
}

static uint32_t ct_tag_equal(uint64_t tag, const Arm32UserHandoffTokenV1 *t)
{
    uint32_t diff=(uint32_t)tag^t->auth_tag_lo;
    diff|=(uint32_t)(tag>>32)^t->auth_tag_hi;
    diff|=(uint32_t)(0u-diff); return (diff>>31)^1u;
}
static void token_retag(Arm32UserHandoffTokenV1 *t)
{
    uint8_t input[72]; uint64_t tag;
    arm32_token_mac_input_v11(input,t);
    tag=arm32_token_siphash24_v13(g_token_key,input);
    t->auth_tag_lo=(uint32_t)tag; t->auth_tag_hi=(uint32_t)(tag>>32);
    bytes_zero(input,sizeof input);
}

int arm32_token_registry_bootstrap_v11(uint32_t cpu_count, uint8_t secret[16])
{
    unsigned i; int valid=secret && cpu_count && cpu_count<=ARM32_MAX_CPU_SLOTS &&
        !g_token_registry_ready && arm32_boot_secret_valid_v12(secret) &&
        arm32_token_siphash24_kat_v13();
    if (valid) { for(i=0;i<16;++i) g_token_key[i]=secret[i]; g_token_registry_ready=1; }
    if (secret) arm32_boot_secret_wipe_v12(secret);
    return valid;
}

int arm32_token_issue_v11(uint32_t cpu, Arm32UserHandoffTokenV1 *t,
 uint32_t task, uint32_t gen, uint32_t asid, uint32_t root, uint64_t nonce,
 uint32_t svc_top, uint32_t supervisor_pc, uint32_t kernel_root)
{
    if (!g_token_registry_ready || !arm32_cpu_slot_valid_v12(cpu) || !t ||
        g_active_tokens[cpu] || !task || !gen || !asid || !root || (root&0x3fffu) ||
        !svc_top || (svc_top&7u) || !supervisor_pc || !kernel_root) return 0;
    bytes_zero((volatile uint8_t *)t,sizeof *t);
    t->magic=ARM32_HANDOFF_TOKEN_MAGIC; t->version=ARM32_USER_ABI_VERSION;
    t->task_id=task; t->task_generation=gen; t->address_space_id=asid;
    t->user_ttbr0_root=root; t->nonce_lo=(uint32_t)nonce; t->nonce_hi=(uint32_t)(nonce>>32);
    t->supervisor_sp=svc_top; t->supervisor_pc=supervisor_pc; t->kernel_ttbr0_root=kernel_root;
    t->lifecycle_state=1; t->expected_frame_sp=arm32_expected_svc_frame_sp(svc_top);
    token_retag(t); g_active_tokens[cpu]=t; return 1;
}
Arm32UserHandoffTokenV1 *arm32_token_lookup_active_v11(uint32_t cpu)
{ return g_token_registry_ready&&arm32_cpu_slot_valid_v12(cpu)?g_active_tokens[cpu]:0; }
int arm32_token_authenticate_v11(uint32_t cpu,const Arm32SvcFrameV1 *f,uint32_t root)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu); uint8_t input[72]; uint64_t tag;
    if(!t||!f||(uint32_t)(uintptr_t)f!=t->expected_frame_sp||root!=t->user_ttbr0_root||
       (f->spsr&ARM32_CPSR_MODE_MASK)!=ARM32_CPSR_USR) return 0;
    arm32_token_mac_input_v11(input,t); tag=arm32_token_siphash24_v13(g_token_key,input);
    bytes_zero(input,sizeof input); return ct_tag_equal(tag,t);
}
int arm32_token_advance_v11(uint32_t cpu,uint32_t expected,uint32_t next)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu);
    if(!t||t->lifecycle_state!=expected||next!=expected+1||next>4) return 0;
    t->lifecycle_state=next; t->syscall_sequence++; token_retag(t); return 1;
}
int arm32_token_revoke_v11(uint32_t cpu,uint32_t task,uint32_t gen)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu);
    if(!t||t->task_id!=task||t->task_generation!=gen||t->lifecycle_state!=4) return 0;
    g_active_tokens[cpu]=0; bytes_zero((volatile uint8_t *)t,sizeof *t); return 1;
}

int arm32_svc_dispatch_disposition_v14(uint32_t cpu,const Arm32SvcFrameV1 *f,
 uint32_t root,Arm32SvcDispositionV14 *out)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu);
    if(!out) return 0;
    bytes_zero((volatile uint8_t *)out,sizeof *out);
    out->status=ARM32_DISPOSITION_BAD_AUTH; out->action=ARM32_DISPOSITION_REJECT;
    if(!t||!f||!arm32_token_authenticate_v11(cpu,f,root)) return 1;
    out->task_id=t->task_id; out->task_generation=t->task_generation;
    out->syscall_sequence=t->syscall_sequence;
    out->auth_receipt_lo=t->auth_tag_lo; out->auth_receipt_hi=t->auth_tag_hi;
    out->observed_ttbr0=root; out->frame_sp=(uint32_t)(uintptr_t)f;
    out->return_pc=f->return_pc; out->spsr=f->spsr;
    if(f->r[7]==ARM32_SVC_WRITE_STDOUT && f->r[0]<=255u) {
        out->action=ARM32_DISPOSITION_STDOUT_BYTE; out->status=ARM32_DISPOSITION_OK;
        out->stdout_byte=f->r[0]; return 1;
    }
    if(f->r[7]==ARM32_SVC_EXIT && f->r[0]==ARM32_EXPECTED_EXIT) {
        out->action=ARM32_DISPOSITION_EXIT; out->status=ARM32_DISPOSITION_OK;
        out->exit_code=f->r[0]; return 1;
    }
    out->status=(f->r[7]==ARM32_SVC_WRITE_STDOUT||f->r[7]==ARM32_SVC_EXIT)?
        ARM32_DISPOSITION_BAD_PAYLOAD:ARM32_DISPOSITION_BAD_SYSCALL;
    out->action=ARM32_DISPOSITION_FAULT; out->fault_code=out->status;
    return 1;
}

enum Arm32SvcActionV1 arm32_scheduler_commit_disposition_v14(
 uint32_t cpu,const Arm32SvcDispositionV14 *d)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu);
    if(!t||!d||d->status!=ARM32_DISPOSITION_OK||d->reserved0||d->reserved1||
       d->task_id!=t->task_id||d->task_generation!=t->task_generation||
       d->syscall_sequence!=t->syscall_sequence||d->auth_receipt_lo!=t->auth_tag_lo||
       d->auth_receipt_hi!=t->auth_tag_hi||d->observed_ttbr0!=t->user_ttbr0_root||
       d->frame_sp!=t->expected_frame_sp||d->spsr!=ARM32_CPSR_USR) return ARM32_SVC_ACTION_REJECT;
    if(d->action==ARM32_DISPOSITION_STDOUT_BYTE&&d->stdout_byte<=255u&&
       !d->exit_code&&!d->fault_code&&t->lifecycle_state==2) {
        if(g_stdout_len[cpu]>=ARM32_STDOUT_CAPTURE_BYTES) return ARM32_SVC_ACTION_REJECT;
        g_stdout[cpu][g_stdout_len[cpu]++]=(uint8_t)d->stdout_byte;
        t->syscall_sequence++; token_retag(t); return ARM32_SVC_ACTION_RETURN_USER;
    }
    if(d->action==ARM32_DISPOSITION_EXIT&&d->exit_code==ARM32_EXPECTED_EXIT&&
       !d->stdout_byte&&!d->fault_code&&t->lifecycle_state==2) {
        t->lifecycle_state=3; t->syscall_sequence++; token_retag(t);
        return ARM32_SVC_ACTION_RESUME_SUPERVISOR;
    }
    return ARM32_SVC_ACTION_REJECT;
}

uint32_t arm32_scheduler_stdout_len_v14(uint32_t cpu)
{ return arm32_cpu_slot_valid_v12(cpu)?g_stdout_len[cpu]:0; }
int arm32_scheduler_stdout_copy_v14(uint32_t cpu,uint8_t *out,uint32_t cap)
{
    uint32_t i,n;
    if(!arm32_cpu_slot_valid_v12(cpu)||!out) return 0;
    n=g_stdout_len[cpu]; if(cap<n) return 0;
    for(i=0;i<n;++i) out[i]=g_stdout[cpu][i]; return 1;
}
int arm32_scheduler_reap_v14(uint32_t cpu,uint32_t task,uint32_t gen)
{
    Arm32UserHandoffTokenV1 *t=arm32_token_lookup_active_v11(cpu);
    uint32_t asid,root;
    if(!t||t->task_id!=task||t->task_generation!=gen||t->lifecycle_state!=3) return 0;
    asid=t->address_space_id; root=t->user_ttbr0_root;
    if(!arm32_token_advance_v11(cpu,3,4)) return 0;
    if(!arm32_user_frames_free_v15(asid)) return 0;
    if(!arm32_user_l1_destroy_v1(root,asid)) return 0;
    return arm32_token_revoke_v11(cpu,task,gen);
}

uint32_t arm32_kernel_ttbr0_root_v16(void)
{
    return read_ttbr0();
}

extern int arm32_fsexec_loan_v16(const uint8_t **bytes_out,
                                 uint32_t *len_out);
extern int arm32_fsexec_release_v16(const uint8_t *bytes,
                                    uint32_t len);
extern int arm32_fsexec_resume_prepare_v16(
    uint32_t task_id, uint32_t task_generation,
    uint32_t kernel_root, uint32_t svc_guard_va);
extern uint32_t arm32_fsexec_supervisor_resume_pc_v16(void);
extern const uint32_t arm32_vector_table_v12[];
extern void arm32_vector_install_v1(uint32_t vector_phys);
extern int arm32_enter_user_v1(Arm32UserHandoffTokenV1 *token,
                               uint32_t entry, uint32_t user_sp);

static Arm32UserHandoffTokenV1 g_arm32_fsexec_token_v16;
static uint32_t g_arm32_fsexec_generation_v16;

static uint64_t arm32_fsexec_nonce_token_v16(const uint8_t *bytes,
                                              uint32_t len)
{
    uint64_t hash = 1469598103934665603ULL;
    uint32_t i;
    for (i = 0; i < len; ++i) {
        hash ^= bytes[i];
        hash *= 1099511628211ULL;
    }
    return hash ? hash : 1ULL;
}

int arm32_fsexec_launch_v16(void)
{
    const uint8_t *elf = 0;
    uint8_t nonce[96];
    uint32_t elf_len = 0, nonce_len, cpu, kernel_root, generation, asid;
    uint64_t nonce_token;
    Arm32StagedImageV15 staged;

    cpu = arm32_platform_cpu_id_v12();
    kernel_root = arm32_kernel_ttbr0_root_v16();
    if (cpu >= ARM32_MAX_CPU_SLOTS || !kernel_root ||
        !arm32_user_table_arena_init_v13(0x40000000u, 0x48000000u) ||
        !arm32_user_frame_arena_init_v15(0x40000000u, 0x48000000u)) return 0;
    arm32_vector_install_v1((uint32_t)(uintptr_t)arm32_vector_table_v12);
    if (!arm32_fsexec_loan_v16(&elf, &elf_len)) return 0;
    nonce_len = arm32_qemu_nonce_read_v15(nonce);
    if (!nonce_len) { arm32_fsexec_release_v16(elf, elf_len); return 0; }
    nonce_token = arm32_fsexec_nonce_token_v16(nonce, nonce_len);
    bytes_zero(nonce, sizeof nonce);
    generation = ++g_arm32_fsexec_generation_v16;
    if (!generation) generation = ++g_arm32_fsexec_generation_v16;
    asid = 0x1000u + generation;
    if (!arm32_stage_elf32_v15(asid, kernel_root, cpu, elf, elf_len, &staged)) {
        arm32_fsexec_release_v16(elf, elf_len);
        return 0;
    }
    if (!arm32_fsexec_release_v16(elf, elf_len) ||
        !arm32_fsexec_resume_prepare_v16(
            1u, generation, kernel_root, staged.svc_guard_va) ||
        !arm32_token_issue_v11(
            cpu, &g_arm32_fsexec_token_v16, 1u, generation, asid,
            staged.user_root, nonce_token, staged.svc_stack_top,
            arm32_fsexec_supervisor_resume_pc_v16(), kernel_root)) {
        arm32_kernel_guard_page_restore_v15(kernel_root, staged.svc_guard_va, cpu);
        arm32_user_frames_free_v15(asid);
        arm32_user_l1_destroy_v1(staged.user_root, asid);
        return 0;
    }
    return arm32_enter_user_v1(
        &g_arm32_fsexec_token_v16, staged.entry, staged.user_sp);
}

enum Arm32SvcActionV1 arm32_svc_dispatch_v1(Arm32SvcFrameV1 *f,
 Arm32UserHandoffTokenV1 *ignored,uint32_t root)
{
    Arm32SvcDispositionV14 d; uint32_t cpu=arm32_platform_cpu_id_v12();
    (void)ignored;
    if(!arm32_svc_dispatch_disposition_v14(cpu,f,root,&d)) return ARM32_SVC_ACTION_REJECT;
    return arm32_scheduler_commit_disposition_v14(cpu,&d);
}

/* ARM virt exposes up to 32 modern virtio-mmio transports at 0x0a000000,
 * spaced by 0x200. This single boot owner accepts device id 4 only. */
#define ARM32_VIRTIO_MMIO_BASE 0x0a000000u
#define ARM32_VIRTIO_MMIO_STRIDE 0x200u
#define ARM32_VIRTIO_MMIO_SLOTS 32u
#define ARM32_VIRTIO_MAGIC 0x74726976u
#define ARM32_VIRTIO_RNG_ID 4u
#define ARM32_RNG_POLL_LIMIT 100000u
#define ARM32_RNG_COMPLETION_LIMIT 16u
static uint8_t g_arm32_rng_queue[4096] __attribute__((aligned(4096),section(".arm32.virtio_rng.v16")));

static void rng_barrier(void)
{
#if defined(__arm__)
    __asm__ volatile("dmb sy" ::: "memory");
#else
    __asm__ volatile("" ::: "memory");
#endif
}
static void rng_wipe(uint8_t *p,uint32_t n)
{ volatile uint8_t *v=p; while(n--) *v++=0; rng_barrier(); }
static void rng_addr(volatile uint32_t *m,uint32_t off,uintptr_t a)
{ m[off/4u]=(uint32_t)a; m[off/4u+1u]=0; }

static int arm32_rng_collect(volatile uint32_t *m,uint8_t key[16])
{
    volatile uint16_t *avail=(volatile uint16_t *)(g_arm32_rng_queue+64);
    volatile uint16_t *used=(volatile uint16_t *)(g_arm32_rng_queue+128);
    volatile uint32_t *desc=(volatile uint32_t *)g_arm32_rng_queue;
    uint32_t got=0,completions=0; uint16_t ai=0,ui=0;
    rng_wipe(g_arm32_rng_queue,sizeof g_arm32_rng_queue);
    m[0x70/4]=0; rng_barrier(); m[0x70/4]=3;
    m[0x14/4]=1; if(!(m[0x10/4]&1u)) return 0;
    m[0x24/4]=0; m[0x20/4]=0; m[0x24/4]=1; m[0x20/4]=1;
    m[0x70/4]=11; if(!(m[0x70/4]&8u)) return 0;
    m[0x30/4]=0; if(m[0x44/4]||m[0x34/4]<1u) return 0;
    m[0x38/4]=1; rng_addr(m,0x80,(uintptr_t)g_arm32_rng_queue);
    rng_addr(m,0x90,(uintptr_t)(g_arm32_rng_queue+64));
    rng_addr(m,0xa0,(uintptr_t)(g_arm32_rng_queue+128));
    m[0x44/4]=1; m[0x70/4]=15;
    while(got<16u&&completions++<ARM32_RNG_COMPLETION_LIMIT) {
        uintptr_t data=(uintptr_t)(g_arm32_rng_queue+256+got);
        desc[0]=(uint32_t)data; desc[1]=0;
        desc[2]=16u-got; ((volatile uint16_t *)desc)[6]=2; ((volatile uint16_t *)desc)[7]=0;
        avail[2]=0; avail[1]=++ai; rng_barrier(); m[0x50/4]=0;
        uint32_t polls=0; while(used[1]==ui&&polls++<ARM32_RNG_POLL_LIMIT) rng_barrier();
        if(used[1]==ui) goto fail;
        uint32_t n=((volatile uint32_t *)used)[2]; ++ui;
        { uint32_t next; if(!arm32_rng_accumulate_len_v16(got,n,&next)) goto fail; got=next; }
    }
    if(got!=16u) goto fail;
    { uint8_t aggregate=0; for(uint32_t i=0;i<16u;++i) { key[i]=g_arm32_rng_queue[256+i]; aggregate|=key[i]; }
      rng_wipe(g_arm32_rng_queue,sizeof g_arm32_rng_queue); m[0x70/4]=0; return aggregate!=0; }
fail:
    rng_wipe(key,16); rng_wipe(g_arm32_rng_queue,sizeof g_arm32_rng_queue); m[0x70/4]=0; return 0;
}

int arm32_virtio_rng_boot_key16_v16(uint8_t key[16],uint32_t *provenance)
{
    if(!key||!provenance) return 0; *provenance=ARM32_ENTROPY_UNAVAILABLE; rng_wipe(key,16);
    for(uint32_t slot=0;slot<ARM32_VIRTIO_MMIO_SLOTS;++slot) {
        volatile uint32_t *m=(volatile uint32_t *)(uintptr_t)(ARM32_VIRTIO_MMIO_BASE+slot*ARM32_VIRTIO_MMIO_STRIDE);
        if(m[0]==ARM32_VIRTIO_MAGIC&&m[1]==2u&&m[2]==ARM32_VIRTIO_RNG_ID&&arm32_rng_collect(m,key)) {
            *provenance=ARM32_ENTROPY_VIRTIO_RNG_MMIO; return 1;
        }
    }
    return 0;
}
int arm32_transition_entropy_bootstrap_v16(uint32_t cpu_count)
{
    uint8_t key[16]; uint32_t provenance=0;
    int ok=arm32_virtio_rng_boot_key16_v16(key,&provenance);
    if(ok&&provenance==ARM32_ENTROPY_VIRTIO_RNG_MMIO)
        ok=arm32_token_registry_bootstrap_v11(cpu_count,key);
    rng_wipe(key,sizeof key); return ok;
}
