/* Host-independent ELF64 contract oracle for the MC/DC aspect object.
 * It deliberately uses one fixed buffer and performs no heap allocation. */
#define _POSIX_C_SOURCE 200809L
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

#define OBJECT_CAP (1024u * 1024u)
#define ITERATIONS 10000u

static unsigned char object_bytes[OBJECT_CAP];

static int in_bounds(size_t off, size_t count, size_t width, size_t size) {
    return off <= size && count <= (size - off) / width;
}

static int validate_object(const unsigned char *p, size_t n) {
    if (n < sizeof(Elf64_Ehdr)) return 10;
    const Elf64_Ehdr *eh = (const Elf64_Ehdr *)p;
    if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0 ||
        eh->e_ident[EI_CLASS] != ELFCLASS64 ||
        eh->e_ident[EI_DATA] != ELFDATA2LSB ||
        eh->e_type != ET_REL || eh->e_machine != EM_X86_64) return 11;
    if (eh->e_shnum > 64 ||
        !in_bounds((size_t)eh->e_shoff, eh->e_shnum, sizeof(Elf64_Shdr), n) ||
        eh->e_shstrndx >= eh->e_shnum) return 12;
    const Elf64_Shdr *sh = (const Elf64_Shdr *)(p + eh->e_shoff);
    const Elf64_Shdr *shstr = &sh[eh->e_shstrndx];
    if (!in_bounds(shstr->sh_offset, 1, shstr->sh_size, n)) return 13;
    const char *shnames = (const char *)(p + shstr->sh_offset);
    const Elf64_Shdr *symtab = NULL, *text = NULL, *rodata = NULL, *rela = NULL;
    unsigned alloc_nonempty = 0;
    for (unsigned i = 0; i < eh->e_shnum; ++i) {
        if (sh[i].sh_name >= shstr->sh_size) return 14;
        const char *name = shnames + sh[i].sh_name;
        if (sh[i].sh_type == SHT_REL) return 15;
        if (sh[i].sh_type == SHT_SYMTAB) symtab = &sh[i];
        if (!strcmp(name, ".text")) text = &sh[i];
        if (!strcmp(name, ".rodata")) rodata = &sh[i];
        if (!strcmp(name, ".rela.text")) rela = &sh[i];
        if ((sh[i].sh_flags & SHF_ALLOC) && sh[i].sh_size) ++alloc_nonempty;
    }
    if (!symtab || !text || !rodata || !rela || alloc_nonempty != 2) return 16;
    if ((text->sh_flags & (SHF_ALLOC | SHF_EXECINSTR | SHF_WRITE)) !=
        (SHF_ALLOC | SHF_EXECINSTR) ||
        (rodata->sh_flags & (SHF_ALLOC | SHF_EXECINSTR | SHF_WRITE)) != SHF_ALLOC)
        return 17;
    if (!symtab->sh_entsize || symtab->sh_link >= eh->e_shnum ||
        !in_bounds(symtab->sh_offset, symtab->sh_size / symtab->sh_entsize,
                   symtab->sh_entsize, n)) return 18;
    const Elf64_Shdr *strtab = &sh[symtab->sh_link];
    if (!in_bounds(strtab->sh_offset, 1, strtab->sh_size, n)) return 19;
    const char *names = (const char *)(p + strtab->sh_offset);
    const Elf64_Sym *syms = (const Elf64_Sym *)(p + symtab->sh_offset);
    const size_t symbol_count = symtab->sh_size / symtab->sh_entsize;
    if (symbol_count > 64) return 20;
    unsigned vector = 0, marker = 0, import = 0, globals = 0;
    size_t import_index = 0;
    for (size_t i = 0; i < symbol_count; ++i) {
        if (syms[i].st_name >= strtab->sh_size) return 21;
        const char *name = names + syms[i].st_name;
        if (ELF64_ST_BIND(syms[i].st_info) != STB_GLOBAL || !*name) continue;
        ++globals;
        if (!strcmp(name, "rt_mcdc_aspect_vector_v1") &&
            ELF64_ST_TYPE(syms[i].st_info) == STT_FUNC && syms[i].st_size) ++vector;
        else if (!strcmp(name,
            "rt_mcdc_aspect_vector_v1__abi_u64_u32_u64_u64_u64_u8_i32_v1") &&
            ELF64_ST_TYPE(syms[i].st_info) == STT_OBJECT && syms[i].st_size == 1) ++marker;
        else if (!strcmp(name, "rt_mcdc_record_compiled_vector_v1") &&
                 syms[i].st_shndx == SHN_UNDEF) { ++import; import_index = i; }
        else return 22;
    }
    if (globals != 3 || vector != 1 || marker != 1 || import != 1) return 23;
    if (rodata->sh_size != 1 || rodata->sh_offset >= n || p[rodata->sh_offset] != 1)
        return 24;
    if (rela->sh_type != SHT_RELA || rela->sh_entsize != sizeof(Elf64_Rela) ||
        rela->sh_info >= eh->e_shnum || &sh[rela->sh_info] != text ||
        !in_bounds(rela->sh_offset, rela->sh_size / sizeof(Elf64_Rela),
                   sizeof(Elf64_Rela), n)) return 25;
    const size_t reloc_count = rela->sh_size / sizeof(Elf64_Rela);
    if (!reloc_count || reloc_count > 64) return 26;
    const Elf64_Rela *relocs = (const Elf64_Rela *)(p + rela->sh_offset);
    for (size_t i = 0; i < reloc_count; ++i) {
        if (ELF64_R_SYM(relocs[i].r_info) != import_index ||
            ELF64_R_TYPE(relocs[i].r_info) != R_X86_64_PLT32 ||
            relocs[i].r_offset + 4 > text->sh_size) return 27;
    }
    return 0;
}

static uint64_t elapsed_ns(struct timespec a, struct timespec b) {
    return (uint64_t)(b.tv_sec - a.tv_sec) * UINT64_C(1000000000) +
           (uint64_t)(b.tv_nsec - a.tv_nsec);
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    int fd = open(argv[1], O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 3;
    size_t used = 0;
    while (used < OBJECT_CAP) {
        ssize_t got = read(fd, object_bytes + used, OBJECT_CAP - used);
        if (got < 0 && errno == EINTR) continue;
        if (got < 0) return 4;
        if (!got) break;
        used += (size_t)got;
    }
    unsigned char overflow;
    if (used == OBJECT_CAP && read(fd, &overflow, 1) != 0) return 5;
    if (close(fd) != 0) return 6;
    struct timespec begin, end;
    if (clock_gettime(CLOCK_MONOTONIC, &begin) != 0) return 7;
    int status = 0;
    for (unsigned i = 0; i < ITERATIONS; ++i) status |= validate_object(object_bytes, used);
    if (clock_gettime(CLOCK_MONOTONIC, &end) != 0) return 8;
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) != 0) return 9;
    if (status) { fprintf(stderr, "object validation failed: %d\n", status); return status; }
    printf("PASS object_bytes=%zu iterations=%u mean_ns=%" PRIu64
           " maxrss_kib=%ld heap_allocations=0\n",
           used, ITERATIONS, elapsed_ns(begin, end) / ITERATIONS, usage.ru_maxrss);
    return 0;
}
