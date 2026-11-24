/* runtime_file_slurp_impl.h -- private read-to-EOF text loader shared by
 * runtime.c and runtime_native.c.
 *
 * Not a public header: include it exactly once, from one translation unit,
 * after <stdio.h>/<stdlib.h> and the rt_string_new prototype. Everything here
 * is static; the exported rt_file_read_text entry points stay hand-written in
 * each includer and only open the file before handing it here.
 *
 * Includer knobs (both default to libc):
 *   RT_FILE_SLURP_MALLOC(n)        allocator for the growable buffer
 *   RT_FILE_SLURP_REALLOC(p, n)    its matching realloc
 * runtime_native.c routes both through its allocation observer; runtime.c
 * uses plain malloc/realloc. The buffer is always released with free().
 *
 * Read to EOF into a growable buffer and keep the BYTE COUNT. strlen() on
 * spl_file_read's result stopped at the first NUL, so a binary file came
 * back as a NON-nil short text -- an ELF object's e_ident has a NUL at
 * offset 7, so a 1080-byte aarch64 `.o` read back as 7 bytes, and
 * FileFingerprint.from_file's sha256 fallback (which fires only on nil)
 * became dead code. The two lanes are paired by the push-rt-dual-implementation
 * ratchet and must not diverge, which is why one body serves both. Do NOT size
 * from fseek/ftell -- procfs and sysfs report 0, which is what the incident
 * spl_file_read's own comment records. */
#ifndef SIMPLE_RUNTIME_FILE_SLURP_IMPL_H
#define SIMPLE_RUNTIME_FILE_SLURP_IMPL_H

#ifndef RT_FILE_SLURP_MALLOC
#define RT_FILE_SLURP_MALLOC(n) malloc(n)
#endif
#ifndef RT_FILE_SLURP_REALLOC
#define RT_FILE_SLURP_REALLOC(p, n) realloc((p), (n))
#endif

/* Reads the rest of `f` into a RuntimeValue text and closes it. Returns nil
 * (RT_NIL == 3, TAG_SPECIAL payload 0) on allocation failure. */
static int64_t rt_file_slurp_text_close(FILE* f) {
    const int64_t rt_nil = 3;
    size_t cap = 4096;
    size_t len = 0;
    char* content = (char*)RT_FILE_SLURP_MALLOC(cap);
    if (!content) { fclose(f); return rt_nil; }
    for (;;) {
        if (len >= cap) {
            size_t new_cap = cap * 2;
            char* grown = (char*)RT_FILE_SLURP_REALLOC(content, new_cap);
            if (!grown) { free(content); fclose(f); return rt_nil; }
            content = grown;
            cap = new_cap;
        }
        size_t n = fread(content + len, 1, cap - len, f);
        len += n;
        if (n == 0) break;
    }
    fclose(f);
    int64_t result = rt_string_new((const uint8_t*)content, (uint64_t)len);
    free(content);
    return result;
}

#endif /* SIMPLE_RUNTIME_FILE_SLURP_IMPL_H */
