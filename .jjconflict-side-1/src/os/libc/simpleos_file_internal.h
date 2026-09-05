#ifndef SIMPLEOS_FILE_INTERNAL_H
#define SIMPLEOS_FILE_INTERNAL_H
/*
 * The ONE definition of the opaque FILE object for the SimpleOS libc.
 *
 * `FILE` is `typedef struct __simpleos_FILE FILE;` in <stdio.h>, i.e. opaque to
 * every consumer. Before 2026-08-06 the tag was defined TWICE with incompatible
 * layouts — a 4-byte `{ int fd; }` in simpleos_libc.c (which sized the
 * stdin/stdout/stderr statics) and a 16-byte `{ fd; eof; error; mode; }` in
 * simpleos_fs.c (which fopen/fread/fwrite/feof/ferror actually used). Any
 * fread/fwrite on a standard stream therefore wrote up to 12 bytes past a
 * 4-byte static. See
 * doc/08_tracking/bug/simpleos_libc_file_struct_odr_mismatch_2026-08-06.md
 *
 * Every translation unit that needs the layout — including the one that
 * allocates the standard streams — MUST include this header and MUST NOT
 * redeclare the tag. A re-added local definition is now a hard compile error
 * (redefinition), which is the durable guard against this regressing.
 *
 * Deliberately free of #includes: simpleos_libc.c is built without the full
 * header set and forward-declares what it needs by hand.
 */

struct __simpleos_FILE {
    int fd;     /* underlying file descriptor                     */
    int eof;    /* end-of-file indicator   — feof()/clearerr()     */
    int error;  /* error indicator         — ferror()/clearerr()   */
    int mode;   /* open flags (O_RDONLY/O_WRONLY/... ) from fopen  */
};

/* ABI guard: the size is load-bearing across TUs (fopen/fdopen malloc it,
 * simpleos_libc.c statically allocates three of them). If this fires, the
 * layout changed in one place and the statics did not follow. */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(struct __simpleos_FILE) == 16,
               "struct __simpleos_FILE must stay 16 bytes: fopen()/fdopen() "
               "malloc() it and simpleos_libc.c allocates stdin/stdout/stderr "
               "as statics of this exact type");
#endif

#endif /* SIMPLEOS_FILE_INTERNAL_H */
