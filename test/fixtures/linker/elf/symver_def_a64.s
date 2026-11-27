// libc.a shape (FreeBSD openat.o): the default-version name foo@@V_2 defines
// `foo`; foo@V_1 is a non-default alias that must not satisfy `foo`.
    .text
    .weak __impl_foo
    .type __impl_foo, %function
__impl_foo:
    mov w0, #42
    ret
    .symver __impl_foo, foo@@V_2
    .symver __impl_foo, foo@V_1
