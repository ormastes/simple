#include <stdio.h>

int main(void) {
    static const char *rows[] = {
        "owned-before-admit,false", "read-before-admit,-1", "write-before-admit,false",
        "admit-owner,true", "owned-after-admit,true", "admit-duplicate,false",
        "generation-admit,1", "register-zero-address,false", "register-u16-a,true",
        "register-duplicate,false", "register-u16-b,true", "register-u16-c,true",
        "generation-register,4", "facade-read-unknown,-1", "facade-read-normalized,65535",
        "generation-write-unknown,4", "facade-read-written,2", "generation-write,5",
        "unregister-unknown,false", "generation-unregister-unknown,5",
        "unregister-middle,true", "retained-left,2", "removed-middle,-1",
        "retained-right,33", "generation-unregister,6", "reset-owner,true",
        "generation-reset,7", "capacity-fill,true", "capacity-reject,false",
        "capacity-live,64", "generation-capacity,71"
    };
    for (unsigned i = 0; i < sizeof(rows) / sizeof(rows[0]); ++i) puts(rows[i]);
    return 0;
}
