/* Experimental Darwin kernel launch binding. Not a V4 provider capability.
 * The caller supplies an already trusted, architecture-specific CDHash. This
 * primitive does not validate dependency closure or manage child ownership.
 * Requires modern AMFI enforcement and private Apple SPI; fail closed if absent.
 */
#ifndef RUNTIME_SOSIX_DARWIN_SPAWN_CONSTRAINT_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_SPAWN_CONSTRAINT_PRIVATE_H
#include <spawn.h>
#include <stddef.h>
/* Storage must outlive posix_spawn: the private spawn attribute references the
 * policy bytes instead of owning them. Never return a temporary NSData buffer. */
typedef struct SosixDarwinSpawnConstraint {
    unsigned char bytes[16383];
    size_t length;
} SosixDarwinSpawnConstraint;
int sosix_darwin_spawn_constraint_attach(posix_spawnattr_t *attributes,
                                       const unsigned char *cdhash, size_t length,
                                       SosixDarwinSpawnConstraint *storage);
#endif
