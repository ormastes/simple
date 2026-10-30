#include "runtime_sosix_darwin_spawn_constraint_private.h"
#import <Foundation/Foundation.h>
#include <dlfcn.h>
#include <errno.h>
#include <sys/sysctl.h>

/* libTLE is private SPI. Keep it dynamically optional and do not promote its
 * presence alone to a capability claim. Native negative controls qualify the
 * concrete host separately. Category zero enforces the supplied requirements;
 * other categories can have unrelated semantics and must never be accepted. */
@interface NSObject (SosixDarwinLightweightRequirement)
+ (id)withVersion:(NSInteger)version withConstraintCategory:(NSInteger)category
    withRequirements:(NSDictionary *)requirements withError:(NSError **)error;
- (NSData *)externalRepresentation;
@end

int sosix_darwin_spawn_constraint_attach(posix_spawnattr_t *attributes,
                                       const unsigned char *cdhash, size_t length,
                                       SosixDarwinSpawnConstraint *storage) {
    if (!attributes || !cdhash || length != 20 || !storage) return EINVAL;
    storage->length = 0;
    int allowed = 0; size_t allowed_size = sizeof(allowed);
    if (sysctlbyname("security.mac.amfi.launch_constraints_3rd_party_allowed",
                    &allowed, &allowed_size, NULL, 0) || allowed_size != sizeof(allowed) || allowed != 1)
        return ENOTSUP;
    @autoreleasepool {
        void *library = dlopen("/usr/lib/libTLE.dylib", RTLD_NOW | RTLD_LOCAL);
        if (!library) return ENOTSUP;
        int (*set_policy)(posix_spawnattr_t *, const char *, void *, size_t) =
            dlsym(RTLD_DEFAULT, "posix_spawnattr_setmacpolicyinfo_np");
        Class serializer = NSClassFromString(@"LWCR");
        int result = ENOTSUP;
        if (set_policy && [serializer respondsToSelector:
                @selector(withVersion:withConstraintCategory:withRequirements:withError:)]) {
            NSError *error = nil;
            NSData *hash = [NSData dataWithBytes:cdhash length:length];
            id requirement = [serializer withVersion:1 withConstraintCategory:0
                withRequirements:@{@"cdhash": hash} withError:&error];
            if (requirement && !error && [requirement respondsToSelector:@selector(externalRepresentation)]) {
                NSData *encoded = [requirement externalRepresentation];
                if ([encoded isKindOfClass:[NSData class]] && encoded.length && encoded.length <= sizeof(storage->bytes)) {
                    memcpy(storage->bytes, encoded.bytes, encoded.length);
                    storage->length = encoded.length;
                    result = set_policy(attributes, "AMFI", storage->bytes, storage->length);
                }
            }
        }
        dlclose(library);
        return result;
    }
}
