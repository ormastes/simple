#import <Foundation/Foundation.h>
#include "../runtime_sosix_darwin_signature_private.h"
#include <assert.h>
@interface NSObject (SosixRequirementParity)
+ (id)withVersion:(NSInteger)version withConstraintCategory:(NSInteger)category
    withRequirements:(NSDictionary *)requirements withError:(NSError **)error;
- (NSData *)externalRepresentation;
@end
int main(void) { @autoreleasepool {
    void *library=dlopen("/usr/lib/libTLE.dylib",RTLD_NOW|RTLD_LOCAL);assert(library);
    Class serializer=NSClassFromString(@"LWCR");assert(serializer);
    for(unsigned turn=0;turn<4;turn++) {
        unsigned char hash[20]={0},encoded[82];
        if(turn)for(size_t i=0;i<sizeof(hash);i++)hash[i]=(unsigned char)(turn*64+i);
        NSError *error=nil;
        id requirement=[serializer withVersion:1 withConstraintCategory:0
            withRequirements:@{@"cdhash":[NSData dataWithBytes:hash length:20]} withError:&error];
        assert(requirement && !error);NSData *expected=[requirement externalRepresentation];
        sosix_darwin_cdhash_requirement(hash,encoded);
        assert(expected.length==sizeof(encoded) && !memcmp(expected.bytes,encoded,sizeof(encoded)));
    }
    dlclose(library);
    puts("PASS: production LWCR encoding matches Apple serializer for zero and high-bit CDHashes");
} }
