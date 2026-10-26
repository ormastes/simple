#ifndef SIMPLE_RUNTIME_DICT_SNAPSHOT_V1_H
#define SIMPLE_RUNTIME_DICT_SNAPSHOT_V1_H
#include <stdint.h>
#include <stddef.h>
/* C-private compiler owner ABI. Metadata is NOT confinement authority. The
 * actual request owner excludes aliases/tasks/callbacks throughout the call
 * sequence; pure/hosted have no admitted implementation. */
typedef struct RtDictSnapshotV1 {
    int64_t dictionary, owner, epoch, backing, capacity, length, tombstones;
    uintptr_t entries;
} RtDictSnapshotV1;
int64_t rt_dict_snapshot_observation_bound_v1(void);
int64_t rt_dict_snapshot_observe_v1(int64_t dictionary,int64_t work,RtDictSnapshotV1* out);
int64_t rt_array_snapshot_bound_v1(int64_t length,int64_t metric);
typedef struct RtArraySnapshotV1 {
    int64_t array, capacity;
    uintptr_t data;
    uint64_t birth;
    uint32_t owner;
    int consumed;
} RtArraySnapshotV1;
/* Compiler-private bridge is supported on the actual 64-bit native ABI only.
 * These are record layout contracts, never Simple object layout assumptions. */
#if UINTPTR_MAX == UINT64_MAX
_Static_assert(sizeof(RtDictSnapshotV1)==64,"snapshot observation ABI size");
_Static_assert(offsetof(RtDictSnapshotV1,dictionary)==0,"snapshot dictionary offset");
_Static_assert(offsetof(RtDictSnapshotV1,owner)==8,"snapshot owner offset");
_Static_assert(offsetof(RtDictSnapshotV1,epoch)==16,"snapshot epoch offset");
_Static_assert(offsetof(RtDictSnapshotV1,backing)==24,"snapshot backing offset");
_Static_assert(offsetof(RtDictSnapshotV1,capacity)==32,"snapshot capacity offset");
_Static_assert(offsetof(RtDictSnapshotV1,length)==40,"snapshot length offset");
_Static_assert(offsetof(RtDictSnapshotV1,tombstones)==48,"snapshot tombstones offset");
_Static_assert(offsetof(RtDictSnapshotV1,entries)==56,"snapshot entries offset");
_Static_assert(sizeof(RtArraySnapshotV1)==40,"snapshot array witness ABI size");
_Static_assert(offsetof(RtArraySnapshotV1,array)==0,"array witness array offset");
_Static_assert(offsetof(RtArraySnapshotV1,capacity)==8,"array witness capacity offset");
_Static_assert(offsetof(RtArraySnapshotV1,data)==16,"array witness data offset");
_Static_assert(offsetof(RtArraySnapshotV1,birth)==24,"array witness birth offset");
_Static_assert(offsetof(RtArraySnapshotV1,owner)==32,"array witness owner offset");
_Static_assert(offsetof(RtArraySnapshotV1,consumed)==36,"array witness consumed offset");
/* Other native targets may build the ordinary runtime, but have no admitted
 * private bridge layout. fill_publish refuses them explicitly. */
#endif
int64_t rt_array_snapshot_new_v1(int64_t length,int64_t work,int64_t fields,int64_t bytes,
    RtArraySnapshotV1* output);
int64_t rt_array_snapshot_dispose_v1(RtArraySnapshotV1* output,int64_t work);
int64_t rt_dict_snapshot_fill_bound_v1(int64_t capacity,int64_t length);
int64_t rt_dict_snapshot_fill_v1(int64_t dictionary,const RtDictSnapshotV1* expected,
    RtArraySnapshotV1* output,int64_t work);
/* Only actual fill success produces a typed bridge value. Failure preserves
 * unpublished output ownership; disposal refusal requires owner abort. */
int64_t rt_dict_snapshot_fill_publish_v1(int64_t dictionary,const RtDictSnapshotV1* expected,
    RtArraySnapshotV1* output,int64_t work);
#endif
