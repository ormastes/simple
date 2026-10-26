#ifndef SIMPLE_RUNTIME_DICT_SNAPSHOT_V1_H
#define SIMPLE_RUNTIME_DICT_SNAPSHOT_V1_H
#include <stdint.h>
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
int64_t rt_array_snapshot_new_v1(int64_t length,int64_t work,int64_t fields,int64_t bytes,
    RtArraySnapshotV1* output);
int64_t rt_array_snapshot_dispose_v1(RtArraySnapshotV1* output,int64_t work);
int64_t rt_dict_snapshot_fill_bound_v1(int64_t capacity,int64_t length);
int64_t rt_dict_snapshot_fill_v1(int64_t dictionary,const RtDictSnapshotV1* expected,
    RtArraySnapshotV1* output,int64_t work);
#endif
