/* 32-bit native value availability only. No 64-bit raw ABI declarations,
 * child owner, capability claim or functional admission exists on this target. */
static SplArray* oiv1_32_unavailable_words(int64_t count,int64_t size,int64_t status_index) {
    SplArray* result=rt_array_new_with_cap_u64(count);
    RtCoreArray* array=rt_core_as_array((int64_t)(uintptr_t)result);
    if (!array) return NULL;
    memset(array->data,0,(size_t)count*8); array->len=count;
    ((uint64_t*)array->data)[0]=1; ((uint64_t*)array->data)[1]=(uint64_t)size;
    ((uint64_t*)array->data)[status_index]=7; /* Unsupported, never Ok */
    return result;
}
SplArray* rt_process_owned_interactive_v1_capabilities_value(void) { return oiv1_32_unavailable_words(16,128,2); }
SplArray* rt_process_owned_interactive_v1_deadline_value(int64_t timeout) { (void)timeout; return oiv1_32_unavailable_words(8,32,4); }
SplArray* rt_process_owned_interactive_v1_start_value(const uint8_t* command,uint64_t length,SplArray* args,
        int64_t clock,int64_t expires,int64_t in,int64_t out,int64_t err) {
    (void)command;(void)length;(void)args;(void)clock;(void)expires;(void)in;(void)out;(void)err;
    return oiv1_32_unavailable_words(32,256,2);
}
SplArray* rt_process_owned_interactive_v1_write_some_value(int64_t handle,SplArray* bytes,int64_t offset,
        int64_t maximum,int64_t expected,int64_t clock,int64_t expires) {
    (void)handle;(void)bytes;(void)offset;(void)maximum;(void)expected;(void)clock;(void)expires;
    return oiv1_32_unavailable_words(32,256,2);
}
int64_t* rt_process_owned_interactive_v1_poll_value(int64_t handle,int64_t clock,int64_t expires,
        int64_t wait,int64_t out,int64_t err) {
    (void)handle;(void)clock;(void)expires;(void)wait;(void)out;(void)err;
    SplArray* words=oiv1_32_unavailable_words(32,256,2);
    SplArray* output=rt_byte_array_new_len(0),*error=rt_byte_array_new_len(0); int64_t tuple=rt_tuple_new(3);
    if (!words || !output || !error || !tuple || !rt_tuple_set(tuple,0,(int64_t)(uintptr_t)output) ||
        !rt_tuple_set(tuple,1,(int64_t)(uintptr_t)error) || !rt_tuple_set(tuple,2,(int64_t)(uintptr_t)words)) {
        if (words) rt_array_free(words); if (output) rt_array_free(output); if (error) rt_array_free(error);
        if (tuple) rt_array_free((SplArray*)(uintptr_t)tuple); return NULL;
    }
    return (int64_t*)(uintptr_t)tuple;
}
SplArray* rt_process_owned_interactive_v1_close_stdin_value(int64_t h,int64_t c,int64_t e) {
    (void)h;(void)c;(void)e; return oiv1_32_unavailable_words(32,256,2);
}
SplArray* rt_process_owned_interactive_v1_cancel_value(int64_t h,int64_t c,int64_t e) {
    (void)h;(void)c;(void)e; return oiv1_32_unavailable_words(32,256,2);
}
SplArray* rt_process_owned_interactive_v1_collect_value(int64_t h,int64_t c,int64_t e,bool d) {
    (void)h;(void)c;(void)e;(void)d; return oiv1_32_unavailable_words(32,256,2);
}
SplArray* rt_process_owned_interactive_v1_release_value(int64_t h) {
    (void)h; return oiv1_32_unavailable_words(32,256,2);
}
