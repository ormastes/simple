/* Included once by runtime_process.c after the canonical pipe registry.
 * Descriptor-only endpoints have no PID, process/group owner or kill API. */
#define BYTE_ENDPOINT_INTEGER_MAX_V1 INT64_C(1152921504606846975)
#if defined(__linux__)
static int byte_endpoint_binding_v1(const char* binding,int64_t size) {
    if(!binding||size!=64)return 0;
    for(int i=0;i<64;i++)if(!((binding[i]>='0'&&binding[i]<='9')||
        (binding[i]>='a'&&binding[i]<='f')))return 0;
    return 1;
}
static struct RtProcSlot* byte_endpoint_find_v1(int64_t generation,const char* binding,int64_t size) {
    if(generation<=0||!byte_endpoint_binding_v1(binding,size))return NULL;
    for(int i=0;i<RT_PROC_MAX;i++) {
        struct RtProcSlot* slot=&s_procs[i];
        if(slot->byte_endpoint&&!slot->closing&&slot->generation==(uint64_t)generation&&
            memcmp(slot->byte_binding,binding,64)==0)return slot;
    }
    return NULL;
}
static int byte_endpoint_lock_v1(void) {
    /* Never wait on a mutex inherited from a legacy-only registry user. Every
     * eligible stream/endpoint also establishes the canonical origin first. */
    if(!simple_local_unix_origin_v1())return -10;
    int error=pthread_mutex_trylock(&s_proc_lock);
    return error==0?0:(error==EBUSY?-7:-3);
}
#endif
static SplArray* byte_endpoint_receipt_v1(int64_t count) {
    SplArray* result=rt_array_new(count);
    if(!result)return NULL;
    for(int64_t i=0;i<count;i++)if(!rt_array_push(result,rt_value_int(0))) {
        rt_array_free(result);return NULL;
    }
    return result;
}
static void byte_endpoint_word_v1(SplArray* receipt,int64_t index,int64_t value) {
    (void)rt_array_set(receipt,index,rt_value_int(value));
}

int64_t simple_process_stdout_take_v1(int64_t pid,int64_t generation,
        const char* root,int64_t root_bytes,const char* identity,int64_t identity_bytes,int* fd) {
    if(fd)*fd=-1;
#if defined(__linux__)
    if(!fd)return -1;
    int status=byte_endpoint_lock_v1();if(status)return status;
    struct RtProcSlot* slot=stream_action_locked_v2(pid,generation,root,root_bytes,identity,identity_bytes);
    if(!slot)status=-2;
    else if(slot->stdout_started||slot->stdout_state!=0||slot->stdout_fd<0)status=-13;
    else {
        *fd=slot->stdout_fd;slot->stdout_fd=-1;
        /* Export is neither EOF nor process termination. Old readers fail. */
        slot->stdout_state=-4;status=0;
    }
    pthread_mutex_unlock(&s_proc_lock);return status;
#else
    (void)pid;(void)generation;(void)root;(void)root_bytes;(void)identity;(void)identity_bytes;return -4;
#endif
}

int64_t simple_process_byte_adopt_v1(int fd,const char* binding,int64_t binding_bytes,int64_t* generation) {
    if(generation)*generation=0;
#if defined(__linux__)
    if(!generation||fd<0||!byte_endpoint_binding_v1(binding,binding_bytes))return -1;
    if(!simple_local_unix_origin_v1())return -10;
    struct stat observed;int flags=fcntl(fd,F_GETFL),descriptor_flags=fcntl(fd,F_GETFD);
    if(fstat(fd,&observed)||!S_ISFIFO(observed.st_mode)||flags<0||descriptor_flags<0||
        (flags&O_ACCMODE)!=O_RDONLY||!(flags&O_NONBLOCK)||!(descriptor_flags&FD_CLOEXEC))return -1;
    int status=byte_endpoint_lock_v1();if(status)return status;
    struct RtProcSlot* slot=NULL;
    if(s_proc_generation<(uint64_t)BYTE_ENDPOINT_INTEGER_MAX_V1)slot=proc_alloc_locked(false);
    if(!slot)status=-5;
    else {
        slot->pid=0;slot->byte_endpoint=true;slot->stdout_fd=fd;
        memcpy(slot->byte_binding,binding,64);slot->byte_binding[64]=0;
        *generation=(int64_t)slot->generation;status=0;
    }
    pthread_mutex_unlock(&s_proc_lock);return status;
#else
    (void)fd;(void)binding;(void)binding_bytes;return -4;
#endif
}

static int64_t byte_endpoint_validate_impl_v1(int64_t generation,const char* binding,int64_t binding_bytes) {
#if defined(__linux__)
    int status=byte_endpoint_lock_v1();if(status)return status;
    status=byte_endpoint_find_v1(generation,binding,binding_bytes)?0:-2;
    pthread_mutex_unlock(&s_proc_lock);return status;
#else
    (void)generation;(void)binding;(void)binding_bytes;return -4;
#endif
}
static int64_t byte_endpoint_state_impl_v1(int64_t generation,const char* binding,int64_t binding_bytes) {
#if defined(__linux__)
    int status=byte_endpoint_lock_v1();if(status)return status;
    struct RtProcSlot* slot=byte_endpoint_find_v1(generation,binding,binding_bytes);
    status=slot?slot->stdout_state:-2;
    pthread_mutex_unlock(&s_proc_lock);return status;
#else
    (void)generation;(void)binding;(void)binding_bytes;return -4;
#endif
}
static SplArray* byte_endpoint_read_impl_v1(int64_t generation,const char* binding,int64_t binding_bytes) {
#if defined(__linux__)
    if(!simple_local_unix_origin_v1())return NULL;
#endif
    SplArray* receipt=byte_endpoint_receipt_v1(PIPED_TEXT_CAP+3);if(!receipt)return NULL;
#if defined(__linux__)
    int status=byte_endpoint_lock_v1();
    if(status){byte_endpoint_word_v1(receipt,0,status);return receipt;}
    struct RtProcSlot* slot=byte_endpoint_find_v1(generation,binding,binding_bytes);
    if(!slot)status=-2;
    else {
        size_t length=0;
        const char* bytes=posix_core_rt_process_read_stdout_slot_count(slot,&length);
        status=slot->stdout_state<0?-3:0;
        byte_endpoint_word_v1(receipt,1,slot->stdout_state==1);
        byte_endpoint_word_v1(receipt,2,(int64_t)length);
        for(size_t i=0;i<length;i++)byte_endpoint_word_v1(receipt,(int64_t)i+3,(uint8_t)bytes[i]);
    }
    pthread_mutex_unlock(&s_proc_lock);byte_endpoint_word_v1(receipt,0,status);
#else
    (void)generation;(void)binding;(void)binding_bytes;byte_endpoint_word_v1(receipt,0,-4);
#endif
    return receipt;
}
static SplArray* byte_endpoint_close_impl_v1(int64_t generation,const char* binding,int64_t binding_bytes) {
#if defined(__linux__)
    if(!simple_local_unix_origin_v1())return NULL;
#endif
    SplArray* receipt=byte_endpoint_receipt_v1(2);if(!receipt)return NULL;
#if defined(__linux__)
    int status=byte_endpoint_lock_v1();
    if(status){byte_endpoint_word_v1(receipt,0,status);return receipt;}
    struct RtProcSlot* slot=byte_endpoint_find_v1(generation,binding,binding_bytes);
    if(!slot)status=-2;
    else {
        int fd=slot->stdout_fd;slot->stdout_fd=-1;
        /* Linux consumes close even on error. Never retry a recycled raw FD. */
        status=fd>=0&&close(fd)!=0?-3:0;
        proc_free_locked(slot);byte_endpoint_word_v1(receipt,1,1);
    }
    pthread_mutex_unlock(&s_proc_lock);byte_endpoint_word_v1(receipt,0,status);
#else
    (void)generation;(void)binding;(void)binding_bytes;byte_endpoint_word_v1(receipt,0,-4);
#endif
    return receipt;
}
