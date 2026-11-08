/* Included after the canonical connection helpers. No second registry/reader.
 * Binding bytes correlate application-verified receipts; they authenticate no
 * caller or lifecycle proof by themselves. */
#include "runtime_local_unix_bridge_v1.h"
static int lu_transfer_binding_v1(const char* value,int64_t size) {
    if(!value||size!=64)return 0;
    for(int i=0;i<64;i++)if(!((value[i]>='0'&&value[i]<='9')||(value[i]>='a'&&value[i]<='f')))return 0;
    return 1;
}
#if defined(__linux__)
/* Explicit receive admits at most ONE FD over the whole connection. On ANY
 * malformed/extra/truncated control, dispose every NEW fd, retaining original. */
static int lu_receive_control_v1(LuSlotV1* slot,struct msghdr* message,int allow) {
    int incoming[16],count=0,bad=(message->msg_flags&(MSG_CTRUNC|MSG_TRUNC))!=0;
    int ancillary=message->msg_controllen>0;
    for(struct cmsghdr* c=CMSG_FIRSTHDR(message);c;c=CMSG_NXTHDR(message,c)) {
        if(c->cmsg_len<CMSG_LEN(0)){bad=1;break;}
        if(c->cmsg_level!=SOL_SOCKET||c->cmsg_type!=SCM_RIGHTS){bad=1;continue;}
        size_t bytes=c->cmsg_len-CMSG_LEN(0),number=bytes/sizeof(int);
        if(bytes%sizeof(int))bad=1;
        int* descriptors=(int*)CMSG_DATA(c);
        for(size_t i=0;i<number;i++) {
            if(descriptors[i]<0){bad=1;continue;}
            if(count<16)incoming[count++]=descriptors[i];
            else{(void)close(descriptors[i]);bad=1;}
        }
    }
    if(ancillary&&count==0)bad=1;
    if(!allow&&ancillary)bad=1;
    if(count>1||(count&&slot->transfer_phase!=0))bad=1;
    if(bad){for(int i=0;i<count;i++)(void)close(incoming[i]);return -9;}
    if(count==1){slot->pending_fd=incoming[0];slot->transfer_phase=3;}
    return 0;
}
static ssize_t lu_send_bytes_v1(LuSlotV1* slot,const unsigned char* data,size_t maximum) {
    if(slot->transfer_phase!=1)return send(slot->fd,data,maximum,MSG_NOSIGNAL);
    if(slot->pending_fd<0){errno=EINVAL;return -1;}
    union {struct cmsghdr align;unsigned char bytes[CMSG_SPACE(sizeof(int))];} control;
    memset(&control,0,sizeof(control));struct iovec io={.iov_base=(void*)data,.iov_len=maximum};
    struct msghdr message={0};message.msg_iov=&io;message.msg_iovlen=1;
    message.msg_control=control.bytes;message.msg_controllen=sizeof(control.bytes);
    struct cmsghdr* c=CMSG_FIRSTHDR(&message);c->cmsg_level=SOL_SOCKET;c->cmsg_type=SCM_RIGHTS;
    c->cmsg_len=CMSG_LEN(sizeof(int));memcpy(CMSG_DATA(c),&slot->pending_fd,sizeof(int));
    return sendmsg(slot->fd,&message,MSG_NOSIGNAL);
}
static int lu_note_sent_v1(LuSlotV1* slot,ssize_t count) {
    if(count<=0)return 0;
    slot->sent_any=1;
    if(slot->transfer_phase==1) {
        int fd=slot->pending_fd;slot->pending_fd=-1;slot->transfer_phase=2;
        /* Positive bytes prove the single SCM handoff. Linux close consumes;
         * preserve byte count even on close diagnostic, NEVER attach it again. */
        if(close(fd))return -3;
    }
    return 0;
}
#endif
static SplArray* lu_stage_stdout_impl_v1(int64_t token,int64_t pid,int64_t generation,
        const char* root,int64_t root_size,const char* identity,int64_t identity_size,
        const char* binding,int64_t binding_size) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(2);if(!answer)return NULL;
#if defined(__linux__)
    int status=-1;LuSlotV1* slot=NULL;
    if(!lu_transfer_binding_v1(binding,binding_size))goto done;
    slot=lu_connection_lock_v1(token,&status);if(!slot)goto done;
    if(!slot->accepted||!slot->request_claimed){status=-15;goto done;}
    if(slot->transfer_phase!=0||slot->pending_fd>=0){status=-16;goto done;}
    if(slot->write_shutdown||slot->sent_any){status=-15;goto done;}
    int fd=-1;status=(int)simple_process_stdout_take_v1(pid,generation,root,root_size,identity,identity_size,&fd);
    if(status==-13)status=-16;
    if(status==0) {
        slot->pending_fd=fd;slot->transfer_phase=1;
        memcpy(slot->transfer_binding,binding,64);slot->transfer_binding[64]=0;
        lu_word_v1(answer,1,1);
    }
done:
    if(slot)pthread_mutex_unlock(&slot->operation);
    lu_word_v1(answer,0,status);
#else
    (void)token;(void)pid;(void)generation;(void)root;(void)root_size;(void)identity;(void)identity_size;(void)binding;(void)binding_size;
    lu_word_v1(answer,0,-4);
#endif
    return answer;
}
static SplArray* lu_adopt_byte_impl_v1(int64_t token,const char* binding,int64_t binding_size) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(2);if(!answer)return NULL;
#if defined(__linux__)
    int status=-1;LuSlotV1* slot=NULL;
    if(!lu_transfer_binding_v1(binding,binding_size))goto done;
    slot=lu_connection_lock_v1(token,&status);if(!slot)goto done;
    if(slot->transfer_phase==4){status=-16;goto done;}
    if(slot->accepted||!slot->write_shutdown||slot->transfer_phase!=3||slot->pending_fd<0){status=-15;goto done;}
    if(slot->transfer_binding[0]&&memcmp(slot->transfer_binding,binding,64)){status=-16;goto done;}
    if(!slot->transfer_binding[0]){memcpy(slot->transfer_binding,binding,64);slot->transfer_binding[64]=0;}
    if(!slot->read_eof){status=-15;goto done;}
    int64_t generation=0;
    status=(int)simple_process_byte_adopt_v1(slot->pending_fd,binding,64,&generation);
    if(status==0) {
        slot->pending_fd=-1;slot->transfer_phase=4;
        memcpy(slot->transfer_binding,binding,64);slot->transfer_binding[64]=0;
        lu_word_v1(answer,1,generation); /* private owner guarantees immediate range */
    }
done:
    if(slot)pthread_mutex_unlock(&slot->operation);
    lu_word_v1(answer,0,status);
#else
    (void)token;(void)binding;(void)binding_size;lu_word_v1(answer,0,-4);
#endif
    return answer;
}
static SplArray* lu_handoff_state_impl_v1(int64_t token) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(2);if(!answer)return NULL;
#if defined(__linux__)
    int status;LuSlotV1* slot=lu_connection_lock_v1(token,&status);
    if(slot){lu_word_v1(answer,1,slot->transfer_phase);pthread_mutex_unlock(&slot->operation);}
    lu_word_v1(answer,0,status);
#else
    (void)token;lu_word_v1(answer,0,-4);
#endif
    return answer;
}
