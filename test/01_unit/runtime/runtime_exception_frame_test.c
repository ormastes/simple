#include "runtime.h"

#include <assert.h>
#include <setjmp.h>
#include <stdint.h>
#include <pthread.h>

static void catch_once(int64_t payload, int64_t type_tag) {
    jmp_buf* environment = (jmp_buf*)rt_exception_frame_push();
    int status = _setjmp(*environment);
    if (status == 0) {
        rt_exception_throw(payload, type_tag);
    }
    assert(rt_exception_peek_payload() == payload);
    assert(rt_exception_peek_type_tag() == type_tag);
    assert(rt_exception_frame_finish(status) != 0);
    assert(rt_exception_caught_type_tag() == type_tag);
    assert(rt_exception_frame_depth() == 0);
}

static void catch_once_capture(int64_t payload, int64_t type_tag) {
    jmp_buf* environment = (jmp_buf*)rt_exception_frame_push();
    int status = _setjmp(*environment);
    if (status == 0) {
        rt_exception_throw(payload, type_tag);
    }
    RtExceptionCapture capture = rt_exception_frame_capture(status);
    assert(capture.status != 0);
    assert(capture.payload == payload);
    assert(__simple_exception_type_tag() == type_tag);
    assert(rt_exception_frame_depth() == 0);
}

static void catch_nested_resume(void) {
    jmp_buf* outer = (jmp_buf*)rt_exception_frame_push();
    int outer_status = _setjmp(*outer);
    if (outer_status == 0) {
        jmp_buf* inner = (jmp_buf*)rt_exception_frame_push();
        int inner_status = _setjmp(*inner);
        if (inner_status == 0) {
            rt_exception_throw(17, 101);
        }
        assert(rt_exception_peek_payload() == 17);
        assert(rt_exception_frame_finish(inner_status) != 0);
        rt_exception_resume(29, 202);
    }
    assert(rt_exception_peek_payload() == 29);
    assert(rt_exception_peek_type_tag() == 202);
    assert(rt_exception_frame_finish(outer_status) != 0);
    assert(rt_exception_frame_depth() == 0);
}

static void* thread_worker(void* raw) {
    intptr_t id = (intptr_t)raw;
    catch_once((int64_t)(1000 + id), (int64_t)(2000 + id));
    return 0;
}

int main(void) {
    assert(rt_exception_frame_capacity() == 64);
    assert(rt_exception_frame_depth() == 0);
    catch_once(73, 11);
    catch_once_capture(81, 12);
    catch_nested_resume();

    pthread_t left;
    pthread_t right;
    assert(pthread_create(&left, 0, thread_worker, (void*)(intptr_t)1) == 0);
    assert(pthread_create(&right, 0, thread_worker, (void*)(intptr_t)2) == 0);
    assert(pthread_join(left, 0) == 0);
    assert(pthread_join(right, 0) == 0);
    assert(rt_exception_frame_depth() == 0);
    return 0;
}
