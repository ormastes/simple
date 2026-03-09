// ipc_events.cpp - CUDA IPC event handle management

#include <cuda_runtime.h>
#include <cstring>
#include <cstdio>

// IPC event handle wrapper
struct IPCEventHandle {
    cudaIpcEventHandle_t handle;
    cudaEvent_t event;
    bool isCreator;
};

// Create IPC-shareable event
bool createIPCEvent(IPCEventHandle* ipcEvent) {
    if (!ipcEvent) return false;

    ipcEvent->isCreator = true;

    // Create event with IPC flag
    cudaError_t err = cudaEventCreate(&ipcEvent->event, cudaEventInterprocess | cudaEventDisableTiming);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to create event: %s\n", cudaGetErrorString(err));
        return false;
    }

    // Get IPC handle
    err = cudaIpcGetEventHandle(&ipcEvent->handle, ipcEvent->event);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to get IPC event handle: %s\n", cudaGetErrorString(err));
        cudaEventDestroy(ipcEvent->event);
        return false;
    }

    return true;
}

// Open IPC event from handle
bool openIPCEvent(IPCEventHandle* ipcEvent, const cudaIpcEventHandle_t* handle) {
    if (!ipcEvent || !handle) return false;

    ipcEvent->isCreator = false;
    memcpy(&ipcEvent->handle, handle, sizeof(cudaIpcEventHandle_t));

    // Open IPC event handle
    cudaError_t err = cudaIpcOpenEventHandle(&ipcEvent->event, *handle);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to open IPC event handle: %s\n", cudaGetErrorString(err));
        return false;
    }

    return true;
}

// Close IPC event
void closeIPCEvent(IPCEventHandle* ipcEvent) {
    if (!ipcEvent || !ipcEvent->event) return;

    if (ipcEvent->isCreator) {
        cudaEventDestroy(ipcEvent->event);
    }
    ipcEvent->event = nullptr;
}

// Record event
bool recordIPCEvent(IPCEventHandle* ipcEvent, cudaStream_t stream) {
    if (!ipcEvent || !ipcEvent->event) return false;

    cudaError_t err = cudaEventRecord(ipcEvent->event, stream);
    return (err == cudaSuccess);
}

// Wait for event
bool waitIPCEvent(IPCEventHandle* ipcEvent, cudaStream_t stream) {
    if (!ipcEvent || !ipcEvent->event) return false;

    cudaError_t err = cudaStreamWaitEvent(stream, ipcEvent->event, 0);
    return (err == cudaSuccess);
}

// Synchronize with event
bool synchronizeIPCEvent(IPCEventHandle* ipcEvent) {
    if (!ipcEvent || !ipcEvent->event) return false;

    cudaError_t err = cudaEventSynchronize(ipcEvent->event);
    return (err == cudaSuccess);
}

// Get event handle for sharing
bool getIPCEventHandle(const IPCEventHandle* ipcEvent, cudaIpcEventHandle_t* outHandle) {
    if (!ipcEvent || !outHandle) return false;
    memcpy(outHandle, &ipcEvent->handle, sizeof(cudaIpcEventHandle_t));
    return true;
}
