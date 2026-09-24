// Optional, independently built Ganesh/Vulkan implementation of the existing
// authenticated Simple GPU provider ABI. This file is never in the embedded
// runtime source closure.
#include "draw_payload_v1.h"
#include "draw_payload_v3_validate.h"
#include "../../src/runtime/simple_gpu_provider_abi_v1.h"
#include "../../src/runtime/simple_gpu_provider_identity_v1.h"

#include "include/core/SkCanvas.h"
#include "include/core/SkBlendMode.h"
#include "include/core/SkColorSpace.h"
#include "include/core/SkImageInfo.h"
#include "include/core/SkMatrix.h"
#include "include/core/SkPaint.h"
#include "include/core/SkRect.h"
#include "include/core/SkSurface.h"
#include "include/gpu/GpuTypes.h"
#include "include/gpu/ganesh/GrDirectContext.h"
#include "include/gpu/ganesh/SkSurfaceGanesh.h"
#include "include/gpu/ganesh/vk/GrVkDirectContext.h"
#include "include/gpu/vk/VulkanBackendContext.h"
#include "include/gpu/vk/VulkanExtensions.h"

#include <vulkan/vulkan.h>
#include <chrono>
#include <cmath>
#include <cstring>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <thread>
#include <vector>

#ifndef SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3
#define SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3 0
#endif
static_assert(SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3 == 0 ||
              SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3 == 1,
              "affine v3 build gate must be 0 or 1");

static_assert(sizeof(SimpleUpstreamSkiaDrawHeaderV1) == 16,
              "draw header ABI drift");
static_assert(sizeof(SimpleUpstreamSkiaRectV1) == 40,
              "draw rect ABI drift");
static_assert(sizeof(SimpleUpstreamSkiaRectV2) == 64,
              "draw rect v2 ABI drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV2, clip_x) == 40,
              "draw clip offset drift");
static_assert(offsetof(SimpleUpstreamSkiaRectV2, flags) == 56,
              "draw flags offset drift");

namespace {
static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "private draw payload v1 requires little-endian Linux");
constexpr uint64_t kProviderIdentity = UINT64_C(0x534b4941564b0001);
constexpr uint64_t kMaxPixels = UINT64_C(16777216);
std::mutex gLock;
uint64_t gNextHandle = 1;

uint64_t next_handle() {
    if (gNextHandle == UINT64_MAX) return 0;
    return gNextHandle++;
}

uint64_t checksum(const std::vector<uint8_t>& bytes) {
    uint64_t hash = UINT64_C(14695981039346656037);
    for (uint8_t byte : bytes) {
        hash ^= byte;
        hash *= UINT64_C(1099511628211);
    }
    return hash;
}

struct Resource {
    uint64_t owner = 0;
    uint32_t width = 0;
    uint32_t height = 0;
    bool ready = false;
    std::vector<uint8_t> pixels;
};

struct Completion {
    uint64_t owner = 0;
    uint64_t resource = 0;
    uint64_t correlation = 0;
    uint64_t checksum = 0;
    uint64_t elapsed_ns = 0;
    bool waited = false;
    bool readback_observed = false;
};

struct Session {
    std::thread::id thread;
    VkInstance instance = VK_NULL_HANDLE;
    VkPhysicalDevice physical = VK_NULL_HANDLE;
    VkDevice device = VK_NULL_HANDLE;
    VkQueue queue = VK_NULL_HANDLE;
    uint32_t queue_family = 0;
    uint64_t device_identity = 0;
    SimpleGpuProviderDeviceIdentityV1 identity{};
    bool lost = false;
    bool busy = false;
    skgpu::VulkanExtensions extensions;
    skgpu::VulkanBackendContext backend;
    sk_sp<GrDirectContext> context;

    ~Session() {
        context.reset();
        if (device != VK_NULL_HANDLE) vkDestroyDevice(device, nullptr);
        if (instance != VK_NULL_HANDLE) vkDestroyInstance(instance, nullptr);
    }
};

std::map<uint64_t, std::unique_ptr<Session>> gSessions;
std::map<uint64_t, Resource> gResources;
std::map<uint64_t, Completion> gCompletions;

Session* owned_session(uint64_t handle) {
    auto it = gSessions.find(handle);
    if (it == gSessions.end() || it->second->thread != std::this_thread::get_id())
        return nullptr;
    return it->second.get();
}

bool create_vulkan(Session& session, uint64_t device_index) {
    VkApplicationInfo app{VK_STRUCTURE_TYPE_APPLICATION_INFO};
    app.pApplicationName = "Simple optional upstream Ganesh";
    app.apiVersion = VK_API_VERSION_1_1;
    VkInstanceCreateInfo instance_info{VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO};
    instance_info.pApplicationInfo = &app;
#ifdef __APPLE__
    // MoltenVK is a portability implementation: the loader only enumerates it
    // when the app enables VK_KHR_portability_enumeration. Without this the
    // instance creates but vkEnumeratePhysicalDevices returns zero devices and
    // session_open rejects. Native ICDs (Linux N2 hosts) do not need the flag.
    const char* portability_extensions[] = {
        VK_KHR_PORTABILITY_ENUMERATION_EXTENSION_NAME};
    instance_info.enabledExtensionCount = 1;
    instance_info.ppEnabledExtensionNames = portability_extensions;
    instance_info.flags = VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR;
#endif
    if (vkCreateInstance(&instance_info, nullptr, &session.instance) != VK_SUCCESS)
        return false;
    uint32_t count = 0;
    if (vkEnumeratePhysicalDevices(session.instance, &count, nullptr) != VK_SUCCESS ||
        count == 0 || device_index >= count)
        return false;
    std::vector<VkPhysicalDevice> devices(count);
    if (vkEnumeratePhysicalDevices(session.instance, &count, devices.data()) != VK_SUCCESS ||
        device_index >= count)
        return false;
    session.physical = devices[static_cast<size_t>(device_index)];
    VkPhysicalDeviceProperties properties{};
    vkGetPhysicalDeviceProperties(session.physical, &properties);
    if (properties.apiVersion < VK_API_VERSION_1_1) return false;
    VkPhysicalDeviceIDProperties id_properties{
        VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_ID_PROPERTIES};
    VkPhysicalDeviceProperties2 properties2{
        VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_PROPERTIES_2};
    properties2.pNext = &id_properties;
    vkGetPhysicalDeviceProperties2(session.physical, &properties2);
    session.identity.struct_size = sizeof(session.identity);
    session.identity.version = SIMPLE_GPU_PROVIDER_DEVICE_IDENTITY_VERSION_V1;
    std::memcpy(session.identity.device_uuid, id_properties.deviceUUID,
                VK_UUID_SIZE);
    std::memcpy(session.identity.driver_uuid, id_properties.driverUUID,
                VK_UUID_SIZE);
    session.identity.vendor_id = properties2.properties.vendorID;
    session.identity.device_id = properties2.properties.deviceID;
    session.identity.device_type = properties2.properties.deviceType;
    session.identity.api_version = properties2.properties.apiVersion;
    session.identity.driver_version = properties2.properties.driverVersion;
    // ABI v1 binds receipt.device_identity to the selected device index.
    // This index remains an ABI-v1 owner token; physical identity is queried
    // through the optional session/completion-bound export below.
    session.device_identity = device_index;
    vkGetPhysicalDeviceQueueFamilyProperties(session.physical, &count, nullptr);
    std::vector<VkQueueFamilyProperties> families(count);
    vkGetPhysicalDeviceQueueFamilyProperties(session.physical, &count, families.data());
    uint32_t family = count;
    for (uint32_t i = 0; i < count; ++i) {
        if (families[i].queueCount && (families[i].queueFlags & VK_QUEUE_GRAPHICS_BIT)) {
            family = i;
            break;
        }
    }
    if (family == count) return false;
    session.queue_family = family;
    const float priority = 1.0f;
    VkDeviceQueueCreateInfo queue_info{VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO};
    queue_info.queueFamilyIndex = family;
    queue_info.queueCount = 1;
    queue_info.pQueuePriorities = &priority;
    VkDeviceCreateInfo device_info{VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO};
    device_info.queueCreateInfoCount = 1;
    device_info.pQueueCreateInfos = &queue_info;
    if (vkCreateDevice(session.physical, &device_info, nullptr, &session.device) != VK_SUCCESS)
        return false;
    vkGetDeviceQueue(session.device, family, 0, &session.queue);
    if (session.queue == VK_NULL_HANDLE) return false;
    auto get_proc = [](const char* name, VkInstance instance, VkDevice device)
        -> PFN_vkVoidFunction {
        return device != VK_NULL_HANDLE ? vkGetDeviceProcAddr(device, name)
                                        : vkGetInstanceProcAddr(instance, name);
    };
    session.extensions.init(get_proc, session.instance, session.physical,
                            0, nullptr, 0, nullptr);
    session.backend.fInstance = session.instance;
    session.backend.fPhysicalDevice = session.physical;
    session.backend.fDevice = session.device;
    session.backend.fQueue = session.queue;
    session.backend.fGraphicsQueueIndex = family;
    session.backend.fMaxAPIVersion = VK_API_VERSION_1_1;
    session.backend.fVkExtensions = &session.extensions;
    session.backend.fGetProc = get_proc;
    session.context = GrDirectContexts::MakeVulkan(session.backend);
    return session.context != nullptr;
}

SimpleUpstreamSkiaRectV2 payload_rect(const SimpleGpuSubmitV1& request,
                                      uint32_t index) {
    SimpleUpstreamSkiaRectV2 rect{};
    if (request.format == SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V2) {
        std::memcpy(&rect, request.data + sizeof(SimpleUpstreamSkiaDrawHeaderV1) +
                    uint64_t(index) * sizeof(rect), sizeof(rect));
    } else {
        SimpleUpstreamSkiaRectV1 old{};
        std::memcpy(&old, request.data + sizeof(SimpleUpstreamSkiaDrawHeaderV1) +
                    uint64_t(index) * sizeof(old), sizeof(old));
        rect.x = old.x;
        rect.y = old.y;
        rect.width = old.width;
        rect.height = old.height;
        rect.argb = old.argb;
        rect.reserved = old.reserved;
    }
    return rect;
}

bool exact_scalar(double value) {
    return std::isfinite(value) && double(float(value)) == value;
}

bool valid_payload(const SimpleGpuSubmitV1& request, const Resource& resource) {
    if (request.struct_size < sizeof(request) || request.correlation_id == 0 ||
        (request.format != SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V1 &&
         request.format != SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V2) || !request.data ||
        request.length < sizeof(SimpleUpstreamSkiaDrawHeaderV1)) return false;
    SimpleUpstreamSkiaDrawHeaderV1 header{};
    std::memcpy(&header, request.data, sizeof(header));
    const bool v2 = request.format == SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V2;
    const uint64_t stride = v2 ? sizeof(SimpleUpstreamSkiaRectV2)
                               : sizeof(SimpleUpstreamSkiaRectV1);
    if (header.magic != (v2 ? SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V2
                            : SIMPLE_UPSTREAM_SKIA_DRAW_MAGIC_V1) ||
        header.width != resource.width || header.height != resource.height ||
        header.rect_count == 0 || header.rect_count > SIMPLE_UPSTREAM_SKIA_MAX_RECTS_V1 ||
        request.length != sizeof(header) + uint64_t(header.rect_count) * stride)
        return false;
    for (uint32_t i = 0; i < header.rect_count; ++i) {
        const SimpleUpstreamSkiaRectV2 rect = payload_rect(request, i);
        const double values[] = {rect.x, rect.y, rect.width, rect.height};
        if (rect.reserved || rect.width <= 0 || rect.height <= 0) return false;
        for (double value : values)
            if (!exact_scalar(value)) return false;
        if ((rect.argb >> 24) != 0xff || rect.reserved2 ||
            (rect.flags & ~SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT)) return false;
        if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT) {
            const int64_t right = int64_t(rect.clip_x) + rect.clip_width;
            const int64_t bottom = int64_t(rect.clip_y) + rect.clip_height;
            if (!v2 || i == 0 || rect.clip_width < 0 || rect.clip_height < 0 ||
                !exact_scalar(rect.clip_x) || !exact_scalar(rect.clip_y) ||
                !exact_scalar(rect.clip_width) ||
                !exact_scalar(rect.clip_height) ||
                !exact_scalar(right) || !exact_scalar(bottom) ||
                !exact_scalar(rect.x + rect.width) ||
                !exact_scalar(rect.y + rect.height)) return false;
        } else if (rect.clip_x || rect.clip_y || rect.clip_width ||
                   rect.clip_height) {
            return false;
        } else if (rect.x < 0 || rect.y < 0 ||
                   rect.x + rect.width > header.width ||
                   rect.y + rect.height > header.height) {
            return false;
        }
        if (i == 0 && (rect.x != 0 || rect.y != 0 ||
                       rect.width != header.width ||
                       rect.height != header.height || rect.flags)) return false;
    }
    return true;
}

struct RenderResult {
    SimpleGpuStatusV1 status = SIMPLE_GPU_STATUS_REJECTED;
    std::vector<uint8_t> pixels;
    uint64_t checksum = 0;
    uint64_t elapsed_ns = 0;
};

// The caller pins the session and resource with Session::busy. No global map
// lock is held while Skia or the Vulkan driver can block.
RenderResult render(Session& session, const SimpleGpuSubmitV1& request,
                    uint32_t width, uint32_t height) {
    RenderResult result;
    const auto start = std::chrono::steady_clock::now();
    sk_sp<SkColorSpace> color_space = SkColorSpace::MakeSRGB();
    const SkImageInfo info = SkImageInfo::Make(width, height,
        kRGBA_8888_SkColorType, kPremul_SkAlphaType, color_space);
    sk_sp<SkSurface> surface = SkSurfaces::RenderTarget(
        session.context.get(), skgpu::Budgeted::kYes, info);
    if (!surface) return result;
    SkCanvas* canvas = surface->getCanvas();
    canvas->clear(SK_ColorTRANSPARENT);
    SimpleUpstreamSkiaDrawHeaderV1 header{};
    std::memcpy(&header, request.data, sizeof(header));
#if SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3
    if (request.format == SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V3) {
        for (uint32_t i = 0; i < header.rect_count; ++i) {
            SimpleUpstreamSkiaRectV3 rect{};
            std::memcpy(&rect, request.data + sizeof(header) +
                uint64_t(i) * sizeof(rect), sizeof(rect));
            if (i == 0) {
                // The validator requires an opaque full-target, unclipped,
                // untransformed clear before any other rectangle is drawn.
                canvas->clear(rect.argb);
                continue;
            }
            SkPaint paint;
            const bool coverage_aa =
                rect.raster_policy == SIMPLE_UPSTREAM_SKIA_RASTER_COVERAGE_AA_V3;
            paint.setColor(rect.argb);
            paint.setAntiAlias(coverage_aa);
            paint.setStyle(SkPaint::kFill_Style);
            paint.setBlendMode(SkBlendMode::kSrcOver);
            canvas->save();
            if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT) {
                canvas->clipRect(SkRect::MakeXYWH(float(rect.clip_x),
                    float(rect.clip_y), float(rect.clip_width),
                    float(rect.clip_height)), SkClipOp::kIntersect,
                    /*doAntiAlias=*/coverage_aa);
            }
            if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V3_AFFINE_PRESENT) {
                SkMatrix matrix;
                matrix.setAll(float(rect.affine_a), float(rect.affine_c),
                    float(rect.affine_tx), float(rect.affine_b),
                    float(rect.affine_d), float(rect.affine_ty),
                    0.0f, 0.0f, 1.0f);
                canvas->concat(matrix);
            }
            canvas->drawRect(SkRect::MakeXYWH(float(rect.x), float(rect.y),
                float(rect.width), float(rect.height)), paint);
            canvas->restore();
        }
    } else
#endif
    {
        for (uint32_t i = 0; i < header.rect_count; ++i) {
            const SimpleUpstreamSkiaRectV2 rect = payload_rect(request, i);
            SkPaint paint;
            paint.setColor(rect.argb);
            paint.setAntiAlias(false);
            paint.setStyle(SkPaint::kFill_Style);
            paint.setBlendMode(SkBlendMode::kSrcOver);
            if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT) {
                canvas->save();
                canvas->clipRect(SkRect::MakeXYWH(float(rect.clip_x),
                    float(rect.clip_y), float(rect.clip_width),
                    float(rect.clip_height)), SkClipOp::kIntersect,
                    /*doAntiAlias=*/false);
            }
            canvas->drawRect(SkRect::MakeXYWH(float(rect.x), float(rect.y),
                float(rect.width), float(rect.height)), paint);
            if (rect.flags & SIMPLE_UPSTREAM_SKIA_RECT_V2_CLIP_PRESENT)
                canvas->restore();
        }
    }
    session.context->flush(surface.get());
    if (!session.context->submit(GrSyncCpu::kYes) ||
        vkDeviceWaitIdle(session.device) != VK_SUCCESS) {
        result.status = SIMPLE_GPU_STATUS_UNCERTAIN;
        return result;
    }
    result.pixels.resize(uint64_t(width) * height * 4);
    const SkImageInfo readback_info = SkImageInfo::Make(width, height,
        kRGBA_8888_SkColorType, kUnpremul_SkAlphaType, color_space);
    if (!surface->readPixels(readback_info, result.pixels.data(),
                             width * 4, 0, 0) ||
        vkDeviceWaitIdle(session.device) != VK_SUCCESS) {
        result.status = SIMPLE_GPU_STATUS_UNCERTAIN;
        return result;
    }
    const auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        std::chrono::steady_clock::now() - start).count();
    result.checksum = checksum(result.pixels);
    result.elapsed_ns = static_cast<uint64_t>(elapsed > 0 ? elapsed : 1);
    result.status = SIMPLE_GPU_STATUS_OK;
    return result;
}

SimpleGpuStatusV1 shutdown() {
    std::lock_guard<std::mutex> lock(gLock);
    return gSessions.empty() && gResources.empty() && gCompletions.empty()
        ? SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_BUSY;
}

SimpleGpuStatusV1 session_open(uint64_t backend, uint64_t device_index,
                               SimpleGpuHandleV1* out) {
    if (!out || backend != SIMPLE_GPU_BACKEND_VULKAN) return SIMPLE_GPU_STATUS_REJECTED;
    *out = 0;
    std::unique_ptr<Session> session;
    try {
        session = std::make_unique<Session>();
    } catch (...) {
        return SIMPLE_GPU_STATUS_REJECTED;
    }
    session->thread = std::this_thread::get_id();
    try {
        if (!create_vulkan(*session, device_index)) return SIMPLE_GPU_STATUS_REJECTED;
    } catch (...) {
        return SIMPLE_GPU_STATUS_REJECTED;
    }
    std::lock_guard<std::mutex> lock(gLock);
    const uint64_t handle = next_handle();
    if (!handle) return SIMPLE_GPU_STATUS_REJECTED;
    try {
        gSessions.emplace(handle, std::move(session));
    } catch (...) {
        return SIMPLE_GPU_STATUS_REJECTED;
    }
    *out = handle;
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 session_close(SimpleGpuHandleV1 handle) {
    std::unique_lock<std::mutex> lock(gLock);
    Session* session = owned_session(handle);
    if (!session) return SIMPLE_GPU_STATUS_INVALID;
    if (session->busy) return SIMPLE_GPU_STATUS_BUSY;
    for (const auto& entry : gResources)
        if (entry.second.owner == handle) return SIMPLE_GPU_STATUS_BUSY;
    for (const auto& entry : gCompletions)
        if (entry.second.owner == handle) return SIMPLE_GPU_STATUS_BUSY;
    session->busy = true;
    lock.unlock();
    const VkResult idle_status = vkDeviceWaitIdle(session->device);
    if (idle_status != VK_SUCCESS && idle_status != VK_ERROR_DEVICE_LOST) {
        lock.lock();
        session->lost = true;
        session->busy = false;
        return SIMPLE_GPU_STATUS_FAILED;
    }
    // A lost device cannot render again, but Vulkan still permits teardown.
    // Keep all handles alive while Ganesh releases its child resources.
    if (idle_status == VK_ERROR_DEVICE_LOST && session->context)
        session->context->releaseResourcesAndAbandonContext();
    session->context.reset();
    vkDestroyDevice(session->device, nullptr);
    session->device = VK_NULL_HANDLE;
    vkDestroyInstance(session->instance, nullptr);
    session->instance = VK_NULL_HANDLE;
    lock.lock();
    gSessions.erase(handle);
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 resource_alloc(SimpleGpuHandleV1 owner,
                                  const SimpleGpuResourceDescV1* desc,
                                  SimpleGpuHandleV1* out) {
    if (!out || !desc || desc->struct_size < sizeof(*desc)) return SIMPLE_GPU_STATUS_REJECTED;
    *out = 0;
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    if (!session || session->lost || session->busy) return SIMPLE_GPU_STATUS_REJECTED;
    uint32_t width = uint32_t(desc->usage_bits >> 32);
    uint32_t height = uint32_t(desc->usage_bits);
    uint64_t pixels = uint64_t(width) * height;
    if (desc->flags || !width || !height || width > 16384 || height > 16384 ||
        pixels > kMaxPixels || desc->size_bytes != pixels * 4)
        return SIMPLE_GPU_STATUS_REJECTED;
    const uint64_t handle = next_handle();
    if (!handle) return SIMPLE_GPU_STATUS_REJECTED;
    try {
        gResources.emplace(handle, Resource{owner, width, height, false, {}});
    } catch (...) {
        return SIMPLE_GPU_STATUS_REJECTED;
    }
    *out = handle;
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 resource_release(SimpleGpuHandleV1 owner, SimpleGpuHandleV1 handle) {
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    if (!session) return SIMPLE_GPU_STATUS_INVALID;
    if (session->busy) return SIMPLE_GPU_STATUS_BUSY;
    auto it = gResources.find(handle);
    if (it == gResources.end() || it->second.owner != owner) return SIMPLE_GPU_STATUS_INVALID;
    for (const auto& entry : gCompletions)
        if (entry.second.resource == handle) return SIMPLE_GPU_STATUS_BUSY;
    gResources.erase(it);
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 submit(SimpleGpuHandleV1 owner, const SimpleGpuSubmitV1* request,
                         SimpleGpuHandleV1* out) {
    if (!out || !request || request->struct_size < sizeof(*request))
        return SIMPLE_GPU_STATUS_REJECTED;
    *out = 0;
    std::unique_lock<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    auto resource = gResources.find(request->output_resource);
    if (!session || session->lost || session->busy || resource == gResources.end() ||
        resource->second.owner != owner)
        return SIMPLE_GPU_STATUS_REJECTED;
    const bool v3 = request->format == SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V3;
    if (v3) {
        double max_corner_error = 0.0;
        if (!request->correlation_id ||
            !simple_upstream_skia_v3_payload_valid(request->data, request->length,
                resource->second.width, resource->second.height,
                &max_corner_error)) return SIMPLE_GPU_STATUS_REJECTED;
#if !SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3
        // Default builds reject even a well-formed v3 payload before GPU work.
        return SIMPLE_GPU_STATUS_REJECTED;
#endif
    }
    if (!v3 && !valid_payload(*request, resource->second))
        return SIMPLE_GPU_STATUS_REJECTED;
    for (const auto& entry : gCompletions)
        if (entry.second.resource == request->output_resource)
            return SIMPLE_GPU_STATUS_REJECTED;
    const uint64_t handle = next_handle();
    if (!handle) return SIMPLE_GPU_STATUS_REJECTED;
    session->busy = true;
    const uint32_t width = resource->second.width;
    const uint32_t height = resource->second.height;
    lock.unlock();
    RenderResult result;
    try {
        result = render(*session, *request, width, height);
    } catch (...) {
        // Allocation or Skia failure after native work may be uncertain.
        // Never throw through the C ABI or leave the session busy forever.
        lock.lock();
        session->lost = true;
        session->busy = false;
        return SIMPLE_GPU_STATUS_UNCERTAIN;
    }
    lock.lock();
    if (result.status != SIMPLE_GPU_STATUS_OK) {
        if (result.status == SIMPLE_GPU_STATUS_UNCERTAIN) session->lost = true;
        session->busy = false;
        return result.status;
    }
    resource->second.pixels = std::move(result.pixels);
    resource->second.ready = false;
    try {
        gCompletions.emplace(handle, Completion{owner, request->output_resource,
            request->correlation_id, result.checksum, result.elapsed_ns, false});
    } catch (...) {
        // Rendering and readback have completed; no queued GPU work remains.
        // The caller can release the resource and close this live session.
        resource->second.pixels.clear();
        session->busy = false;
        return SIMPLE_GPU_STATUS_REJECTED;
    }
    session->busy = false;
    *out = handle;
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 wait(SimpleGpuHandleV1 owner, SimpleGpuHandleV1 handle,
                       uint64_t timeout_ns, SimpleGpuReceiptV1* receipt) {
    if (!receipt || receipt->struct_size < sizeof(*receipt) || !timeout_ns)
        return SIMPLE_GPU_STATUS_INVALID;
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    auto completion = gCompletions.find(handle);
    if (!session || completion == gCompletions.end() ||
        completion->second.owner != owner || completion->second.waited ||
        session->lost || session->busy)
        return SIMPLE_GPU_STATUS_INVALID;
    auto resource = gResources.find(completion->second.resource);
    if (resource == gResources.end()) return SIMPLE_GPU_STATUS_INVALID;
    completion->second.waited = true;
    resource->second.ready = true;
    *receipt = SimpleGpuReceiptV1{sizeof(*receipt), SIMPLE_GPU_STATUS_OK,
        completion->second.correlation, kProviderIdentity,
        session->device_identity, completion->second.resource,
        completion->second.checksum, completion->second.elapsed_ns};
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 readback(SimpleGpuHandleV1 owner, SimpleGpuHandleV1 handle,
                           SimpleGpuBytesV1* bytes) {
    if (!bytes || bytes->struct_size < sizeof(*bytes) || !bytes->data)
        return SIMPLE_GPU_STATUS_INVALID;
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    auto resource = gResources.find(handle);
    if (!session || session->lost || session->busy || resource == gResources.end() ||
        resource->second.owner != owner || !resource->second.ready ||
        bytes->length < resource->second.pixels.size())
        return SIMPLE_GPU_STATUS_INVALID;
    std::memcpy(bytes->data, resource->second.pixels.data(),
                resource->second.pixels.size());
    bytes->length = resource->second.pixels.size();
    for (auto& entry : gCompletions) {
        Completion& completion = entry.second;
        if (completion.owner == owner && completion.resource == handle &&
            completion.waited) {
            completion.readback_observed = true;
            break;
        }
    }
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 device_identity_for_completion(
    SimpleGpuHandleV1 owner, SimpleGpuHandleV1 handle,
    SimpleGpuProviderDeviceIdentityV1* out) {
    if (!out || out->struct_size < sizeof(*out))
        return SIMPLE_GPU_STATUS_INVALID;
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    auto completion = gCompletions.find(handle);
    if (!session || session->lost || session->busy ||
        completion == gCompletions.end() || completion->second.owner != owner ||
        !completion->second.waited ||
        !completion->second.readback_observed)
        return SIMPLE_GPU_STATUS_INVALID;
    auto resource = gResources.find(completion->second.resource);
    if (resource == gResources.end() || resource->second.owner != owner ||
        !resource->second.ready || resource->second.pixels.empty())
        return SIMPLE_GPU_STATUS_INVALID;
    *out = session->identity;
    return SIMPLE_GPU_STATUS_OK;
}

SimpleGpuStatusV1 completion_release(SimpleGpuHandleV1 owner,
                                      SimpleGpuHandleV1 handle) {
    std::lock_guard<std::mutex> lock(gLock);
    Session* session = owned_session(owner);
    if (!session) return SIMPLE_GPU_STATUS_INVALID;
    if (session->busy) return SIMPLE_GPU_STATUS_BUSY;
    auto completion = gCompletions.find(handle);
    if (completion == gCompletions.end() || completion->second.owner != owner)
        return SIMPLE_GPU_STATUS_INVALID;
    gCompletions.erase(completion);
    return SIMPLE_GPU_STATUS_OK;
}

int64_t operation_identity() { return SIMPLE_UPSTREAM_SKIA_DRAW_FORMAT_V1; }
const SimpleGpuOperationV1 kOperations[] = {operation_identity};
const SimpleGpuProviderAbiV1 kApi = {
    sizeof(SimpleGpuProviderAbiV1), SIMPLE_GPU_PROVIDER_ABI_MAJOR,
    SIMPLE_GPU_PROVIDER_ABI_MINOR, SIMPLE_GPU_BACKEND_VULKAN,
    SIMPLE_GPU_CAP_DEVICE_READBACK,
    kProviderIdentity, SIMPLE_GPU_OP_COUNT, 0, kOperations,
    shutdown, session_open, session_close, submit, wait, readback,
    resource_alloc, resource_release, completion_release
};
} // namespace

extern "C" const SimpleGpuProviderAbiV1* simple_gpu_provider_query_v1() {
    return &kApi;
}

extern "C" SimpleGpuStatusV1 simple_gpu_provider_device_identity_v1(
    SimpleGpuHandleV1 session, SimpleGpuHandleV1 completion,
    SimpleGpuProviderDeviceIdentityV1* out) {
    return device_identity_for_completion(session, completion, out);
}
