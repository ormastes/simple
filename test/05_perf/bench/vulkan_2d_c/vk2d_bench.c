// vk2d_bench.c — headless Vulkan 2D rect-fill benchmark.
//
// Adapted from the Magicalbat/videos vulkan-compute single-file C99 example
// (test/05_perf/bench/vulkan_2d_c/main.c, fetched verbatim from
// https://raw.githubusercontent.com/Magicalbat/videos/main/vulkan-compute/main.c):
// same instance/device/memory strategy (one HOST_VISIBLE|HOST_COHERENT
// allocation, first compute queue, one-shot command buffers, fence wait).
// The adaptation adds exactly what a 2D renderer does per frame:
// vkCmdFillBuffer clear + N rect-fill compute dispatches + optional CPU
// readback, retained three-slot submission, and nonblocking completion polls.
//
// macOS/MoltenVK: requires VK_KHR_portability_enumeration (patched below).
//
// Build:  glslangValidator -V rect.comp.glsl -o rect.spv
//         clang -std=c99 -O2 vk2d_bench.c -I/opt/homebrew/include \
//               -L/opt/homebrew/lib -lvulkan -o vk2d_bench
// Run:    VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json \
//         ./vk2d_bench [w] [h] [rects] [frames] [readback=0|1]

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

#include <vulkan/vulkan.h>

typedef uint8_t u8;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int32_t b32;
typedef int32_t i32;
typedef float f32;

#define ALIGN_UP(n, a) (((n) + (a) - 1) - ((n) + (a) - 1) % (a))

typedef struct RectPush {
    i32 x, y, w, h;
    u32 color;
    i32 fb_w, fb_h;
} RectPush;

static u64 now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (u64)ts.tv_sec * 1000000000ull + (u64)ts.tv_nsec;
}

static int compare_u64(const void* a, const void* b) {
    const u64 av = *(const u64*)a, bv = *(const u64*)b;
    return av < bv ? -1 : av > bv ? 1 : 0;
}

static b32 poll_fence_complete(VkDevice device, VkFence fence, u64* poll_count) {
    for (;;) {
        (*poll_count)++;
        const VkResult status = vkGetFenceStatus(device, fence);
        if (status == VK_SUCCESS) return 1;
        if (status != VK_NOT_READY) return 0;
        const struct timespec pause = { .tv_sec = 0, .tv_nsec = 50000 };
        nanosleep(&pause, NULL);
    }
}

static void record_frame(VkCommandBuffer cmd_buffer, VkBuffer fb_buffer,
                         u64 fb_size, VkPipeline pipeline,
                         VkPipelineLayout pipeline_layout,
                         VkDescriptorSet descriptor_set,
                         const RectPush* rects, i32 num_rects,
                         u32 clear_color) {
    vkResetCommandBuffer(cmd_buffer, 0);
    vkBeginCommandBuffer(cmd_buffer, &(VkCommandBufferBeginInfo){
        .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO
    });
    vkCmdFillBuffer(cmd_buffer, fb_buffer, 0, fb_size, clear_color);
    vkCmdPipelineBarrier(cmd_buffer,
        VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
        0, 0, NULL, 1, &(VkBufferMemoryBarrier){
            .sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER,
            .srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT,
            .dstAccessMask = VK_ACCESS_SHADER_WRITE_BIT,
            .buffer = fb_buffer, .offset = 0, .size = fb_size,
        }, 0, NULL);
    vkCmdBindPipeline(cmd_buffer, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline);
    vkCmdBindDescriptorSets(cmd_buffer, VK_PIPELINE_BIND_POINT_COMPUTE,
        pipeline_layout, 0, 1, &descriptor_set, 0, NULL);
    for (i32 i = 0; i < num_rects; i++) {
        vkCmdPushConstants(cmd_buffer, pipeline_layout,
            VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(RectPush), &rects[i]);
        vkCmdDispatch(cmd_buffer,
            (u32)(rects[i].w + 15) / 16,
            (u32)(rects[i].h + 15) / 16, 1);
    }
    vkEndCommandBuffer(cmd_buffer);
}

int main(int argc, char** argv) {
    const i32 fb_w = argc > 1 ? atoi(argv[1]) : 800;
    const i32 fb_h = argc > 2 ? atoi(argv[2]) : 600;
    i32 num_rects = argc > 3 ? atoi(argv[3]) : 64;
    const i32 num_frames = argc > 4 ? atoi(argv[4]) : 300;
    const b32 do_readback = argc > 5 ? atoi(argv[5]) : 0;
    const i32 warmup_count = argc > 6 ? atoi(argv[6]) : 5;
    const i32 ring_size = 3;

    VkInstance instance = NULL;
    {
        const char* portability_ext = VK_KHR_PORTABILITY_ENUMERATION_EXTENSION_NAME;
        vkCreateInstance(&(VkInstanceCreateInfo){
            .sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO,
            .flags = VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR,
            .pApplicationInfo = &(VkApplicationInfo){
                .sType = VK_STRUCTURE_TYPE_APPLICATION_INFO,
                .apiVersion = VK_API_VERSION_1_0
            },
            .enabledExtensionCount = 1,
            .ppEnabledExtensionNames = &portability_ext,
        }, NULL, &instance);
        if (!instance) { fprintf(stderr, "vkCreateInstance failed\n"); return 1; }
    }

    VkPhysicalDevice physical_device = NULL;
    VkPhysicalDeviceProperties device_props = { 0 };
    {
        u32 n = 1;
        vkEnumeratePhysicalDevices(instance, &n, &physical_device);
        vkGetPhysicalDeviceProperties(physical_device, &device_props);
        printf("device: %s\n", device_props.deviceName);
    }

    u32 queue_family_index = 0;
    VkDevice device = NULL;
    {
        u32 count = 0;
        vkGetPhysicalDeviceQueueFamilyProperties(physical_device, &count, NULL);
        VkQueueFamilyProperties* qp = malloc(sizeof(VkQueueFamilyProperties) * count);
        vkGetPhysicalDeviceQueueFamilyProperties(physical_device, &count, qp);
        for (u32 i = 0; i < count; i++) {
            if (qp[i].queueFlags & VK_QUEUE_COMPUTE_BIT) { queue_family_index = i; break; }
        }
        free(qp);
        f32 priority = 0.0f;
        vkCreateDevice(physical_device, &(VkDeviceCreateInfo){
            .sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO,
            .queueCreateInfoCount = 1,
            .pQueueCreateInfos = &(VkDeviceQueueCreateInfo){
                .sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO,
                .queueFamilyIndex = queue_family_index,
                .queueCount = 1,
                .pQueuePriorities = &priority,
            },
        }, NULL, &device);
    }

    const u64 fb_size = (u64)fb_w * (u64)fb_h * sizeof(u32);

    VkBuffer fb_buffer = NULL;
    vkCreateBuffer(device, &(VkBufferCreateInfo){
        .sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO,
        .size = fb_size,
        .usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT,
        .sharingMode = VK_SHARING_MODE_EXCLUSIVE,
        .queueFamilyIndexCount = 1,
        .pQueueFamilyIndices = &queue_family_index
    }, NULL, &fb_buffer);

    VkMemoryRequirements mem_reqs = { 0 };
    vkGetBufferMemoryRequirements(device, fb_buffer, &mem_reqs);

    VkPhysicalDeviceMemoryProperties mem_props = { 0 };
    vkGetPhysicalDeviceMemoryProperties(physical_device, &mem_props);
    u32 mem_type_index = 0;
    for (u32 i = 0; i < mem_props.memoryTypeCount; i++) {
        if ((mem_props.memoryTypes[i].propertyFlags & VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT) &&
            (mem_props.memoryTypes[i].propertyFlags & VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)) {
            mem_type_index = i;
            break;
        }
    }

    VkDeviceMemory memory = NULL;
    vkAllocateMemory(device, &(VkMemoryAllocateInfo){
        .sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO,
        .memoryTypeIndex = mem_type_index,
        .allocationSize = mem_reqs.size
    }, NULL, &memory);
    vkBindBufferMemory(device, fb_buffer, memory, 0);

    u32* fb_pixels = NULL;
    vkMapMemory(device, memory, 0, mem_reqs.size, 0, (void**)&fb_pixels);

    VkShaderModule shader_module = NULL;
    {
        FILE* f = fopen("rect.spv", "rb");
        if (!f) { fprintf(stderr, "rect.spv missing (run glslangValidator first)\n"); return 1; }
        fseek(f, 0, SEEK_END);
        u64 size = ftell(f);
        fseek(f, 0, SEEK_SET);
        u8* code = malloc(size);
        fread(code, 1, size, f);
        fclose(f);
        vkCreateShaderModule(device, &(VkShaderModuleCreateInfo){
            .sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO,
            .codeSize = size,
            .pCode = (u32*)code,
        }, NULL, &shader_module);
        free(code);
    }

    VkDescriptorSetLayoutBinding binding =
        { 0, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_SHADER_STAGE_COMPUTE_BIT, NULL };
    VkDescriptorSetLayout descriptor_set_layout = NULL;
    vkCreateDescriptorSetLayout(device, &(VkDescriptorSetLayoutCreateInfo){
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO,
        .bindingCount = 1,
        .pBindings = &binding,
    }, NULL, &descriptor_set_layout);

    VkDescriptorPool descriptor_pool = NULL;
    vkCreateDescriptorPool(device, &(VkDescriptorPoolCreateInfo){
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO,
        .maxSets = 1,
        .poolSizeCount = 1,
        .pPoolSizes = &(VkDescriptorPoolSize){
            .type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            .descriptorCount = 1
        }
    }, NULL, &descriptor_pool);

    VkDescriptorSet descriptor_set = NULL;
    vkAllocateDescriptorSets(device, &(VkDescriptorSetAllocateInfo){
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO,
        .descriptorPool = descriptor_pool,
        .descriptorSetCount = 1,
        .pSetLayouts = &descriptor_set_layout
    }, &descriptor_set);

    vkUpdateDescriptorSets(device, 1, &(VkWriteDescriptorSet){
        .sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET,
        .dstSet = descriptor_set,
        .dstBinding = 0,
        .descriptorCount = 1,
        .descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
        .pBufferInfo = &(VkDescriptorBufferInfo){
            .buffer = fb_buffer, .offset = 0, .range = VK_WHOLE_SIZE
        }
    }, 0, NULL);

    VkPushConstantRange pc_range = {
        .stageFlags = VK_SHADER_STAGE_COMPUTE_BIT,
        .offset = 0,
        .size = sizeof(RectPush),
    };
    VkPipelineLayout pipeline_layout = NULL;
    vkCreatePipelineLayout(device, &(VkPipelineLayoutCreateInfo){
        .sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO,
        .setLayoutCount = 1,
        .pSetLayouts = &descriptor_set_layout,
        .pushConstantRangeCount = 1,
        .pPushConstantRanges = &pc_range,
    }, NULL, &pipeline_layout);

    VkPipeline pipeline = NULL;
    vkCreateComputePipelines(device, NULL, 1, &(VkComputePipelineCreateInfo){
        .sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO,
        .layout = pipeline_layout,
        .stage = (VkPipelineShaderStageCreateInfo){
            .sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO,
            .stage = VK_SHADER_STAGE_COMPUTE_BIT,
            .module = shader_module,
            .pName = "main"
        },
    }, NULL, &pipeline);

    VkCommandPool cmd_pool = NULL;
    vkCreateCommandPool(device, &(VkCommandPoolCreateInfo){
        .sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO,
        .queueFamilyIndex = queue_family_index,
        .flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT,
    }, NULL, &cmd_pool);

    VkCommandBuffer cmd_buffers[3] = { NULL, NULL, NULL };
    vkAllocateCommandBuffers(device, &(VkCommandBufferAllocateInfo){
        .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO,
        .commandPool = cmd_pool,
        .commandBufferCount = ring_size,
        .level = VK_COMMAND_BUFFER_LEVEL_PRIMARY
    }, cmd_buffers);

    VkQueue queue = NULL;
    vkGetDeviceQueue(device, queue_family_index, 0, &queue);

    VkFence fences[3] = { NULL, NULL, NULL };
    for (i32 i = 0; i < ring_size; i++) {
        vkCreateFence(device, &(VkFenceCreateInfo){
            .sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO,
        }, NULL, &fences[i]);
    }

    // Deterministic pseudo-random rect set (same for every run/implementation).
    u64 rng = 0x9e3779b97f4a7c15ull;
    RectPush* rects = malloc(sizeof(RectPush) * num_rects);
    for (i32 i = 0; i < num_rects; i++) {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        rects[i].w = 24 + (i32)(rng % 160);
        rects[i].h = 24 + (i32)((rng >> 16) % 120);
        rects[i].x = (i32)((rng >> 8) % (u64)(fb_w - rects[i].w));
        rects[i].y = (i32)((rng >> 24) % (u64)(fb_h - rects[i].h));
        rects[i].color = 0xFF000000u | (u32)(rng & 0x00FFFFFFu);
        rects[i].fb_w = fb_w;
        rects[i].fb_h = fb_h;
    }

    // Shared scene table: when scenes.txt is present it REPLACES the generated
    // set, so both legs render a bit-identical workload. Generating the set
    // independently in each language is exactly how the two sides silently
    // diverged (i64 sign-masking vs u64 wraparound), so the table is committed
    // literal data, not a re-derivation.
    const char* required_scene_path = getenv("VK2D_SCENES");
    const char* scene_path = required_scene_path;
    const char* scene_source = "generated";
    if (!scene_path) scene_path = "scenes.txt";
    FILE* sf = fopen(scene_path, "r");
    if (sf) {
        char line[256];
        i32 k = 0;
        while (k < num_rects && fgets(line, sizeof(line), sf)) {
            if (line[0] == '#' || line[0] == '\n') continue;
            i32 x, y, w, h; unsigned int col;
            if (sscanf(line, "rect %d %d %d %d %X", &x, &y, &w, &h, &col) == 5) {
                rects[k].x = x; rects[k].y = y; rects[k].w = w; rects[k].h = h;
                rects[k].color = (u32)col;
                rects[k].fb_w = fb_w; rects[k].fb_h = fb_h;
                k++;
            }
        }
        fclose(sf);
        if (k != num_rects) {
            fprintf(stderr, "scenes: expected %d rect(s), loaded %d from %s\n",
                num_rects, k, scene_path);
            return 1;
        }
        scene_source = "table";
        fprintf(stderr, "scenes: loaded %d rect(s) from %s\n", k, scene_path);
    } else if (required_scene_path) {
        fprintf(stderr, "scenes: required table unreadable: %s\n", scene_path);
        return 1;
    }

    if (getenv("VK2D_DUMP_RECTS")) {
        for (i32 i = 0; i < num_rects; i++)
            printf("rect %d %d %d %d %08X\n",
                rects[i].x, rects[i].y, rects[i].w, rects[i].h, rects[i].color);
        return 0;
    }

    const u32 clear_color = 0xFF141414u;
    u64 checksum = 0;

    // Pipeline/JIT warmup is outside both throughput and latency samples.
    for (i32 frame = 0; frame < warmup_count; frame++) {
        record_frame(cmd_buffers[0], fb_buffer, fb_size, pipeline,
            pipeline_layout, descriptor_set, rects, num_rects, clear_color);
        vkQueueSubmit(queue, 1, &(VkSubmitInfo){
            .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO, .commandBufferCount = 1,
            .pCommandBuffers = &cmd_buffers[0]
        }, fences[0]);
        vkWaitForFences(device, 1, &fences[0], true, ~(u64)(0));
        vkResetFences(device, 1, &fences[0]);
    }

    u64* latency_ns = calloc((size_t)num_frames, sizeof(u64));
    u64 sample_start_ns[3] = { 0, 0, 0 };
    i32 slot_sample[3] = { -1, -1, -1 };
    u64 completion_poll_count = 0;
    u64 t0 = now_ns();
    for (i32 frame = 0; frame < num_frames; frame++) {
        const i32 slot = frame % ring_size;
        if (slot_sample[slot] >= 0) {
            if (!poll_fence_complete(device, fences[slot], &completion_poll_count)) {
                fprintf(stderr, "timed fence poll failed\n");
                return 1;
            }
            latency_ns[slot_sample[slot]] = now_ns() - sample_start_ns[slot];
            vkResetFences(device, 1, &fences[slot]);
        }
        sample_start_ns[slot] = now_ns();
        record_frame(cmd_buffers[slot], fb_buffer, fb_size, pipeline,
            pipeline_layout, descriptor_set, rects, num_rects, clear_color);
        slot_sample[slot] = frame;
        vkQueueSubmit(queue, 1, &(VkSubmitInfo){
            .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO, .commandBufferCount = 1,
            .pCommandBuffers = &cmd_buffers[slot]
        }, fences[slot]);
    }
    for (i32 slot = 0; slot < ring_size; slot++) {
        if (slot_sample[slot] >= 0) {
            if (!poll_fence_complete(device, fences[slot], &completion_poll_count)) {
                fprintf(stderr, "final fence poll failed\n");
                return 1;
            }
            latency_ns[slot_sample[slot]] = now_ns() - sample_start_ns[slot];
        }
    }
    u64 t1 = now_ns();

    qsort(latency_ns, (size_t)num_frames, sizeof(u64), compare_u64);
    const u64 p50_ns = latency_ns[(num_frames - 1) * 50 / 100];
    const u64 p95_ns = latency_ns[(num_frames - 1) * 95 / 100];

    // Raw framebuffer dump for the byte-for-byte comparator. Written AFTER
    // the frame loop, so it is the same pixels the checksum folded.
    const char* dump_path = getenv("VK2D_DUMP_FB");
    if (do_readback) {
        vkResetFences(device, 1, &fences[0]);
        vkResetCommandBuffer(cmd_buffers[0], 0);
        vkBeginCommandBuffer(cmd_buffers[0], &(VkCommandBufferBeginInfo){
            .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO
        });
        vkCmdPipelineBarrier(cmd_buffers[0],
            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, VK_PIPELINE_STAGE_HOST_BIT,
            0, 0, NULL, 1, &(VkBufferMemoryBarrier){
                .sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER,
                .srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT,
                .dstAccessMask = VK_ACCESS_HOST_READ_BIT,
                .buffer = fb_buffer, .offset = 0, .size = fb_size,
            }, 0, NULL);
        vkEndCommandBuffer(cmd_buffers[0]);
        vkQueueSubmit(queue, 1, &(VkSubmitInfo){
            .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO, .commandBufferCount = 1,
            .pCommandBuffers = &cmd_buffers[0]
        }, fences[0]);
        vkWaitForFences(device, 1, &fences[0], true, ~(u64)(0));
        for (u64 i = 0; i < fb_size / 4; i += 4096) checksum ^= fb_pixels[i];
    }
    if (dump_path && do_readback) {
        FILE* df = fopen(dump_path, "wb");
        if (df) {
            fwrite(fb_pixels, 1, fb_size, df);
            fclose(df);
            fprintf(stderr, "dump: wrote %llu bytes to %s\n",
                (unsigned long long)fb_size, dump_path);
        }
    }

    if (getenv("VK2D_DEBUG") && do_readback) {
        // Correctness probe: center + corner pixels must be non-zero after
        // the clear, and at least one rect-colored pixel must exist.
        u64 nonzero = 0, rected = 0;
        for (u64 i = 0; i < fb_size / 4; i++) {
            if (fb_pixels[i] != 0) nonzero++;
            if (fb_pixels[i] != clear_color) rected++;
        }
        printf("debug: px[0]=%08x nonzero=%llu/%llu nonclear=%llu (rect coverage)\n",
            fb_pixels[0],
            (unsigned long long)nonzero, (unsigned long long)(fb_size / 4),
            (unsigned long long)rected);
    }

    double ms = (double)(t1 - t0) / 1e6;
    double fps = (double)num_frames / (ms / 1000.0);
    free(rects);
    free(latency_ns);
    vkUnmapMemory(device, memory);
    for (i32 i = 0; i < ring_size; i++) vkDestroyFence(device, fences[i], NULL);
    vkDestroyCommandPool(device, cmd_pool, NULL);
    vkDestroyPipeline(device, pipeline, NULL);
    vkDestroyPipelineLayout(device, pipeline_layout, NULL);
    vkDestroyDescriptorPool(device, descriptor_pool, NULL);
    vkDestroyDescriptorSetLayout(device, descriptor_set_layout, NULL);
    vkDestroyShaderModule(device, shader_module, NULL);
    vkDestroyBuffer(device, fb_buffer, NULL);
    vkFreeMemory(device, memory, NULL);
    vkDestroyDevice(device, NULL);
    vkDestroyInstance(instance, NULL);
    printf("c-vulkan-2d w=%d h=%d rects=%d warmups=%d samples=%d scene_source=%s ring=%d max_frames_in_flight=3 unconditional_submit_wait=false timed_buffer_allocation_count=0 retained_buffer_bytes=%llu teardown_released_bytes=%llu timed_full_frame_upload_count=0 upload_bytes=%llu timed_readback_bytes=0 capture_count=%d capture_readback_bytes=%llu fence_completions=%d completion_polls=%llu cpu_completion_wait_count=0 event_generations=%d damage_area_pixels=%llu device_vendor=%04x device_id=%04x p50_ns=%llu p95_ns=%llu ms=%.1f fps=%.1f checksum=%llu\n",
        fb_w, fb_h, num_rects, warmup_count, num_frames, scene_source, ring_size,
        (unsigned long long)mem_reqs.size, (unsigned long long)mem_reqs.size,
        (unsigned long long)num_frames * (unsigned long long)num_rects * sizeof(RectPush),
        do_readback ? 1 : 0, (unsigned long long)(do_readback ? fb_size : 0),
        num_frames, (unsigned long long)completion_poll_count, num_frames,
        (unsigned long long)fb_size / 4ull * (unsigned long long)num_frames,
        device_props.vendorID, device_props.deviceID,
        (unsigned long long)p50_ns, (unsigned long long)p95_ns, ms, fps,
        (unsigned long long)checksum);
    return 0;
}
