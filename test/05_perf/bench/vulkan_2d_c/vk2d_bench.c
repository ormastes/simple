// vk2d_bench.c — headless Vulkan 2D rect-fill benchmark.
//
// Adapted from the Magicalbat/videos vulkan-compute single-file C99 example
// (test/05_perf/bench/vulkan_2d_c/main.c, fetched verbatim from
// https://raw.githubusercontent.com/Magicalbat/videos/main/vulkan-compute/main.c):
// same instance/device/memory strategy (one HOST_VISIBLE|HOST_COHERENT
// allocation, first compute queue, one-shot command buffers, fence wait).
// The adaptation adds exactly what a 2D renderer does per frame:
// vkCmdFillBuffer clear + N rect-fill compute dispatches + optional CPU
// readback, one submit + one fence wait per frame.
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

int main(int argc, char** argv) {
    const i32 fb_w = argc > 1 ? atoi(argv[1]) : 800;
    const i32 fb_h = argc > 2 ? atoi(argv[2]) : 600;
    i32 num_rects = argc > 3 ? atoi(argv[3]) : 64;
    const i32 num_frames = argc > 4 ? atoi(argv[4]) : 300;
    const b32 do_readback = argc > 5 ? atoi(argv[5]) : 1;

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
    {
        u32 n = 1;
        vkEnumeratePhysicalDevices(instance, &n, &physical_device);
        VkPhysicalDeviceProperties props = { 0 };
        vkGetPhysicalDeviceProperties(physical_device, &props);
        printf("device: %s\n", props.deviceName);
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

    VkCommandBuffer cmd_buffer = NULL;
    vkAllocateCommandBuffers(device, &(VkCommandBufferAllocateInfo){
        .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO,
        .commandPool = cmd_pool,
        .commandBufferCount = 1,
        .level = VK_COMMAND_BUFFER_LEVEL_PRIMARY
    }, &cmd_buffer);

    VkQueue queue = NULL;
    vkGetDeviceQueue(device, queue_family_index, 0, &queue);

    VkFence fence = NULL;
    vkCreateFence(device, &(VkFenceCreateInfo){
        .sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO,
    }, NULL, &fence);

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
    const char* scene_path = getenv("VK2D_SCENES");
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
        if (k > 0) num_rects = k;
        fprintf(stderr, "scenes: loaded %d rect(s) from %s\n", k, scene_path);
    }

    if (getenv("VK2D_DUMP_RECTS")) {
        for (i32 i = 0; i < num_rects; i++)
            printf("rect %d %d %d %d %08X\n",
                rects[i].x, rects[i].y, rects[i].w, rects[i].h, rects[i].color);
        return 0;
    }

    const u32 clear_color = 0xFF141414u;
    // The scene is fixed, so every frame MUST fold to the same `acc`. The old
    // accumulator was `checksum ^= acc`, which cancels itself on any even
    // frame count and printed checksum=0 while the renderer was perfectly
    // correct -- and 0 also reads as "blank surface". Latch the first frame's
    // fold and COUNT later frames that disagree, so the value is independent
    // of the frame count and a genuine mid-run divergence is still reported.
    // Mirrors the Simple leg (vk2d_bench.spl) exactly.
    u64 checksum = 0;
    int checksum_latched = 0;
    u64 frame_mismatches = 0;

    u64 t0 = now_ns();
    for (i32 frame = 0; frame < num_frames; frame++) {
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
                (u32)(rects[i].w + 15) / 16, (u32)(rects[i].h + 15) / 16, 1);
        }

        if (do_readback) {
            vkCmdPipelineBarrier(cmd_buffer,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, VK_PIPELINE_STAGE_HOST_BIT,
                0, 0, NULL, 1, &(VkBufferMemoryBarrier){
                    .sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER,
                    .srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT,
                    .dstAccessMask = VK_ACCESS_HOST_READ_BIT,
                    .buffer = fb_buffer, .offset = 0, .size = fb_size,
                }, 0, NULL);
        }
        vkEndCommandBuffer(cmd_buffer);

        vkQueueSubmit(queue, 1, &(VkSubmitInfo){
            .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO,
            .commandBufferCount = 1,
            .pCommandBuffers = &cmd_buffer
        }, fence);
        vkWaitForFences(device, 1, &fence, true, ~(u64)(0));
        vkResetFences(device, 1, &fence);

        if (do_readback) {
            // HOST_COHERENT: visible right after the fence. Cheap fold so the
            // readback is real work the optimizer cannot delete.
            //
            // The stride SCALES with the surface: a fixed +4096 sampled
            // exactly one pixel at 64x64 (n == 4096), so the checksum could
            // not tell a rendered frame from a blank one. `n / 4096` keeps the
            // sample count at ~4096 pixels spread across the whole surface.
            // The fold is 32-bit FNV-1a, NOT xor: xor over N equal samples
            // cancels for even N. `acc = ((acc ^ px) * 16777619) & M` is a
            // bijection on acc for fixed px (16777619 is odd, hence invertible
            // mod 2^32) and on px for fixed acc, so equal-length sequences
            // that differ at ANY index fold to different values.
            //
            // THIS MUST STAY BYTE-FOR-BYTE THE SAME FOLD AS THE SIMPLE LEG
            // (vk2d_bench.spl): same n, same stride, same seed, same prime,
            // same 32-bit mask, same iteration order. If the two diverge the
            // checksums stop being comparable and the gate's premise breaks.
            // u64 + an explicit mask (not u32 wraparound) so the expression is
            // literally the same as the Simple leg's i64 one.
            const u64 n = fb_size / 4;
            u64 stride = n / 4096;
            if (stride < 1) stride = 1;
            u64 acc = 2166136261u;
            for (u64 i = 0; i < n; i += stride) {
                const u64 px = (u64)fb_pixels[i] & 0xFFFFFFFFu;
                acc = ((acc ^ px) * 16777619u) & 0xFFFFFFFFu;
            }
            if (!checksum_latched) { checksum = acc; checksum_latched = 1; }
            else if (acc != checksum) { frame_mismatches++; }
        }
    }
    u64 t1 = now_ns();

    // Raw framebuffer dump for the byte-for-byte comparator. Written AFTER
    // the frame loop, so it is the same pixels the checksum folded.
    const char* dump_path = getenv("VK2D_DUMP_FB");
    if (dump_path && do_readback) {
        FILE* df = fopen(dump_path, "wb");
        if (df) {
            fwrite(fb_pixels, 1, fb_size, df);
            fclose(df);
            fprintf(stderr, "dump: wrote %llu bytes to %s\n",
                (unsigned long long)fb_size, dump_path);
        }
    }

    if (getenv("VK2D_DEBUG")) {
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
    printf("c-vulkan-2d w=%d h=%d rects=%d frames=%d readback=%d ms=%.1f fps=%.1f checksum=%llu frame_mismatches=%llu\n",
        fb_w, fb_h, num_rects, num_frames, do_readback, ms, fps,
        (unsigned long long)checksum, (unsigned long long)frame_mismatches);

    free(rects);
    vkUnmapMemory(device, memory);
    vkDestroyFence(device, fence, NULL);
    vkDestroyCommandPool(device, cmd_pool, NULL);
    vkDestroyPipeline(device, pipeline, NULL);
    vkDestroyPipelineLayout(device, pipeline_layout, NULL);
    vkDestroyDescriptorPool(device, descriptor_pool, NULL);
    vkDestroyDescriptorSetLayout(device, descriptor_set_layout, NULL);
    vkDestroyShaderModule(device, shader_module, NULL);
    vkFreeMemory(device, memory, NULL);
    vkDestroyBuffer(device, fb_buffer, NULL);
    vkDestroyDevice(device, NULL);
    vkDestroyInstance(instance, NULL);
    return 0;
}
