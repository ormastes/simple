/* Physical Vulkan evidence probe for the ML-KEM forward/inverse NTT candidate. */
#include <vulkan/vulkan.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "ntt_fixture.h"

#define N 256
#define BATCH 3
#define Q 3329
#define VK_OK(call) do { VkResult _r = (call); if (_r != VK_SUCCESS) { \
    fprintf(stderr, "%s failed: %d\n", #call, (int)_r); goto cleanup; } } while (0)

static const int32_t zetas[128] = {
1,1729,2580,3289,2642,630,1897,848,1062,1919,193,797,2786,3260,569,1746,
296,2447,1339,1476,3046,56,2240,1333,1426,2094,535,2882,2393,2879,1974,821,
289,331,3253,1756,1197,2304,2277,2055,650,1977,2513,632,2865,33,1320,1915,
2319,1435,807,452,1438,2868,1534,2402,2647,2617,1481,648,2474,3110,1227,910,
17,2761,583,2649,1637,723,2288,1100,1409,2662,3281,233,756,2156,3015,3050,
1703,1651,2789,1789,1847,952,1461,2687,939,2308,2437,2388,733,2337,268,641,
1584,2298,2037,3220,375,2549,2090,1645,1063,319,2773,757,2099,561,2466,2594,
2804,1092,403,1026,1143,2150,2775,886,1722,1212,1874,1029,2110,2935,885,2154};

typedef struct Buffer {
    VkBuffer buffer;
    VkDeviceMemory memory;
} Buffer;

static int32_t modq(int64_t x) {
    int32_t r = (int32_t)(x % Q);
    return r < 0 ? r + Q : r;
}

static void scalar_ntt(int32_t *f, uint32_t stage_count) {
    int k = 1;
    for (uint32_t stage = 0; stage < stage_count; ++stage) {
        int len = 128 >> stage;
        for (int start = 0; start < N; start += 2 * len) {
            int32_t zeta = zetas[k++];
            for (int j = start; j < start + len; ++j) {
                int32_t t = modq((int64_t)zeta * f[j + len]);
                int32_t lower = f[j];
                f[j] = modq((int64_t)lower + t);
                f[j + len] = modq((int64_t)lower - t);
            }
        }
    }
}

static void scalar_intt(int32_t *f, uint32_t stage_count) {
    int k = 127;
    for (uint32_t stage = 0; stage < stage_count; ++stage) {
        int len = 2 << stage;
        for (int start = 0; start < N; start += 2 * len) {
            int32_t zeta = zetas[k--];
            for (int j = start; j < start + len; ++j) {
                int32_t lower = f[j];
                int32_t upper = f[j + len];
                f[j] = modq((int64_t)lower + upper);
                f[j + len] = modq((int64_t)zeta * modq((int64_t)upper - lower));
            }
        }
    }
    for (int i = 0; i < N; ++i) f[i] = modq((int64_t)f[i] * 3303);
}

static uint32_t memory_type(VkPhysicalDevice physical, uint32_t bits,
                            VkMemoryPropertyFlags required) {
    VkPhysicalDeviceMemoryProperties properties;
    vkGetPhysicalDeviceMemoryProperties(physical, &properties);
    for (uint32_t i = 0; i < properties.memoryTypeCount; ++i) {
        if ((bits & (1u << i)) &&
            (properties.memoryTypes[i].propertyFlags & required) == required) return i;
    }
    return UINT32_MAX;
}

static int create_buffer(VkPhysicalDevice physical, VkDevice device,
                         VkDeviceSize size, VkBufferUsageFlags usage,
                         VkMemoryPropertyFlags memory_flags, Buffer *out) {
    VkBufferCreateInfo info = {.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO};
    info.size = size;
    info.usage = usage;
    info.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
    if (vkCreateBuffer(device, &info, NULL, &out->buffer) != VK_SUCCESS) return 0;
    VkMemoryRequirements requirements;
    vkGetBufferMemoryRequirements(device, out->buffer, &requirements);
    uint32_t type = memory_type(physical, requirements.memoryTypeBits, memory_flags);
    if (type == UINT32_MAX) return 0;
    VkMemoryAllocateInfo allocation = {
        .sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO};
    allocation.allocationSize = requirements.size;
    allocation.memoryTypeIndex = type;
    if (vkAllocateMemory(device, &allocation, NULL, &out->memory) != VK_SUCCESS) return 0;
    return vkBindBufferMemory(device, out->buffer, out->memory, 0) == VK_SUCCESS;
}

static void destroy_buffer(VkDevice device, Buffer *buffer) {
    if (buffer->buffer) vkDestroyBuffer(device, buffer->buffer, NULL);
    if (buffer->memory) vkFreeMemory(device, buffer->memory, NULL);
    memset(buffer, 0, sizeof(*buffer));
}

static uint32_t *read_spirv(const char *path, size_t *byte_count) {
    FILE *file = fopen(path, "rb");
    if (!file) return NULL;
    if (fseek(file, 0, SEEK_END) != 0) { fclose(file); return NULL; }
    long length = ftell(file);
    if (length <= 0 || (length % 4) != 0) { fclose(file); return NULL; }
    rewind(file);
    uint32_t *data = malloc((size_t)length);
    if (!data || fread(data, 1, (size_t)length, file) != (size_t)length) {
        free(data); fclose(file); return NULL;
    }
    fclose(file);
    *byte_count = (size_t)length;
    return data;
}

static int run_device(VkPhysicalDevice physical, uint32_t ordinal,
                      const uint32_t *spirv, size_t spirv_size,
                      uint32_t stage_count, int inverse) {
    VkPhysicalDeviceProperties properties;
    vkGetPhysicalDeviceProperties(physical, &properties);
    if (properties.deviceType != VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU &&
        properties.deviceType != VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU) return -1;

    uint32_t family_count = 0, queue_family = UINT32_MAX;
    vkGetPhysicalDeviceQueueFamilyProperties(physical, &family_count, NULL);
    VkQueueFamilyProperties *families = calloc(family_count, sizeof(*families));
    vkGetPhysicalDeviceQueueFamilyProperties(physical, &family_count, families);
    for (uint32_t i = 0; i < family_count; ++i) {
        if (families[i].queueFlags & VK_QUEUE_COMPUTE_BIT) { queue_family = i; break; }
    }
    free(families);
    if (queue_family == UINT32_MAX) return 0;

    VkDevice device = VK_NULL_HANDLE;
    VkShaderModule shader = VK_NULL_HANDLE;
    VkDescriptorSetLayout set_layout = VK_NULL_HANDLE;
    VkPipelineLayout pipeline_layout = VK_NULL_HANDLE;
    VkPipeline pipeline = VK_NULL_HANDLE;
    VkDescriptorPool descriptor_pool = VK_NULL_HANDLE;
    VkCommandPool command_pool = VK_NULL_HANDLE;
    VkFence fence = VK_NULL_HANDLE;
    Buffer staging_input = {0}, staging_output = {0}, staging_zeta = {0},
           device_input = {0}, device_output = {0}, zeta_buffer = {0};
    int passed = 0;
    const VkDeviceSize bytes = BATCH * N * sizeof(int32_t);

    float priority = 1.0f;
    VkDeviceQueueCreateInfo queue_info = {
        .sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO};
    queue_info.queueFamilyIndex = queue_family;
    queue_info.queueCount = 1;
    queue_info.pQueuePriorities = &priority;
    VkDeviceCreateInfo device_info = {
        .sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO};
    device_info.queueCreateInfoCount = 1;
    device_info.pQueueCreateInfos = &queue_info;
    VK_OK(vkCreateDevice(physical, &device_info, NULL, &device));
    VkQueue queue;
    vkGetDeviceQueue(device, queue_family, 0, &queue);

    if (!create_buffer(physical, device, bytes, VK_BUFFER_USAGE_TRANSFER_SRC_BIT,
            VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
            &staging_input) ||
        !create_buffer(physical, device, bytes, VK_BUFFER_USAGE_TRANSFER_DST_BIT,
            VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
            &staging_output) ||
        !create_buffer(physical, device, bytes,
            VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT,
            VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, &device_input) ||
        !create_buffer(physical, device, bytes,
            VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT,
            VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, &device_output) ||
        !create_buffer(physical, device, sizeof(zetas),
            VK_BUFFER_USAGE_TRANSFER_SRC_BIT,
            VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
            &staging_zeta) ||
        !create_buffer(physical, device, sizeof(zetas),
            VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT,
            VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
            &zeta_buffer)) goto cleanup;

    int32_t input[BATCH * N], expected[BATCH * N];
    for (int p = 0; p < BATCH; ++p) {
        for (int i = 0; i < N; ++i) {
            input[p * N + i] =
                x25519mlkem768_ntt_fixture_coefficient(p, i);
            expected[p * N + i] = input[p * N + i];
        }
        if (inverse) {
            scalar_ntt(&input[p * N], 7);
            memcpy(&expected[p * N], &input[p * N], N * sizeof(int32_t));
            scalar_intt(&expected[p * N], stage_count);
        } else {
            scalar_ntt(&expected[p * N], stage_count);
        }
    }
    void *mapped = NULL;
    VK_OK(vkMapMemory(device, staging_input.memory, 0, bytes, 0, &mapped));
    memcpy(mapped, input, (size_t)bytes);
    vkUnmapMemory(device, staging_input.memory);
    VK_OK(vkMapMemory(device, staging_zeta.memory, 0, sizeof(zetas), 0, &mapped));
    memcpy(mapped, zetas, sizeof(zetas));
    vkUnmapMemory(device, staging_zeta.memory);

    VkShaderModuleCreateInfo shader_info = {
        .sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO};
    shader_info.codeSize = spirv_size;
    shader_info.pCode = spirv;
    VK_OK(vkCreateShaderModule(device, &shader_info, NULL, &shader));
    VkDescriptorSetLayoutBinding bindings[3] = {0};
    for (uint32_t i = 0; i < 3; ++i) {
        bindings[i].binding = i;
        bindings[i].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        bindings[i].descriptorCount = 1;
        bindings[i].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
    }
    VkDescriptorSetLayoutCreateInfo set_info = {
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO};
    set_info.bindingCount = 3;
    set_info.pBindings = bindings;
    VK_OK(vkCreateDescriptorSetLayout(device, &set_info, NULL, &set_layout));
    typedef struct Parameters {
        uint32_t polynomial_count;
        uint32_t stage_count;
    } Parameters;
    VkPushConstantRange push = {
        VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(Parameters)};
    VkPipelineLayoutCreateInfo layout_info = {
        .sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO};
    layout_info.setLayoutCount = 1;
    layout_info.pSetLayouts = &set_layout;
    layout_info.pushConstantRangeCount = 1;
    layout_info.pPushConstantRanges = &push;
    VK_OK(vkCreatePipelineLayout(device, &layout_info, NULL, &pipeline_layout));
    VkComputePipelineCreateInfo pipeline_info = {
        .sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO};
    pipeline_info.stage.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
    pipeline_info.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
    pipeline_info.stage.module = shader;
    pipeline_info.stage.pName = "main";
    pipeline_info.layout = pipeline_layout;
    VK_OK(vkCreateComputePipelines(device, VK_NULL_HANDLE, 1, &pipeline_info, NULL, &pipeline));

    VkDescriptorPoolSize pool_size = {VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 3};
    VkDescriptorPoolCreateInfo pool_info = {
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO};
    pool_info.maxSets = 1; pool_info.poolSizeCount = 1; pool_info.pPoolSizes = &pool_size;
    VK_OK(vkCreateDescriptorPool(device, &pool_info, NULL, &descriptor_pool));
    VkDescriptorSetAllocateInfo set_alloc = {
        .sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO};
    set_alloc.descriptorPool = descriptor_pool; set_alloc.descriptorSetCount = 1;
    set_alloc.pSetLayouts = &set_layout;
    VkDescriptorSet descriptor_set;
    VK_OK(vkAllocateDescriptorSets(device, &set_alloc, &descriptor_set));
    VkDescriptorBufferInfo buffer_infos[3] = {
        {device_input.buffer, 0, bytes}, {device_output.buffer, 0, bytes},
        {zeta_buffer.buffer, 0, sizeof(zetas)}};
    VkWriteDescriptorSet writes[3] = {0};
    for (uint32_t i = 0; i < 3; ++i) {
        writes[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        writes[i].dstSet = descriptor_set; writes[i].dstBinding = i;
        writes[i].descriptorCount = 1; writes[i].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        writes[i].pBufferInfo = &buffer_infos[i];
    }
    vkUpdateDescriptorSets(device, 3, writes, 0, NULL);

    VkCommandPoolCreateInfo command_pool_info = {
        .sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO};
    command_pool_info.queueFamilyIndex = queue_family;
    VK_OK(vkCreateCommandPool(device, &command_pool_info, NULL, &command_pool));
    VkCommandBufferAllocateInfo command_alloc = {
        .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO};
    command_alloc.commandPool = command_pool; command_alloc.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    command_alloc.commandBufferCount = 1;
    VkCommandBuffer command;
    VK_OK(vkAllocateCommandBuffers(device, &command_alloc, &command));
    VkCommandBufferBeginInfo begin = {
        .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO};
    VK_OK(vkBeginCommandBuffer(command, &begin));
    VkBufferCopy copy = {0, 0, bytes};
    vkCmdCopyBuffer(command, staging_input.buffer, device_input.buffer, 1, &copy);
    VkBufferCopy zeta_copy = {0, 0, sizeof(zetas)};
    vkCmdCopyBuffer(
        command, staging_zeta.buffer, zeta_buffer.buffer, 1, &zeta_copy);
    VkMemoryBarrier upload_barrier = {
        .sType = VK_STRUCTURE_TYPE_MEMORY_BARRIER};
    upload_barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
    upload_barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
    vkCmdPipelineBarrier(command, VK_PIPELINE_STAGE_TRANSFER_BIT,
        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, 0, 1, &upload_barrier, 0, NULL, 0, NULL);
    vkCmdBindPipeline(command, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline);
    vkCmdBindDescriptorSets(command, VK_PIPELINE_BIND_POINT_COMPUTE,
        pipeline_layout, 0, 1, &descriptor_set, 0, NULL);
    Parameters parameters = {BATCH, stage_count};
    vkCmdPushConstants(command, pipeline_layout, VK_SHADER_STAGE_COMPUTE_BIT,
        0, sizeof(parameters), &parameters);
    vkCmdDispatch(command, BATCH, 1, 1);
    VkMemoryBarrier read_barrier = {
        .sType = VK_STRUCTURE_TYPE_MEMORY_BARRIER};
    read_barrier.srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT;
    read_barrier.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
    vkCmdPipelineBarrier(command, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
        VK_PIPELINE_STAGE_TRANSFER_BIT, 0, 1, &read_barrier, 0, NULL, 0, NULL);
    vkCmdCopyBuffer(command, device_output.buffer, staging_output.buffer, 1, &copy);
    VK_OK(vkEndCommandBuffer(command));
    VkSubmitInfo submit = {.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO};
    submit.commandBufferCount = 1; submit.pCommandBuffers = &command;
    VkFenceCreateInfo fence_info = {
        .sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO};
    VK_OK(vkCreateFence(device, &fence_info, NULL, &fence));
    VK_OK(vkQueueSubmit(queue, 1, &submit, fence));
    VK_OK(vkWaitForFences(device, 1, &fence, VK_TRUE, 10000000000ULL));
    VK_OK(vkMapMemory(device, staging_output.memory, 0, bytes, 0, &mapped));
    if (memcmp(mapped, expected, (size_t)bytes) != 0) {
        int32_t *actual = mapped;
        for (int i = 0; i < BATCH * N; ++i) if (actual[i] != expected[i]) {
            fprintf(stderr, "device=%u mismatch index=%d expected=%d actual=%d\n",
                    ordinal, i, expected[i], actual[i]); break;
        }
        for (int i = 0; i < 16; ++i) {
            fprintf(stderr, "  coefficient[%d] expected=%d actual=%d\n",
                    i, expected[i], actual[i]);
        }
        vkUnmapMemory(device, staging_output.memory); goto cleanup;
    }
    vkUnmapMemory(device, staging_output.memory);
    printf("PASS backend=vulkan operation=%s device=%u name=%s "
           "vendor=0x%04x device_id=0x%04x api_version=%u "
           "driver_version=%u "
           "compile=1 submit=1 fence=1 readback=1 oracle_match=1 "
           "batch=%d stages=%u fixture_id=%s\n",
           inverse ? "inverse" : "forward", ordinal, properties.deviceName,
           properties.vendorID, properties.deviceID, properties.apiVersion,
           properties.driverVersion, BATCH, stage_count,
           X25519MLKEM768_NTT_FIXTURE_ID);
    passed = 1;

cleanup:
    if (device) vkDeviceWaitIdle(device);
    if (fence) vkDestroyFence(device, fence, NULL);
    if (command_pool) vkDestroyCommandPool(device, command_pool, NULL);
    if (descriptor_pool) vkDestroyDescriptorPool(device, descriptor_pool, NULL);
    if (pipeline) vkDestroyPipeline(device, pipeline, NULL);
    if (pipeline_layout) vkDestroyPipelineLayout(device, pipeline_layout, NULL);
    if (set_layout) vkDestroyDescriptorSetLayout(device, set_layout, NULL);
    if (shader) vkDestroyShaderModule(device, shader, NULL);
    if (device) {
        destroy_buffer(device, &zeta_buffer);
        destroy_buffer(device, &staging_zeta);
        destroy_buffer(device, &device_output); destroy_buffer(device, &device_input);
        destroy_buffer(device, &staging_output); destroy_buffer(device, &staging_input);
        vkDestroyDevice(device, NULL);
    }
    return passed;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) {
        fprintf(stderr,
                "usage: %s <spirv> <forward|inverse> [stage-count:1..7]\n",
                argv[0]);
        return 2;
    }
    int inverse = 0;
    if (strcmp(argv[2], "inverse") == 0) inverse = 1;
    else if (strcmp(argv[2], "forward") != 0) {
        fprintf(stderr, "operation must be forward or inverse\n");
        return 2;
    }
    char *stage_end = NULL;
    unsigned long requested_stages =
        argc == 4 ? strtoul(argv[3], &stage_end, 10) : 7;
    if (requested_stages < 1 || requested_stages > 7 ||
            (argc == 4 && (!stage_end || *stage_end != '\0'))) {
        fprintf(stderr, "stage-count must be an integer from 1 through 7\n");
        return 2;
    }
    uint32_t stage_count = (uint32_t)requested_stages;
    size_t spirv_size = 0;
    uint32_t *spirv = read_spirv(argv[1], &spirv_size);
    if (!spirv) return 1;
    VkApplicationInfo app = {.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO};
    app.pApplicationName = "x25519mlkem768-vulkan-ntt-probe";
    app.apiVersion = VK_API_VERSION_1_1;
    VkInstanceCreateInfo instance_info = {
        .sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO};
    instance_info.pApplicationInfo = &app;
    VkInstance instance = VK_NULL_HANDLE;
    if (vkCreateInstance(&instance_info, NULL, &instance) != VK_SUCCESS) { free(spirv); return 1; }
    uint32_t count = 0;
    vkEnumeratePhysicalDevices(instance, &count, NULL);
    VkPhysicalDevice *devices = calloc(count, sizeof(*devices));
    vkEnumeratePhysicalDevices(instance, &count, devices);
    int physical = 0, passed = 0;
    for (uint32_t i = 0; i < count; ++i) {
        int result = run_device(
            devices[i], i, spirv, spirv_size, stage_count, inverse);
        if (result >= 0) { ++physical; passed += result; }
    }
    free(devices); free(spirv); vkDestroyInstance(instance, NULL);
    return physical > 0 && passed == physical ? 0 : 1;
}
