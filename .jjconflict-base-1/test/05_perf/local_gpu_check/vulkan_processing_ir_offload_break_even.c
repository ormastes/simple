/* Real Vulkan ProcessingIR break-even harness.
 * CPU and vkCmdDispatch execute the same repeated u32 fill. No fallback exists.
 */
#define _POSIX_C_SOURCE 200809L
#include <dlfcn.h>
#include <vulkan/vulkan.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>

#define DLSYM(h, n) (PFN_##n)dlsym((h), #n)
#define MAX_BATCHES 8
#define COMMANDS_PER_ROW 4
#define FILL_REPETITIONS 64
#define LOCAL_SIZE 256u
#define FILL_VALUE 0x12345678u

/* Validated with: spirv-val --target-env vulkan1.0. */
static const uint32_t fill_spirv[] = {
    119734787,65536,458752,35,0,131089,1,196622,0,1,393231,5,1,1852399981,0,2,
    393232,1,17,256,1,1,262215,2,11,28,262215,3,6,4,327752,4,0,35,0,196679,4,3,
    262215,5,34,0,262215,5,33,0,327752,6,0,35,0,327752,6,1,35,4,327752,6,2,35,8,
    196679,6,2,131091,7,196641,8,7,262165,9,32,0,131092,10,262167,11,9,3,196637,
    3,9,196638,4,3,262176,12,2,4,262176,13,2,9,262203,12,5,2,327710,6,9,9,9,
    262176,14,9,6,262176,15,9,9,262203,14,16,9,262176,17,1,11,262203,17,2,1,
    262187,9,18,0,262187,9,19,1,262187,9,20,2,327734,7,1,0,8,131320,21,262205,
    11,22,2,327761,9,23,22,0,327745,15,24,16,19,262205,9,25,24,327856,10,26,
    23,25,196855,27,0,262394,26,28,27,131320,28,327745,15,29,16,18,262205,9,
    30,29,327745,15,31,16,20,262205,9,32,31,327808,9,33,32,23,393281,13,34,
    5,18,33,196670,34,30,131321,27,131320,27,65789,65592
};

struct sample { long long cpu_us, upload_us, device_us, readback_us, transfer_us, total_us, mismatch; };
struct push_constants { uint32_t value, count, base; };
struct vk_api {
    void *lib;
    PFN_vkCreateInstance create_instance; PFN_vkDestroyInstance destroy_instance;
    PFN_vkEnumeratePhysicalDevices enumerate_physical_devices;
    PFN_vkGetPhysicalDeviceProperties get_properties;
    PFN_vkGetPhysicalDeviceProperties2 get_properties2;
    PFN_vkGetPhysicalDeviceMemoryProperties get_memory_properties;
    PFN_vkGetPhysicalDeviceQueueFamilyProperties get_queue_properties;
    PFN_vkCreateDevice create_device; PFN_vkDestroyDevice destroy_device; PFN_vkGetDeviceQueue get_queue;
    PFN_vkCreateBuffer create_buffer; PFN_vkDestroyBuffer destroy_buffer;
    PFN_vkGetBufferMemoryRequirements get_requirements; PFN_vkAllocateMemory allocate_memory;
    PFN_vkFreeMemory free_memory; PFN_vkBindBufferMemory bind_memory;
    PFN_vkMapMemory map_memory; PFN_vkUnmapMemory unmap_memory;
    PFN_vkFlushMappedMemoryRanges flush_memory; PFN_vkInvalidateMappedMemoryRanges invalidate_memory;
    PFN_vkCreateCommandPool create_pool; PFN_vkDestroyCommandPool destroy_pool;
    PFN_vkResetCommandPool reset_pool; PFN_vkAllocateCommandBuffers allocate_commands;
    PFN_vkBeginCommandBuffer begin_command; PFN_vkEndCommandBuffer end_command;
    PFN_vkCmdCopyBuffer copy_buffer; PFN_vkCmdPipelineBarrier pipeline_barrier;
    PFN_vkCreateShaderModule create_shader_module; PFN_vkDestroyShaderModule destroy_shader_module;
    PFN_vkCreateDescriptorSetLayout create_descriptor_layout;
    PFN_vkDestroyDescriptorSetLayout destroy_descriptor_layout;
    PFN_vkCreateDescriptorPool create_descriptor_pool; PFN_vkDestroyDescriptorPool destroy_descriptor_pool;
    PFN_vkAllocateDescriptorSets allocate_descriptor_sets; PFN_vkUpdateDescriptorSets update_descriptor_sets;
    PFN_vkCreatePipelineLayout create_pipeline_layout; PFN_vkDestroyPipelineLayout destroy_pipeline_layout;
    PFN_vkCreateComputePipelines create_compute_pipelines; PFN_vkDestroyPipeline destroy_pipeline;
    PFN_vkCmdBindPipeline bind_pipeline; PFN_vkCmdBindDescriptorSets bind_descriptor_sets;
    PFN_vkCmdPushConstants push_constants; PFN_vkCmdDispatch dispatch;
    PFN_vkCreateFence create_fence; PFN_vkDestroyFence destroy_fence;
    PFN_vkResetFences reset_fences; PFN_vkQueueSubmit queue_submit; PFN_vkWaitForFences wait_fences;
    PFN_vkDeviceWaitIdle wait_idle;
};
struct vk_state {
    struct vk_api a; VkInstance instance; VkPhysicalDevice physical; VkDevice device; VkQueue queue;
    VkCommandPool pool; VkCommandBuffer command; VkFence fence;
    VkBuffer buffer, staging_buffer; VkDeviceMemory memory, staging_memory;
    VkShaderModule shader_module; VkDescriptorSetLayout descriptor_layout;
    VkDescriptorPool descriptor_pool; VkDescriptorSet descriptor_set;
    VkPipelineLayout pipeline_layout; VkPipeline pipeline;
    VkDeviceSize bytes, active_bytes; uint32_t queue_family;
    VkMemoryPropertyFlags memory_flags, staging_memory_flags;
    VkPhysicalDeviceProperties properties; VkPhysicalDeviceDriverProperties driver;
    int driver_properties_available;
};

static long long now_ns(void) { struct timespec t; return clock_gettime(CLOCK_MONOTONIC, &t) ? -1 : (long long)t.tv_sec * 1000000000LL + t.tv_nsec; }
static long long elapsed_us(long long a, long long b) { return a < 0 || b < a ? -1 : (b - a + 999) / 1000; }
static int parse_int(const char *s, int min, int max, int *out) { char *e = NULL; long v = strtol(s, &e, 10); if (!*s || !e || *e || v < min || v > max) return 0; *out = (int)v; return 1; }
static int parse_batch(const char *s, unsigned int *out) { char *e = NULL; unsigned long v = strtoul(s, &e, 10); if (!*s || !e || *e || v < COMMANDS_PER_ROW || v > 67108864UL) return 0; *out = (unsigned int)v; return 1; }
static int32_t find_memory(const VkPhysicalDeviceMemoryProperties *p, uint32_t bits, VkMemoryPropertyFlags flags) { uint32_t i; for (i = 0; i < p->memoryTypeCount; i++) if ((bits & (1u << i)) && (p->memoryTypes[i].propertyFlags & flags) == flags) return (int32_t)i; return -1; }
static int is_software_name(const char *name) { const char *bad[] = {"llvmpipe","lavapipe","swiftshader","software"}; size_t i; const char *p; for (i = 0; i < sizeof(bad)/sizeof(bad[0]); i++) for (p = name; *p; p++) if (!strncasecmp(p, bad[i], strlen(bad[i]))) return 1; return 0; }
static int admitted_device_type(VkPhysicalDeviceType type) { return type != VK_PHYSICAL_DEVICE_TYPE_CPU && (type == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU || type == VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU); }
static void cpu_fill(volatile uint32_t *out, unsigned int count) { unsigned int r, i; for (r = 0; r < FILL_REPETITIONS; r++) for (i = 0; i < count; i++) out[i] = FILL_VALUE; }
static long long mismatch(const uint32_t *out, unsigned int count) { unsigned int i; long long n = 0; for (i = 0; i < count; i++) if (out[i] != FILL_VALUE) n++; return n; }
static void sort_values(long long *v, int n) { int i; for (i = 1; i < n; i++) { long long x = v[i]; int j = i - 1; while (j >= 0 && v[j] > x) { v[j + 1] = v[j]; j--; } v[j + 1] = x; } }
static long long median(const struct sample *s, int n, int f) { long long v[64]; int i; for (i = 0; i < n; i++) v[i] = f==0?s[i].cpu_us:f==1?s[i].upload_us:f==2?s[i].device_us:f==3?s[i].readback_us:f==4?s[i].transfer_us:f==5?s[i].total_us:s[i].mismatch; sort_values(v,n); return v[n/2]; }
static int read_rss(const char *key) { FILE *f = fopen("/proc/self/status","r"); char line[128], name[32]; long value; int result=0; if (!f) return 0; while (fgets(line,sizeof(line),f)) if (sscanf(line,"%31[^:]: %ld",name,&value)==2 && !strcmp(name,key)) { result=value>0&&value<2147483647L?(int)value:0; break; } fclose(f); return result; }
static void emit_failure(const char *why) { printf("processing_ir_vulkan_offload_status=fail\nprocessing_ir_vulkan_offload_reason=%s\nprocessing_ir_vulkan_offload_schema=processing-ir-offload-v1\nprocessing_ir_vulkan_offload_execution=processing_ir\nprocessing_ir_vulkan_offload_backend=vulkan\n",why); }

static void close_state(struct vk_state *s) {
    if (s->a.wait_idle && s->device) s->a.wait_idle(s->device);
    if (s->a.destroy_pipeline && s->pipeline) s->a.destroy_pipeline(s->device,s->pipeline,NULL);
    if (s->a.destroy_pipeline_layout && s->pipeline_layout) s->a.destroy_pipeline_layout(s->device,s->pipeline_layout,NULL);
    if (s->a.destroy_descriptor_pool && s->descriptor_pool) s->a.destroy_descriptor_pool(s->device,s->descriptor_pool,NULL);
    if (s->a.destroy_descriptor_layout && s->descriptor_layout) s->a.destroy_descriptor_layout(s->device,s->descriptor_layout,NULL);
    if (s->a.destroy_shader_module && s->shader_module) s->a.destroy_shader_module(s->device,s->shader_module,NULL);
    if (s->a.destroy_fence && s->fence) s->a.destroy_fence(s->device,s->fence,NULL);
    if (s->a.destroy_pool && s->pool) s->a.destroy_pool(s->device,s->pool,NULL);
    if (s->a.destroy_buffer && s->staging_buffer) s->a.destroy_buffer(s->device,s->staging_buffer,NULL);
    if (s->a.destroy_buffer && s->buffer) s->a.destroy_buffer(s->device,s->buffer,NULL);
    if (s->a.free_memory && s->staging_memory) s->a.free_memory(s->device,s->staging_memory,NULL);
    if (s->a.free_memory && s->memory) s->a.free_memory(s->device,s->memory,NULL);
    if (s->a.destroy_device && s->device) s->a.destroy_device(s->device,NULL);
    if (s->a.destroy_instance && s->instance) s->a.destroy_instance(s->instance,NULL);
    if (s->a.lib) dlclose(s->a.lib);
    memset(s,0,sizeof(*s));
}

static int load_api(struct vk_api *a) {
    memset(a,0,sizeof(*a)); a->lib=dlopen("libvulkan.so.1",RTLD_LAZY); if (!a->lib) a->lib=dlopen("libvulkan.so",RTLD_LAZY); if (!a->lib) return 0;
#define LOAD(f,n) a->f=DLSYM(a->lib,vk##n)
    LOAD(create_instance,CreateInstance); LOAD(destroy_instance,DestroyInstance); LOAD(enumerate_physical_devices,EnumeratePhysicalDevices);
    LOAD(get_properties,GetPhysicalDeviceProperties); LOAD(get_properties2,GetPhysicalDeviceProperties2);
    LOAD(get_memory_properties,GetPhysicalDeviceMemoryProperties); LOAD(get_queue_properties,GetPhysicalDeviceQueueFamilyProperties);
    LOAD(create_device,CreateDevice); LOAD(destroy_device,DestroyDevice); LOAD(get_queue,GetDeviceQueue);
    LOAD(create_buffer,CreateBuffer); LOAD(destroy_buffer,DestroyBuffer); LOAD(get_requirements,GetBufferMemoryRequirements);
    LOAD(allocate_memory,AllocateMemory); LOAD(free_memory,FreeMemory); LOAD(bind_memory,BindBufferMemory);
    LOAD(map_memory,MapMemory); LOAD(unmap_memory,UnmapMemory); LOAD(flush_memory,FlushMappedMemoryRanges); LOAD(invalidate_memory,InvalidateMappedMemoryRanges);
    LOAD(create_pool,CreateCommandPool); LOAD(destroy_pool,DestroyCommandPool); LOAD(reset_pool,ResetCommandPool);
    LOAD(allocate_commands,AllocateCommandBuffers); LOAD(begin_command,BeginCommandBuffer); LOAD(end_command,EndCommandBuffer);
    LOAD(copy_buffer,CmdCopyBuffer); LOAD(pipeline_barrier,CmdPipelineBarrier);
    LOAD(create_shader_module,CreateShaderModule); LOAD(destroy_shader_module,DestroyShaderModule);
    LOAD(create_descriptor_layout,CreateDescriptorSetLayout); LOAD(destroy_descriptor_layout,DestroyDescriptorSetLayout);
    LOAD(create_descriptor_pool,CreateDescriptorPool); LOAD(destroy_descriptor_pool,DestroyDescriptorPool);
    LOAD(allocate_descriptor_sets,AllocateDescriptorSets); LOAD(update_descriptor_sets,UpdateDescriptorSets);
    LOAD(create_pipeline_layout,CreatePipelineLayout); LOAD(destroy_pipeline_layout,DestroyPipelineLayout);
    LOAD(create_compute_pipelines,CreateComputePipelines); LOAD(destroy_pipeline,DestroyPipeline);
    LOAD(bind_pipeline,CmdBindPipeline); LOAD(bind_descriptor_sets,CmdBindDescriptorSets);
    LOAD(push_constants,CmdPushConstants); LOAD(dispatch,CmdDispatch);
    LOAD(create_fence,CreateFence); LOAD(destroy_fence,DestroyFence); LOAD(reset_fences,ResetFences);
    LOAD(queue_submit,QueueSubmit); LOAD(wait_fences,WaitForFences); LOAD(wait_idle,DeviceWaitIdle);
#undef LOAD
    return a->create_instance&&a->destroy_instance&&a->enumerate_physical_devices&&a->get_properties&&a->get_memory_properties&&a->get_queue_properties&&a->create_device&&a->destroy_device&&a->get_queue&&a->create_buffer&&a->destroy_buffer&&a->get_requirements&&a->allocate_memory&&a->free_memory&&a->bind_memory&&a->map_memory&&a->unmap_memory&&a->create_pool&&a->destroy_pool&&a->reset_pool&&a->allocate_commands&&a->begin_command&&a->end_command&&a->copy_buffer&&a->pipeline_barrier&&a->create_shader_module&&a->destroy_shader_module&&a->create_descriptor_layout&&a->destroy_descriptor_layout&&a->create_descriptor_pool&&a->destroy_descriptor_pool&&a->allocate_descriptor_sets&&a->update_descriptor_sets&&a->create_pipeline_layout&&a->destroy_pipeline_layout&&a->create_compute_pipelines&&a->destroy_pipeline&&a->bind_pipeline&&a->bind_descriptor_sets&&a->push_constants&&a->dispatch&&a->create_fence&&a->destroy_fence&&a->reset_fences&&a->queue_submit&&a->wait_fences;
}

static int make_buffer(struct vk_state *s,VkDeviceSize size,VkBufferUsageFlags usage,VkMemoryPropertyFlags required,VkBuffer *buffer,VkDeviceMemory *memory,VkMemoryPropertyFlags *actual) {
    VkBufferCreateInfo b={0}; VkMemoryRequirements req; VkPhysicalDeviceMemoryProperties props; VkMemoryAllocateInfo m={0}; int32_t index;
    b.sType=VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO; b.size=size; b.usage=usage; b.sharingMode=VK_SHARING_MODE_EXCLUSIVE;
    if (s->a.create_buffer(s->device,&b,NULL,buffer)!=VK_SUCCESS) return 0;
    s->a.get_requirements(s->device,*buffer,&req); s->a.get_memory_properties(s->physical,&props); index=find_memory(&props,req.memoryTypeBits,required);
    if (index<0) { s->a.destroy_buffer(s->device,*buffer,NULL); *buffer=VK_NULL_HANDLE; return 0; }
    *actual=props.memoryTypes[index].propertyFlags; m.sType=VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO; m.allocationSize=req.size; m.memoryTypeIndex=(uint32_t)index;
    if (s->a.allocate_memory(s->device,&m,NULL,memory)!=VK_SUCCESS || s->a.bind_memory(s->device,*buffer,*memory,0)!=VK_SUCCESS) { if (*memory) s->a.free_memory(s->device,*memory,NULL); s->a.destroy_buffer(s->device,*buffer,NULL); *memory=VK_NULL_HANDLE; *buffer=VK_NULL_HANDLE; return 0; }
    return 1;
}

static int make_pipeline(struct vk_state *s) {
    VkShaderModuleCreateInfo sm={0}; VkDescriptorSetLayoutBinding binding={0}; VkDescriptorSetLayoutCreateInfo dl={0};
    VkDescriptorPoolSize pool_size={0}; VkDescriptorPoolCreateInfo pool={0}; VkDescriptorSetAllocateInfo alloc={0};
    VkDescriptorBufferInfo buffer={0}; VkWriteDescriptorSet write={0}; VkPushConstantRange push={0};
    VkPipelineLayoutCreateInfo layout={0}; VkPipelineShaderStageCreateInfo stage={0}; VkComputePipelineCreateInfo pipe={0};
    sm.sType=VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO; sm.codeSize=sizeof(fill_spirv); sm.pCode=fill_spirv;
    if (s->a.create_shader_module(s->device,&sm,NULL,&s->shader_module)!=VK_SUCCESS) return 0;
    binding.binding=0; binding.descriptorType=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; binding.descriptorCount=1; binding.stageFlags=VK_SHADER_STAGE_COMPUTE_BIT;
    dl.sType=VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO; dl.bindingCount=1; dl.pBindings=&binding;
    if (s->a.create_descriptor_layout(s->device,&dl,NULL,&s->descriptor_layout)!=VK_SUCCESS) return 0;
    pool_size.type=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; pool_size.descriptorCount=1;
    pool.sType=VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO; pool.maxSets=1; pool.poolSizeCount=1; pool.pPoolSizes=&pool_size;
    if (s->a.create_descriptor_pool(s->device,&pool,NULL,&s->descriptor_pool)!=VK_SUCCESS) return 0;
    alloc.sType=VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO; alloc.descriptorPool=s->descriptor_pool; alloc.descriptorSetCount=1; alloc.pSetLayouts=&s->descriptor_layout;
    if (s->a.allocate_descriptor_sets(s->device,&alloc,&s->descriptor_set)!=VK_SUCCESS) return 0;
    buffer.buffer=s->buffer; buffer.range=s->bytes;
    write.sType=VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; write.dstSet=s->descriptor_set; write.descriptorCount=1; write.descriptorType=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; write.pBufferInfo=&buffer;
    s->a.update_descriptor_sets(s->device,1,&write,0,NULL);
    push.stageFlags=VK_SHADER_STAGE_COMPUTE_BIT; push.size=sizeof(struct push_constants);
    layout.sType=VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO; layout.setLayoutCount=1; layout.pSetLayouts=&s->descriptor_layout; layout.pushConstantRangeCount=1; layout.pPushConstantRanges=&push;
    if (s->a.create_pipeline_layout(s->device,&layout,NULL,&s->pipeline_layout)!=VK_SUCCESS) return 0;
    stage.sType=VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO; stage.stage=VK_SHADER_STAGE_COMPUTE_BIT; stage.module=s->shader_module; stage.pName="main";
    pipe.sType=VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO; pipe.stage=stage; pipe.layout=s->pipeline_layout;
    return s->a.create_compute_pipelines(s->device,VK_NULL_HANDLE,1,&pipe,NULL,&s->pipeline)==VK_SUCCESS;
}

static int init_state(struct vk_state *s,unsigned int count) {
    VkApplicationInfo app={0}; VkInstanceCreateInfo ici={0}; VkPhysicalDevice devices[16]; VkQueueFamilyProperties qp[32];
    VkDeviceQueueCreateInfo qci={0}; VkDeviceCreateInfo dci={0}; VkCommandPoolCreateInfo pci={0};
    VkCommandBufferAllocateInfo cai={0}; VkFenceCreateInfo fci={0}; uint32_t dc=16,qc=0,i; float priority=1.0f;
    memset(s,0,sizeof(*s)); if (!load_api(&s->a)) return 0;
    app.sType=VK_STRUCTURE_TYPE_APPLICATION_INFO; app.pApplicationName="simple-vulkan-break-even"; app.apiVersion=VK_API_VERSION_1_1;
    ici.sType=VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO; ici.pApplicationInfo=&app;
    if (s->a.create_instance(&ici,NULL,&s->instance)!=VK_SUCCESS) return 0;
    if (s->a.enumerate_physical_devices(s->instance,&dc,NULL)!=VK_SUCCESS || !dc || dc>16 || s->a.enumerate_physical_devices(s->instance,&dc,devices)!=VK_SUCCESS) return 0;
    for (i=0;i<dc;i++) { VkPhysicalDeviceProperties p; s->a.get_properties(devices[i],&p); if (admitted_device_type(p.deviceType)&&!is_software_name(p.deviceName)&&p.limits.maxComputeWorkGroupInvocations>=LOCAL_SIZE&&p.limits.maxComputeWorkGroupSize[0]>=LOCAL_SIZE&&p.limits.maxStorageBufferRange>=(VkDeviceSize)count*sizeof(uint32_t)) { s->physical=devices[i]; s->properties=p; break; } }
    if (!s->physical) return 0;
    if (s->a.get_properties2) { VkPhysicalDeviceProperties2 p2={0}; memset(&s->driver,0,sizeof(s->driver)); s->driver.sType=VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_DRIVER_PROPERTIES; p2.sType=VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_PROPERTIES_2; p2.pNext=&s->driver; s->a.get_properties2(s->physical,&p2); s->driver_properties_available=s->driver.driverName[0]!=0; }
    s->a.get_queue_properties(s->physical,&qc,NULL); if (!qc||qc>32) return 0; s->a.get_queue_properties(s->physical,&qc,qp);
    for (i=0;i<qc;i++) {
        if (qp[i].queueCount && (qp[i].queueFlags&VK_QUEUE_COMPUTE_BIT)) {
            s->queue_family=i;
            break;
        }
    }
    if (i==qc) return 0;
    qci.sType=VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO; qci.queueFamilyIndex=s->queue_family; qci.queueCount=1; qci.pQueuePriorities=&priority;
    dci.sType=VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO; dci.queueCreateInfoCount=1; dci.pQueueCreateInfos=&qci;
    if (s->a.create_device(s->physical,&dci,NULL,&s->device)!=VK_SUCCESS) return 0;
    s->a.get_queue(s->device,s->queue_family,0,&s->queue);
    s->bytes=(VkDeviceSize)count*sizeof(uint32_t);
    if (!make_buffer(s,s->bytes,VK_BUFFER_USAGE_STORAGE_BUFFER_BIT|VK_BUFFER_USAGE_TRANSFER_DST_BIT|VK_BUFFER_USAGE_TRANSFER_SRC_BIT,VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,&s->buffer,&s->memory,&s->memory_flags) ||
        (!make_buffer(s,s->bytes,VK_BUFFER_USAGE_TRANSFER_DST_BIT|VK_BUFFER_USAGE_TRANSFER_SRC_BIT,VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT|VK_MEMORY_PROPERTY_HOST_CACHED_BIT,&s->staging_buffer,&s->staging_memory,&s->staging_memory_flags) &&
         !make_buffer(s,s->bytes,VK_BUFFER_USAGE_TRANSFER_DST_BIT|VK_BUFFER_USAGE_TRANSFER_SRC_BIT,VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT,&s->staging_buffer,&s->staging_memory,&s->staging_memory_flags))) return 0;
    if (!make_pipeline(s)) return 0;
    pci.sType=VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO; pci.flags=VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT; pci.queueFamilyIndex=s->queue_family;
    if (s->a.create_pool(s->device,&pci,NULL,&s->pool)!=VK_SUCCESS) return 0;
    cai.sType=VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO; cai.commandPool=s->pool; cai.level=VK_COMMAND_BUFFER_LEVEL_PRIMARY; cai.commandBufferCount=1;
    if (s->a.allocate_commands(s->device,&cai,&s->command)!=VK_SUCCESS) return 0;
    fci.sType=VK_STRUCTURE_TYPE_FENCE_CREATE_INFO; return s->a.create_fence(s->device,&fci,NULL,&s->fence)==VK_SUCCESS;
}

static int map_write(struct vk_state *s,const uint32_t *v,unsigned int count) { void *p=NULL; VkMappedMemoryRange r={VK_STRUCTURE_TYPE_MAPPED_MEMORY_RANGE,NULL,s->staging_memory,0,VK_WHOLE_SIZE}; if (s->a.map_memory(s->device,s->staging_memory,0,VK_WHOLE_SIZE,0,&p)!=VK_SUCCESS) return 0; memcpy(p,v,(size_t)count*4); if (!(s->staging_memory_flags&VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)&&(!s->a.flush_memory||s->a.flush_memory(s->device,1,&r)!=VK_SUCCESS)) { s->a.unmap_memory(s->device,s->staging_memory); return 0; } s->a.unmap_memory(s->device,s->staging_memory); return 1; }
static int map_read(struct vk_state *s,uint32_t *v,unsigned int count) { void *p=NULL; VkMappedMemoryRange r={VK_STRUCTURE_TYPE_MAPPED_MEMORY_RANGE,NULL,s->staging_memory,0,VK_WHOLE_SIZE}; if (s->a.map_memory(s->device,s->staging_memory,0,VK_WHOLE_SIZE,0,&p)!=VK_SUCCESS) return 0; if (!(s->staging_memory_flags&VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)&&(!s->a.invalidate_memory||s->a.invalidate_memory(s->device,1,&r)!=VK_SUCCESS)) { s->a.unmap_memory(s->device,s->staging_memory); return 0; } memcpy(v,p,(size_t)count*4); s->a.unmap_memory(s->device,s->staging_memory); return 1; }
static int submit(struct vk_state *s) { VkSubmitInfo si={0}; if (s->a.end_command(s->command)!=VK_SUCCESS||s->a.reset_fences(s->device,1,&s->fence)!=VK_SUCCESS) return 0; si.sType=VK_STRUCTURE_TYPE_SUBMIT_INFO; si.commandBufferCount=1; si.pCommandBuffers=&s->command; return s->a.queue_submit(s->queue,1,&si,s->fence)==VK_SUCCESS&&s->a.wait_fences(s->device,1,&s->fence,VK_TRUE,10000000000ULL)==VK_SUCCESS; }
static int begin(struct vk_state *s) { VkCommandBufferBeginInfo bi={0}; bi.sType=VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO; return s->a.reset_pool(s->device,s->pool,0)==VK_SUCCESS&&s->a.begin_command(s->command,&bi)==VK_SUCCESS; }
static int submit_copy(struct vk_state *s,VkBuffer src,VkBuffer dst) { VkBufferCopy c={0}; if (!begin(s)) return 0; c.size=s->active_bytes; s->a.copy_buffer(s->command,src,dst,1,&c); return submit(s); }
static int submit_dispatch(struct vk_state *s,unsigned int count,int commands) {
    VkBufferMemoryBarrier b={0}; unsigned int r,c; if (!begin(s)) return 0;
    b.sType=VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER; b.srcAccessMask=VK_ACCESS_TRANSFER_WRITE_BIT; b.dstAccessMask=VK_ACCESS_SHADER_WRITE_BIT; b.srcQueueFamilyIndex=VK_QUEUE_FAMILY_IGNORED; b.dstQueueFamilyIndex=VK_QUEUE_FAMILY_IGNORED; b.buffer=s->buffer; b.size=s->active_bytes;
    s->a.pipeline_barrier(s->command,VK_PIPELINE_STAGE_TRANSFER_BIT,VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,0,0,NULL,1,&b,0,NULL);
    s->a.bind_pipeline(s->command,VK_PIPELINE_BIND_POINT_COMPUTE,s->pipeline);
    s->a.bind_descriptor_sets(s->command,VK_PIPELINE_BIND_POINT_COMPUTE,s->pipeline_layout,0,1,&s->descriptor_set,0,NULL);
    for (r=0;r<FILL_REPETITIONS;r++) for (c=0;c<(unsigned int)commands;c++) {
        struct push_constants p; p.value=FILL_VALUE; p.base=(count*c)/(unsigned int)commands; p.count=(count*(c+1u))/(unsigned int)commands-p.base;
        s->a.push_constants(s->command,s->pipeline_layout,VK_SHADER_STAGE_COMPUTE_BIT,0,sizeof(p),&p);
        s->a.dispatch(s->command,(p.count+LOCAL_SIZE-1)/LOCAL_SIZE,1,1);
    }
    b.srcAccessMask=VK_ACCESS_SHADER_WRITE_BIT; b.dstAccessMask=VK_ACCESS_TRANSFER_READ_BIT;
    s->a.pipeline_barrier(s->command,VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,VK_PIPELINE_STAGE_TRANSFER_BIT,0,0,NULL,1,&b,0,NULL);
    return submit(s);
}
static int run_gpu(struct vk_state *s,unsigned int count,int commands,uint32_t *out,struct sample *x) {
    uint32_t *zeros=calloc(count,sizeof(uint32_t)); long long a,b,c,d; if (!zeros) return 0; a=now_ns();
    if (a<0||!map_write(s,zeros,count)||!submit_copy(s,s->staging_buffer,s->buffer)) { free(zeros); return 0; } b=now_ns();
    if (b<a||!submit_dispatch(s,count,commands)) { free(zeros); return 0; } c=now_ns();
    if (c<b||!submit_copy(s,s->buffer,s->staging_buffer)||!map_read(s,out,count)) { free(zeros); return 0; } d=now_ns(); free(zeros);
    if (d<c) return 0;
    if (x) {
        x->upload_us=elapsed_us(a,b); x->device_us=elapsed_us(b,c);
        x->readback_us=elapsed_us(c,d); x->transfer_us=x->upload_us+x->readback_us;
        x->total_us=x->transfer_us+x->device_us; x->mismatch=mismatch(out,count);
        if (x->upload_us<1||x->device_us<1||x->readback_us<1||x->mismatch) return 0;
    }
    return 1;
}

static void write_provenance(const char *path,const struct vk_state *s,const char *hash,const char *source,const char *workload) { FILE *f=fopen(path,"w"); if (!f) return; fprintf(f,"processing_ir_vulkan_offload_provenance_schema=vulkan-processing-ir-provenance-v1\nprocessing_ir_vulkan_offload_provenance_status=pass\nprocessing_ir_vulkan_offload_provenance_workload_id=%s\nprocessing_ir_vulkan_offload_provenance_source_path=%s\nprocessing_ir_vulkan_offload_provenance_source_sha256=%s\nprocessing_ir_vulkan_offload_provenance_device_name=%s\nprocessing_ir_vulkan_offload_provenance_device_type=%u\nprocessing_ir_vulkan_offload_provenance_vendor_id=%u\nprocessing_ir_vulkan_offload_provenance_device_id=%u\nprocessing_ir_vulkan_offload_provenance_driver_properties_available=%s\nprocessing_ir_vulkan_offload_provenance_driver_id=%u\nprocessing_ir_vulkan_offload_provenance_driver_name=%s\nprocessing_ir_vulkan_offload_provenance_physical_device_admitted=true\nprocessing_ir_vulkan_offload_provenance_readback_source=device_readback\nprocessing_ir_vulkan_offload_provenance_cpu_fallback=false\n",workload,source,hash,s->properties.deviceName,s->properties.deviceType,s->properties.vendorID,s->properties.deviceID,s->driver_properties_available?"true":"false",s->driver.driverID,s->driver.driverName); fclose(f); }
static int dump_spirv(const char *path) { FILE *f=fopen(path,"wb"); if (!f) return 1; if (fwrite(fill_spirv,1,sizeof(fill_spirv),f)!=sizeof(fill_spirv)) { fclose(f); return 1; } return fclose(f)!=0; }
static int self_test(void) { uint32_t v[4]={0}; cpu_fill(v,4); return v[0]==FILL_VALUE&&v[3]==FILL_VALUE&&sizeof(fill_spirv)==844?(puts("vulkan_processing_ir_vulkan_offload_harness_self_test=pass"),0):(puts("vulkan_processing_ir_vulkan_offload_harness_self_test=fail"),1); }

int main(int argc,char **argv) {
    struct vk_state s; unsigned int batches[MAX_BATCHES],batch; int warmups,samples,batch_count,mode,i,j,rss,cpu_rss=0,gpu_rss=0,peak_rss=0,first_fast=-1; long long first_fast_communication=0;
    const char *raw_path,*provenance_path,*source_hash,*source_path,*workload="dispatch_fill_u32_repeated_v1"; FILE *raw=NULL; uint32_t *out=NULL,*cpu_out=NULL;
    if (argc==2&&!strcmp(argv[1],"--self-test")) return self_test();
    if (argc==3&&!strcmp(argv[1],"--dump-spirv")) return dump_spirv(argv[2]);
    if (argc<8||argc>13) { emit_failure("invalid-argv"); return 2; }
    raw_path=argv[1]; provenance_path=argv[2]; if (!parse_int(argv[3],3,64,&warmups)||!parse_int(argv[4],5,64,&samples)) { emit_failure("invalid-sample-count"); return 2; }
    batch_count=argc-5; if (batch_count<3||batch_count>MAX_BATCHES) { emit_failure("invalid-batch-count"); return 2; }
    for (i=0;i<batch_count;i++) if (!parse_batch(argv[5+i],&batches[i])||(i&&batches[i]<=batches[i-1])) { emit_failure("invalid-batches"); return 2; }
    source_hash=getenv("VULKAN_PROCESSING_IR_SOURCE_SHA256"); source_path=getenv("VULKAN_PROCESSING_IR_SOURCE_PATH");
    if (!source_hash||strlen(source_hash)!=64||!source_path||!*source_path) { emit_failure("missing-source-provenance"); return 2; }
    raw=fopen(raw_path,"w"); if (!raw) { emit_failure("raw-log-open-failed"); return 2; } fprintf(raw,"# batch mode sample cpu_us upload_us device_us readback_us transfer_us total_us mismatch_count\n");
    memset(&s,0,sizeof(s)); cpu_rss=read_rss("VmRSS"); if (!init_state(&s,batches[batch_count-1])) { fclose(raw); close_state(&s); emit_failure("physical-vulkan-device-unavailable"); return 3; }
    for (i=0;i<batch_count;i++) {
        batch=batches[i]; s.active_bytes=(VkDeviceSize)batch*4;
        if (!i) {
            printf("processing_ir_vulkan_offload_status=pass\nprocessing_ir_vulkan_offload_reason=measured-vulkan-compute-dispatch\nprocessing_ir_vulkan_offload_schema=processing-ir-offload-v1\nprocessing_ir_vulkan_offload_execution=processing_ir\nprocessing_ir_vulkan_offload_backend=vulkan\nprocessing_ir_vulkan_offload_evidence_kind=live\nprocessing_ir_vulkan_offload_cpu_workload_id=%s\nprocessing_ir_vulkan_offload_gpu_workload_id=%s\nprocessing_ir_vulkan_offload_aggregate=median\nprocessing_ir_vulkan_offload_timing_unit=us\nprocessing_ir_vulkan_offload_warmup_samples=%d\nprocessing_ir_vulkan_offload_measured_samples=%d\nprocessing_ir_vulkan_offload_row_count=%d\nprocessing_ir_vulkan_offload_physical_device_admitted=true\nprocessing_ir_vulkan_offload_cpu_fallback=false\nprocessing_ir_vulkan_offload_software_fallback=false\nprocessing_ir_vulkan_offload_device_type=physical\nprocessing_ir_vulkan_offload_device_type_code=%u\nprocessing_ir_vulkan_offload_device_identity=%llu\nprocessing_ir_vulkan_offload_readback_source=device_readback\nprocessing_ir_vulkan_offload_readback_exact=true\nprocessing_ir_vulkan_offload_mismatch_count=0\nprocessing_ir_vulkan_offload_device_name=%s\nprocessing_ir_vulkan_offload_vendor_id=%u\nprocessing_ir_vulkan_offload_device_id=%u\nprocessing_ir_vulkan_offload_api_version=%u\nprocessing_ir_vulkan_offload_driver_version=%u\nprocessing_ir_vulkan_offload_queue_family=%u\nprocessing_ir_vulkan_offload_driver_properties_available=%s\nprocessing_ir_vulkan_offload_driver_id=%u\nprocessing_ir_vulkan_offload_driver_name=%s\nprocessing_ir_vulkan_offload_source_path=%s\nprocessing_ir_vulkan_offload_source_sha256=%s\nprocessing_ir_vulkan_offload_raw_samples=%s\nprocessing_ir_vulkan_offload_provenance_env=%s\n",workload,workload,warmups,samples,batch_count*2,s.properties.deviceType,(unsigned long long)(((uint64_t)s.properties.vendorID<<32)|s.properties.deviceID),s.properties.deviceName,s.properties.vendorID,s.properties.deviceID,s.properties.apiVersion,s.properties.driverVersion,s.queue_family,s.driver_properties_available?"true":"false",s.driver.driverID,s.driver.driverName,source_path,source_hash,raw_path,provenance_path);
            write_provenance(provenance_path,&s,source_hash,source_path,workload);
        }
        out=malloc((size_t)batch*4); cpu_out=malloc((size_t)batch*4); if (!out||!cpu_out) { free(out); free(cpu_out); fclose(raw); close_state(&s); emit_failure("host-allocation-failed"); return 3; }
        for (mode=0;mode<2;mode++) {
            struct sample values[64]; long long cm,um,dm,rm,tm,totalm,mm; int commands=mode?COMMANDS_PER_ROW:1;
            for (j=0;j<warmups;j++) { cpu_fill(cpu_out,batch); if (!run_gpu(&s,batch,commands,out,NULL)||mismatch(out,batch)) { free(out); free(cpu_out); fclose(raw); close_state(&s); emit_failure("warmup-device-readback-failed"); return 3; } }
            rss=read_rss("VmRSS"); if (rss>gpu_rss) gpu_rss=rss;
            for (j=0;j<samples;j++) { long long a=now_ns(),b; cpu_fill(cpu_out,batch); b=now_ns(); values[j].cpu_us=elapsed_us(a,b); if (values[j].cpu_us<1||!run_gpu(&s,batch,commands,out,&values[j])||memcmp(cpu_out,out,(size_t)batch*4)) { free(out); free(cpu_out); fclose(raw); close_state(&s); emit_failure("measured-device-readback-failed"); return 3; } fprintf(raw,"%u %s %d %lld %lld %lld %lld %lld %lld %lld\n",batch,mode?"per_command":"batched",j,values[j].cpu_us,values[j].upload_us,values[j].device_us,values[j].readback_us,values[j].transfer_us,values[j].total_us,values[j].mismatch); }
            cm=median(values,samples,0); um=median(values,samples,1); dm=median(values,samples,2); rm=median(values,samples,3); tm=median(values,samples,4); totalm=median(values,samples,5); mm=median(values,samples,6);
            { int row=i*2+mode; unsigned int groups=0,c; for (c=0;c<(unsigned int)commands;c++) { unsigned int base=(batch*c)/(unsigned int)commands, n=(batch*(c+1u))/(unsigned int)commands-base; groups+=(n+LOCAL_SIZE-1)/LOCAL_SIZE; }
              printf("processing_ir_vulkan_offload_row_%d_batch=%u\nprocessing_ir_vulkan_offload_row_%d_workload_id=%s\nprocessing_ir_vulkan_offload_row_%d_cpu_us=%lld\nprocessing_ir_vulkan_offload_row_%d_upload_us=%lld\nprocessing_ir_vulkan_offload_row_%d_device_us=%lld\nprocessing_ir_vulkan_offload_row_%d_readback_us=%lld\nprocessing_ir_vulkan_offload_row_%d_transfer_us=%lld\nprocessing_ir_vulkan_offload_row_%d_total_us=%lld\nprocessing_ir_vulkan_offload_row_%d_upload_bytes=%llu\nprocessing_ir_vulkan_offload_row_%d_readback_bytes=%llu\nprocessing_ir_vulkan_offload_row_%d_command_count=%d\nprocessing_ir_vulkan_offload_row_%d_dispatch_count=%d\nprocessing_ir_vulkan_offload_row_%d_workgroup_count=%u\nprocessing_ir_vulkan_offload_row_%d_submission_mode=%s\nprocessing_ir_vulkan_offload_row_%d_readback_source=device_readback\nprocessing_ir_vulkan_offload_row_%d_readback_exact=true\nprocessing_ir_vulkan_offload_row_%d_readback_mismatch_count=%lld\nprocessing_ir_vulkan_offload_row_%d_decision=%s\n",row,batch,row,workload,row,cm,row,um,row,dm,row,rm,row,tm,row,totalm,row,(unsigned long long)s.active_bytes,row,(unsigned long long)s.active_bytes,row,commands,row,commands*FILL_REPETITIONS,row,groups*FILL_REPETITIONS,row,mode?"per_command":"batched",row,row,row,mm,row,totalm<cm?"gpu":"cpu");
              if (totalm<cm&&first_fast<0) { first_fast=row; first_fast_communication=um+rm; }
            }
        }
        free(out); free(cpu_out); out=NULL; cpu_out=NULL; rss=read_rss("VmHWM"); if (rss>peak_rss) peak_rss=rss;
    }
    fclose(raw); close_state(&s);
    printf("processing_ir_vulkan_offload_cpu_rss_kb=%d\nprocessing_ir_vulkan_offload_gpu_rss_kb=%d\nprocessing_ir_vulkan_offload_peak_rss_kb=%d\nprocessing_ir_vulkan_offload_communication_overhead_us=%lld\nprocessing_ir_vulkan_offload_break_even_batch=%u\n",cpu_rss,gpu_rss,peak_rss,first_fast_communication,first_fast>=0?batches[first_fast/2]:0);
    if (first_fast<0) { emit_failure("no-measured-break-even"); return 4; } return 0;
}
