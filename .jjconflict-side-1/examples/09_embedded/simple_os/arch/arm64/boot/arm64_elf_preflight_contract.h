#ifndef SIMPLEOS_ARM64_ELF_PREFLIGHT_CONTRACT_H
#define SIMPLEOS_ARM64_ELF_PREFLIGHT_CONTRACT_H
#include <stddef.h>
#include <stdint.h>
enum arm64_elf_preflight_reason_v1 {
 ARM64_ELF_OK=0, ARM64_ELF_SHORT=1, ARM64_ELF_MAGIC=2, ARM64_ELF_CLASS=3,
 ARM64_ELF_DATA=4, ARM64_ELF_MACHINE=5, ARM64_ELF_EHSIZE=6,
 ARM64_ELF_PHENTSIZE=7, ARM64_ELF_PHOFF=8, ARM64_ELF_PHNUM=9,
 ARM64_ELF_PHBOUNDS=10, ARM64_ELF_NO_LOAD=11, ARM64_ELF_FILE_GT_MEM=12,
 ARM64_ELF_SOURCE_BOUNDS=13, ARM64_ELF_VA_OVERFLOW=14,
 ARM64_ELF_IMAGE_BOUNDS=15, ARM64_ELF_STAGE_COPY=16,
 ARM64_ELF_STDOUT_UNSET=17, ARM64_ELF_MAP_PAGE=18
};
static uint16_t arm64_ep_u16(const uint8_t *p){return (uint16_t)p[0]|((uint16_t)p[1]<<8);}
static uint64_t arm64_ep_u64(const uint8_t *p){uint64_t v=0;for(unsigned i=0;i<8;i++)v|=(uint64_t)p[i]<<(8*i);return v;}
static uint32_t arm64_elf_preflight_bytes(const uint8_t *b,size_t n){
 if(!b||n<64)return ARM64_ELF_SHORT;
 if(b[0]!=0x7f||b[1]!='E'||b[2]!='L'||b[3]!='F')return ARM64_ELF_MAGIC;
 if(b[4]!=2)return ARM64_ELF_CLASS;
 if(b[5]!=1)return ARM64_ELF_DATA;
 if(arm64_ep_u16(b+18)!=183)return ARM64_ELF_MACHINE;
 if(arm64_ep_u16(b+52)!=64)return ARM64_ELF_EHSIZE;
 if(arm64_ep_u16(b+54)!=56)return ARM64_ELF_PHENTSIZE;
 uint64_t off=arm64_ep_u64(b+32),num=arm64_ep_u16(b+56);
 if(off>n)return ARM64_ELF_PHOFF;
 if(num>256)return ARM64_ELF_PHNUM;
 if(num>(UINT64_MAX-off)/56||off+num*56>n)return ARM64_ELF_PHBOUNDS;
 unsigned loads=0;uint64_t lo=UINT64_MAX,hi=0;
 for(uint64_t i=0;i<num;i++){const uint8_t*p=b+off+i*56;
  uint32_t type=(uint32_t)arm64_ep_u16(p)|((uint32_t)arm64_ep_u16(p+2)<<16);
  if(type!=1)continue;
  loads++;
  uint64_t fo=arm64_ep_u64(p+8),va=arm64_ep_u64(p+16),fs=arm64_ep_u64(p+32),ms=arm64_ep_u64(p+40);
  if(fs>ms)return ARM64_ELF_FILE_GT_MEM;
  if(fo>n||fs>n-fo)return ARM64_ELF_SOURCE_BOUNDS;
  if(ms>UINT64_MAX-va)return ARM64_ELF_VA_OVERFLOW;
  if(va<lo)lo=va;
  if(va+ms>hi)hi=va+ms;}
 if(!loads)return ARM64_ELF_NO_LOAD;
 lo&=~4095ULL;
 if(hi<lo||hi-lo>0x006fe000ULL)return ARM64_ELF_IMAGE_BOUNDS;
 return ARM64_ELF_OK;
}
#endif
