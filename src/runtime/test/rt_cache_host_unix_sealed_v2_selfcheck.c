/* Prepared Unix ABI regression; runtime execution UNRUN in this Windows session. */
#define _GNU_SOURCE
static int probe_fsync(int fd);
#define fsync probe_fsync
#include "../runtime_cache_host_authority_v1.c"
#undef fsync
extern int fsync(int);
static int fail_at,flush_calls;
static int probe_fsync(int fd){if(fail_at&&++flush_calls==fail_at){errno=EIO;return -1;}return fsync(fd);}
static int checks;
#define CHECK(x) do{++checks;if(!(x)){fprintf(stderr,"FAIL%d %s errno%d\n",__LINE__,#x,errno);return 1;}}while(0)
int main(void){char dir[]="/tmp/simple-retained-XXXXXX";CHECK(mkdtemp(dir));int64_t r=rt_cache_host_open_root_v1((uint8_t*)dir,strlen(dir));CHECK(r>0);
int64_t t=rt_cache_host_secure_temp_v1(r);CHECK(t>0);CHECK(rt_cache_host_write_temp_v1(t,0,(uint8_t*)"original",8)==8);int fd=find_cap(t)->fd;struct stat original;CHECK(!fstat(fd,&original));int64_t s=rt_cache_host_publish_retained_noreplace_v2(t,(uint8_t*)"object",6);CHECK(s>0&&s!=t);CHECK(find_cap(s)->fd==fd);struct stat published;CHECK(!fstatat(find_cap(r)->fd,"object",&published,AT_SYMLINK_NOFOLLOW));CHECK(original.st_dev==published.st_dev&&original.st_ino==published.st_ino);CHECK(rt_cache_host_write_temp_v1(s,0,(uint8_t*)"x",1)<0);CHECK(rt_cache_host_close_v1(t)<0);CHECK(rt_cache_host_size_v1(s,8)==8);CHECK(rt_cache_host_size_v1(s,7)<0);uint8_t out[8];CHECK(rt_cache_host_pread_receipt_v1(s,0,out,8)==8&&!memcmp(out,"original",8));CHECK(rt_cache_host_fsync_v1(s)==1);CHECK(rt_cache_host_fsync_v1(r)==1);
int64_t c=rt_cache_host_secure_temp_v1(r);CHECK(c>0);CHECK(rt_cache_host_write_temp_v1(c,0,(uint8_t*)"other",5)==5);CHECK(rt_cache_host_publish_retained_noreplace_v2(c,(uint8_t*)"object",6)==0);CHECK(rt_cache_host_write_temp_v1(c,0,(uint8_t*)"x",1)<0);CHECK(rt_cache_host_close_v1(c)==0);
CHECK(rt_cache_host_close_v1(s)==0);CHECK(rt_cache_host_close_v1(s)<0);CHECK(!fstatat(find_cap(r)->fd,"object",&published,AT_SYMLINK_NOFOLLOW));
t=rt_cache_host_secure_temp_v1(r);CHECK(t>0);CHECK(rt_cache_host_write_temp_v1(t,0,(uint8_t*)"real",4)==4);struct cache_cap *cap=find_cap(t);CHECK(!unlinkat(cap->parent_fd,cap->temp_name,0));int swapped=openat(cap->parent_fd,cap->temp_name,O_WRONLY|O_CREAT|O_EXCL,0600);CHECK(swapped>=0);CHECK(write(swapped,"swap",4)==4);CHECK(!close(swapped));CHECK(rt_cache_host_publish_retained_noreplace_v2(t,(uint8_t*)"swapped",7)<0);CHECK(rt_cache_host_close_v1(t)<0);CHECK(!fstatat(find_cap(r)->fd,"swapped",&published,AT_SYMLINK_NOFOLLOW));
t=rt_cache_host_secure_temp_v1(r);CHECK(t>0);CHECK(rt_cache_host_write_temp_v1(t,0,(uint8_t*)"real",4)==4);fail_at=2;flush_calls=0;CHECK(rt_cache_host_publish_retained_noreplace_v2(t,(uint8_t*)"flushfail",9)<0);fail_at=0;CHECK(rt_cache_host_close_v1(t)<0);CHECK(!fstatat(find_cap(r)->fd,"flushfail",&published,AT_SYMLINK_NOFOLLOW));CHECK(rt_cache_host_close_v1(r)==0);printf("PASS %d actual C Unix ABI checks; fixture=%s\n",checks,dir);return 0;}
