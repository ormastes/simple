#ifndef _WIN32
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#if defined(__linux__)
int rt_cache_host_duplicate_root_fd_internal_v1(int64_t);
enum receipt_kind { R_PEER=1, R_LOCK=2, R_BOOT=3 };
struct receipt { int64_t token; enum receipt_kind kind; int root_fd, aux_fd; pid_t pid; uid_t uid; dev_t dev; ino_t ino; char boot[37]; struct receipt *next; };
static struct receipt *receipts;
static pthread_mutex_t receipt_mu=PTHREAD_MUTEX_INITIALIZER;
static int64_t random_token(void){uint64_t v=0;int fd=open("/dev/urandom",O_RDONLY|O_CLOEXEC|O_NOFOLLOW);if(fd<0||read(fd,&v,8)!=8){if(fd>=0)close(fd);return-1;}close(fd);v&=INT64_MAX;return v?(int64_t)v:1;}
static struct receipt *find_receipt(int64_t h){struct receipt*r;for(r=receipts;r;r=r->next)if(r->token==h)return r;return NULL;}
static int64_t add_receipt(struct receipt*r){pthread_mutex_lock(&receipt_mu);do r->token=random_token();while(r->token>0&&find_receipt(r->token));if(r->token>0){r->next=receipts;receipts=r;}pthread_mutex_unlock(&receipt_mu);return r->token;}
static int read_boot(char out[37]){int fd=open("/proc/sys/kernel/random/boot_id",O_RDONLY|O_CLOEXEC|O_NOFOLLOW);if(fd<0)return 0;ssize_t n=read(fd,out,36);close(fd);if(n!=36)return 0;out[36]=0;for(int i=0;i<36;i++)if(!((out[i]>='0'&&out[i]<='9')||(out[i]>='a'&&out[i]<='f')||out[i]=='-'))return 0;return 1;}
static int write_all_at(int fd,const void*p,size_t n){size_t o=0;while(o<n){ssize_t w=pwrite(fd,(const uint8_t*)p+o,n-o,(off_t)o);if(w<=0)return 0;o+=(size_t)w;}return ftruncate(fd,(off_t)n)==0&&fsync(fd)==0;}
struct epoch_record { char magic[8]; uint64_t epoch; char boot[37]; uint8_t reserved[11]; };
struct ready_record { char magic[8]; uint64_t token,epoch; uint32_t uid,pid,nonce_len; char boot[37]; uint8_t nonce[256]; };
int64_t rt_cache_host_authenticate_peer_v1(int64_t root,int64_t peer){int rfd=rt_cache_host_duplicate_root_fd_internal_v1(root);if(rfd<0||peer<0){if(rfd>=0)close(rfd);return-1;}struct ucred c;socklen_t n=sizeof c;if(getsockopt((int)peer,SOL_SOCKET,SO_PEERCRED,&c,&n)||n!=sizeof c||c.uid!=geteuid()){close(rfd);return-1;}struct stat s;if(fstat(rfd,&s)||!S_ISDIR(s.st_mode)){close(rfd);return-1;}int pfd=fcntl((int)peer,F_DUPFD_CLOEXEC,3);if(pfd<0){close(rfd);return-1;}struct receipt*r=calloc(1,sizeof*r);if(!r){close(rfd);close(pfd);return-1;}r->kind=R_PEER;r->root_fd=rfd;r->aux_fd=pfd;r->pid=c.pid;r->uid=c.uid;r->dev=s.st_dev;r->ino=s.st_ino;return add_receipt(r);}
int64_t rt_cache_host_acquire_exclusive_lock_v1(int64_t root,int64_t peer){int rfd=rt_cache_host_duplicate_root_fd_internal_v1(root);if(rfd<0)return-1;struct stat s;if(fstat(rfd,&s)){close(rfd);return-1;}pthread_mutex_lock(&receipt_mu);struct receipt*p=find_receipt(peer);int ok=p&&p->kind==R_PEER&&p->dev==s.st_dev&&p->ino==s.st_ino;pid_t pid=ok?p->pid:0;uid_t uid=ok?p->uid:0;pthread_mutex_unlock(&receipt_mu);if(!ok){close(rfd);return-1;}int lfd=openat(rfd,".simple-cache-writer.lock",O_RDWR|O_CREAT|O_NOFOLLOW|O_CLOEXEC,0600);if(lfd<0||flock(lfd,LOCK_EX|LOCK_NB)){if(lfd>=0)close(lfd);close(rfd);return-1;}struct receipt*r=calloc(1,sizeof*r);if(!r){close(lfd);close(rfd);return-1;}r->kind=R_LOCK;r->root_fd=rfd;r->aux_fd=lfd;r->pid=pid;r->uid=uid;r->dev=s.st_dev;r->ino=s.st_ino;return add_receipt(r);}
int64_t rt_cache_host_boot_identity_v1(int64_t lock){char boot[37];if(!read_boot(boot))return-1;pthread_mutex_lock(&receipt_mu);struct receipt*l=find_receipt(lock);int ok=l&&l->kind==R_LOCK;pthread_mutex_unlock(&receipt_mu);if(!ok)return-1;struct receipt*r=calloc(1,sizeof*r);if(!r)return-1;r->kind=R_BOOT;r->aux_fd=(int)lock;memcpy(r->boot,boot,37);return add_receipt(r);}
int64_t rt_cache_host_advance_writer_epoch_v1(int64_t lock,int64_t boot){char current[37];if(!read_boot(current))return-1;pthread_mutex_lock(&receipt_mu);struct receipt*l=find_receipt(lock),*b=find_receipt(boot);int rfd=l&&l->kind==R_LOCK&&b&&b->kind==R_BOOT&&b->aux_fd==(int)lock&&!memcmp(b->boot,current,37)?fcntl(l->root_fd,F_DUPFD_CLOEXEC,3):-1;pthread_mutex_unlock(&receipt_mu);if(rfd<0)return-1;int fd=openat(rfd,".simple-cache-writer.epoch",O_RDWR|O_CREAT|O_NOFOLLOW|O_CLOEXEC,0600);struct stat s;struct epoch_record rec={{0}};uint64_t prev=0;if(fd<0||fstat(fd,&s)||!S_ISREG(s.st_mode)||s.st_nlink!=1){if(fd>=0)close(fd);close(rfd);return-1;}if(s.st_size==(off_t)sizeof rec){if(pread(fd,&rec,sizeof rec,0)!=(ssize_t)sizeof rec||memcmp(rec.magic,"SCEPOC1",7)){close(fd);close(rfd);return-1;}prev=rec.epoch;}else if(s.st_size!=0){close(fd);close(rfd);return-1;}if(prev==INT64_MAX){close(fd);close(rfd);return-1;}memset(&rec,0,sizeof rec);memcpy(rec.magic,"SCEPOC1",7);rec.epoch=prev+1;memcpy(rec.boot,current,37);int ok=write_all_at(fd,&rec,sizeof rec)&&fsync(rfd)==0;close(fd);close(rfd);return ok?(int64_t)rec.epoch:-1;}
int64_t rt_cache_host_publish_readiness_v1(int64_t lock,int64_t epoch,const uint8_t*nonce,int64_t len){if(!nonce||len<16||len>256||epoch<=0)return-1;pthread_mutex_lock(&receipt_mu);struct receipt*l=find_receipt(lock);int rfd=l&&l->kind==R_LOCK?fcntl(l->root_fd,F_DUPFD_CLOEXEC,3):-1;pid_t pid=l?l->pid:0;uid_t uid=l?l->uid:0;pthread_mutex_unlock(&receipt_mu);if(rfd<0)return-1;int64_t token=random_token();char boot[37],tmp[96];if(token<0||!read_boot(boot)){close(rfd);return-1;}snprintf(tmp,sizeof tmp,".simple-cache-ready.%lld.tmp",(long long)token);int fd=openat(rfd,tmp,O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600);if(fd<0){close(rfd);return-1;}struct ready_record rec={{0}};memcpy(rec.magic,"SCREADY1",8);rec.token=(uint64_t)token;rec.epoch=(uint64_t)epoch;rec.uid=uid;rec.pid=(uint32_t)pid;rec.nonce_len=(uint32_t)len;memcpy(rec.boot,boot,37);memcpy(rec.nonce,nonce,(size_t)len);int ok=write_all_at(fd,&rec,sizeof rec);close(fd);if(ok)ok=renameat(rfd,tmp,rfd,".simple-cache-ready")==0&&fsync(rfd)==0;if(!ok)unlinkat(rfd,tmp,0);close(rfd);return ok?token:-1;}
int64_t rt_cache_host_validate_readiness_v1(int64_t peer,int64_t ready,const uint8_t*nonce,int64_t len,int64_t epoch){if(!nonce||len<16||len>256||ready<=0||epoch<=0)return-1;pthread_mutex_lock(&receipt_mu);struct receipt*p=find_receipt(peer);int rfd=p&&p->kind==R_PEER?fcntl(p->root_fd,F_DUPFD_CLOEXEC,3):-1;pid_t pid=p?p->pid:0;uid_t uid=p?p->uid:0;pthread_mutex_unlock(&receipt_mu);if(rfd<0)return-1;int fd=openat(rfd,".simple-cache-ready",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);close(rfd);struct ready_record rec;struct stat s;if(fd<0||fstat(fd,&s)||!S_ISREG(s.st_mode)||s.st_nlink!=1||s.st_size!=(off_t)sizeof rec||pread(fd,&rec,sizeof rec,0)!=(ssize_t)sizeof rec){if(fd>=0)close(fd);return-1;}close(fd);char boot[37];if(!read_boot(boot))return-1;return !memcmp(rec.magic,"SCREADY1",8)&&rec.token==(uint64_t)ready&&rec.epoch==(uint64_t)epoch&&rec.uid==uid&&rec.pid==(uint32_t)pid&&rec.nonce_len==(uint32_t)len&&!memcmp(rec.boot,boot,37)&&!memcmp(rec.nonce,nonce,(size_t)len)?1:-1;}
int64_t rt_cache_host_release_daemon_receipt_v1(int64_t h){pthread_mutex_lock(&receipt_mu);struct receipt**slot=&receipts,*r=NULL;while(*slot){if((*slot)->token==h){r=*slot;*slot=r->next;break;}slot=&(*slot)->next;}pthread_mutex_unlock(&receipt_mu);if(!r)return-1;if(r->kind==R_PEER){close(r->aux_fd);close(r->root_fd);}else if(r->kind==R_LOCK){unlinkat(r->root_fd,".simple-cache-ready",0);fsync(r->root_fd);flock(r->aux_fd,LOCK_UN);close(r->aux_fd);close(r->root_fd);}free(r);return 0;}
#else
#define FAIL(name,args) int64_t name args{return -1;}
FAIL(rt_cache_host_authenticate_peer_v1,(int64_t r,int64_t p)) FAIL(rt_cache_host_acquire_exclusive_lock_v1,(int64_t r,int64_t p)) FAIL(rt_cache_host_boot_identity_v1,(int64_t l)) FAIL(rt_cache_host_advance_writer_epoch_v1,(int64_t l,int64_t b)) FAIL(rt_cache_host_publish_readiness_v1,(int64_t l,int64_t e,const uint8_t*n,int64_t z)) FAIL(rt_cache_host_validate_readiness_v1,(int64_t p,int64_t r,const uint8_t*n,int64_t z,int64_t e)) FAIL(rt_cache_host_release_daemon_receipt_v1,(int64_t h))
#endif
#else
#include <stdint.h>
#define FAIL(name,args) int64_t name args{return -1;}
FAIL(rt_cache_host_authenticate_peer_v1,(int64_t r,int64_t p)) FAIL(rt_cache_host_acquire_exclusive_lock_v1,(int64_t r,int64_t p)) FAIL(rt_cache_host_boot_identity_v1,(int64_t l)) FAIL(rt_cache_host_advance_writer_epoch_v1,(int64_t l,int64_t b)) FAIL(rt_cache_host_publish_readiness_v1,(int64_t l,int64_t e,const uint8_t*n,int64_t z)) FAIL(rt_cache_host_validate_readiness_v1,(int64_t p,int64_t r,const uint8_t*n,int64_t z,int64_t e)) FAIL(rt_cache_host_release_daemon_receipt_v1,(int64_t h))
#endif
