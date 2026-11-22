// Headless RenderDoc REPLAY of a .rdc: count the actions it holds and dump the
// post-replay contents of every buffer of a given byte length.
//
// Why a replay and not `renderdoccmd convert -c zip.xml`: the converted capture
// holds only what the application WROTE (initial contents and coherent mapped
// memory writes serialised before vkQueueSubmit). What the GPU wrote -- for
// Simple's compute-only Engine2D, the framebuffer storage buffer -- exists only
// after the capture is replayed. Used by
// scripts/check/check-simple-renderdoc-capture.shs.
//
// Usage: renderdoc-replay-buffer-dump <capture.rdc> <byte_length> <out_dir>
//        renderdoc-replay-buffer-dump --compare <buffer.bin> <reference.ppm>
// Stdout is key=value. Exit 0 only when the capture replayed; a dump of zero
// buffers is still exit 0 and is the caller's to reject (replay_buffers=0).
#include <cstdio>
#include <cstdlib>
#include <string>

#include "api/replay/renderdoc_replay.h"

REPLAY_PROGRAM_MARKER()

struct Counts
{
  uint32_t actions = 0, draws = 0, dispatches = 0, clears = 0, last_event = 0;
};

static void walk(const rdcarray<ActionDescription> &actions, Counts &c)
{
  for(const ActionDescription &a : actions)
  {
    c.actions++;
    if(a.flags & ActionFlags::Drawcall)
      c.draws++;
    if(a.flags & ActionFlags::Dispatch)
      c.dispatches++;
    if(a.flags & ActionFlags::Clear)
      c.clears++;
    if(a.eventId > c.last_event)
      c.last_event = a.eventId;
    walk(a.children, c);
  }
}

// Compare a dumped framebuffer buffer with a binary P6 PPM, tolerance 0.
// Engine2D pixels are u32 0xAARRGGBB, little-endian in the buffer: B,G,R,A.
// Alpha is not in a PPM and is not compared.
static int compare(const char *buf_path, const char *ppm_path)
{
  FILE *b = fopen(buf_path, "rb");
  FILE *p = fopen(ppm_path, "rb");
  unsigned w = 0, h = 0, maxv = 0;
  if(b == nullptr || p == nullptr || fscanf(p, "P6 %u %u %u", &w, &h, &maxv) != 3 || maxv != 255 ||
     w == 0 || h == 0)
  {
    printf("compare_status=unreadable\n");
    return 2;
  }
  fgetc(p);    // the single whitespace byte after maxval
  uint64_t pixels = (uint64_t)w * h, mismatches = 0, first = 0;
  for(uint64_t i = 0; i < pixels; i++)
  {
    unsigned char px[4], rgb[3];
    if(fread(px, 1, 4, b) != 4 || fread(rgb, 1, 3, p) != 3)
    {
      printf("compare_status=short-read\ncompare_pixel=%llu\n", (unsigned long long)i);
      return 2;
    }
    if(px[2] != rgb[0] || px[1] != rgb[1] || px[0] != rgb[2])
    {
      if(mismatches == 0)
        first = i;
      mismatches++;
    }
  }
  bool trailing = fgetc(b) != EOF || fgetc(p) != EOF;
  fclose(b);
  fclose(p);
  if(trailing)
  {
    printf("compare_status=size-mismatch\n");
    return 2;
  }
  printf("compare_size=%ux%u\ncompare_pixels=%llu\ncompare_mismatch_pixels=%llu\n", w, h,
         (unsigned long long)pixels, (unsigned long long)mismatches);
  if(mismatches != 0)
    printf("compare_first_mismatch=%llu,%llu\n", (unsigned long long)(first % w),
           (unsigned long long)(first / w));
  printf("compare_status=%s\n", mismatches == 0 ? "equal" : "differ");
  return mismatches == 0 ? 0 : 1;
}

int main(int argc, char **argv)
{
  if(argc == 4 && std::string(argv[1]) == "--compare")
    return compare(argv[2], argv[3]);
  if(argc != 4)
  {
    fprintf(stderr, "usage: %s <capture.rdc> <byte_length> <out_dir>\n       %s --compare <buffer.bin> <reference.ppm>\n", argv[0], argv[0]);
    return 2;
  }
  const char *path = argv[1];
  uint64_t want = strtoull(argv[2], nullptr, 10);
  std::string out_dir = argv[3];

  RENDERDOC_InitialiseReplay(GlobalEnvironment(), {});
  ICaptureFile *cap = RENDERDOC_OpenCaptureFile();
  ResultDetails opened = cap->OpenFile(path, "", nullptr);
  if(!opened.OK())
  {
    printf("replay_status=open-failed\nreplay_reason=result-code-%u\n", (uint32_t)opened.code);
    cap->Shutdown();
    RENDERDOC_ShutdownReplay();
    return 1;
  }
  printf("replay_driver=%s\n", cap->DriverName().c_str());
  rdcpair<ResultDetails, IReplayController *> ctl = cap->OpenCapture(ReplayOptions(), nullptr);
  if(!ctl.first.OK() || ctl.second == nullptr)
  {
    printf("replay_status=replay-failed\nreplay_reason=result-code-%u\n", (uint32_t)ctl.first.code);
    cap->Shutdown();
    RENDERDOC_ShutdownReplay();
    return 1;
  }
  IReplayController *r = ctl.second;

  Counts c;
  walk(r->GetRootActions(), c);
  printf("replay_actions=%u\nreplay_draws=%u\nreplay_dispatches=%u\nreplay_clears=%u\n"
         "replay_last_event=%u\n",
         c.actions, c.draws, c.dispatches, c.clears, c.last_event);

  // Force the whole frame so buffers hold what the GPU left in them.
  r->SetFrameEvent(c.last_event, true);

  uint32_t dumped = 0;
  rdcarray<BufferDescription> buffers = r->GetBuffers();
  for(const BufferDescription &b : buffers)
  {
    if(b.length != want)
      continue;
    bytebuf data = r->GetBufferData(b.resourceId, 0, 0);
    std::string file = out_dir + "/buffer-" + std::to_string(dumped) + ".bin";
    FILE *f = fopen(file.c_str(), "wb");
    if(f == nullptr)
    {
      printf("replay_status=write-failed\nreplay_reason=%s\n", file.c_str());
      r->Shutdown();
      cap->Shutdown();
      RENDERDOC_ShutdownReplay();
      return 1;
    }
    size_t wrote = fwrite(data.data(), 1, data.size(), f);
    fclose(f);
    printf("replay_buffer_%u=%s\nreplay_buffer_%u_bytes=%zu\n", dumped, file.c_str(), dumped, wrote);
    dumped++;
  }
  printf("replay_buffers_total=%d\nreplay_buffers=%u\nreplay_status=pass\n", buffers.count(), dumped);

  r->Shutdown();
  cap->Shutdown();
  RENDERDOC_ShutdownReplay();
  return 0;
}
