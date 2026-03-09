#include <gtest/gtest.h>
#include <vector>
#include <cstdint>
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"

namespace {
struct SqFix {
  std::vector<std::uint8_t> ring; Queue q{}; std::uint32_t db{0};
  SqFix(std::uint16_t depth): ring(depth*64,0){ q.vaddr=ring.data(); q.entry_size=64; q.entries=depth; q.db=&db; q.phase=1; q.qid=1; }
};
struct CqFix {
  std::vector<std::uint8_t> ring; Queue q{}; std::uint32_t db{0};
  CqFix(std::uint16_t depth): ring(depth*16,0){ q.vaddr=ring.data(); q.entry_size=16; q.entries=depth; q.db=&db; q.phase=1; q.qid=1; }
};
constexpr std::size_t kPage=4096;
}

// ============================================================================
// READ Command Tests - DOORBELL_MMIO removed (GPU cannot access MMIO)
// ============================================================================

TEST(HostIO, Submit_Read_PRP1_MMIO) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0x1234,512,&b,kPage); // MMIO→DEFERRED
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(cmd->prp1,b.iova);
  EXPECT_EQ(cmd->prp2,0u);
  EXPECT_EQ(*sq.q.db,0u);  // Doorbell NOT rung (deferred)
}

TEST(HostIO, Submit_Read_PRP2_MMIO) {  // MMIO→DEFERRED (GPU cannot access MMIO)
  SqFix sq(8); DmaBuf b{}; b.bytes=2*kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,2*kPage);
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->prp1,b.iova);
  EXPECT_EQ(cmd->prp2,b.iova + kPage);  // Second page
}

TEST(HostIO, Submit_Read_PRPList_MMIO) {
  SqFix sq(8); DmaBuf b{}; b.bytes=3*kPage; b.iova=0x90000000ull; b.prplist_iova=0xA0000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,3*kPage); // MMIO→DEFERRED
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->prp2,b.prplist_iova);  // PRP list for >2 pages
}

// ============================================================================
// WRITE Command Tests - DOORBELL_MMIO removed (GPU cannot access MMIO)
// ============================================================================

TEST(HostIO, Submit_Write_PRP1_MMIO) {  // MMIO→DEFERRED (GPU cannot access MMIO)
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q,1,0x5678,512,&b,kPage);
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_WRITE);
  EXPECT_EQ(cmd->prp1,b.iova);
  EXPECT_EQ(*sq.q.db,0u);  // Doorbell NOT rung (deferred)
}

TEST(HostIO, Submit_Write_PRP2_MMIO) {  // MMIO→DEFERRED (GPU cannot access MMIO)
  SqFix sq(8); DmaBuf b{}; b.bytes=2*kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,2*kPage);
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->prp2,b.iova + kPage);
}

TEST(HostIO, Submit_Write_PRPList_MMIO) {
  SqFix sq(8); DmaBuf b{}; b.bytes=5*kPage; b.iova=0x90000000ull; b.prplist_iova=0xA0000000ull;
  auto cid=host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q,1,100,512,&b,5*kPage);  // MMIO→DEFERRED
  ASSERT_NE(cid, 0xFFFFu);
  auto* cmd=reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->prp2,b.prplist_iova);
}

// ============================================================================
// DOORBELL_DEFERRED Tests
// ============================================================================

TEST(HostIO, Submit_Read_Deferred) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,kPage);
  ASSERT_NE(cid, 0xFFFFu);
  EXPECT_EQ(*sq.q.db,0u);  // Doorbell NOT rung (deferred)
  EXPECT_EQ(sq.q.tail,1u);  // But tail updated
}

TEST(HostIO, Submit_Write_Deferred) {
  SqFix sq(8); DmaBuf b{}; b.bytes=2*kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,2*kPage);
  ASSERT_NE(cid, 0xFFFFu);
  EXPECT_EQ(*sq.q.db,0u);  // Doorbell NOT rung
}

// ============================================================================
// DOORBELL_DEFERRED_EVENTIDX Tests
// ============================================================================

TEST(HostIO, Submit_Read_DeferredEventIdx) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(&sq.q,1,0,512,&b,kPage);
  ASSERT_NE(cid, 0xFFFFu);
  EXPECT_EQ(*sq.q.db,0u);  // Doorbell NOT rung (deferred with event index)
}

TEST(HostIO, Submit_Write_DeferredEventIdx) {
  SqFix sq(8); DmaBuf b{}; b.bytes=3*kPage; b.iova=0x90000000ull; b.prplist_iova=0xA0000000ull;
  auto cid=host_submit<CMD_WRITE, DOORBELL_DEFERRED_EVENTIDX>(&sq.q,1,0,512,&b,3*kPage);
  ASSERT_NE(cid, 0xFFFFu);
  EXPECT_EQ(*sq.q.db,0u);
}

// ============================================================================
// Error Handling Tests
// ============================================================================

TEST(HostIO, Submit_NullQueue) {
  DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(nullptr,1,0,512,&b,kPage);  // Use DEFERRED (MMIO removed)
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_NullBuffer) {
  SqFix sq(8);
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,nullptr,kPage);  // Use DEFERRED (MMIO removed)
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_NullDoorbell) {
  SqFix sq(8); sq.q.db = nullptr;
  DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_MMIO>(&sq.q,1,0,512,&b,kPage);
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_NullVaddr) {
  SqFix sq(8); sq.q.vaddr = nullptr;
  DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,kPage);  // Use DEFERRED (MMIO removed)
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_ZeroLbaSize) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,0,&b,kPage);  // Use DEFERRED (MMIO removed)
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_ZeroBytes) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,0);  // Use DEFERRED (MMIO removed)
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_BytesExceedBuffer) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,2*kPage);  // Use DEFERRED (MMIO removed)  // Request 2 pages but buffer is 1
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_BytesNotAligned) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q,1,0,512,&b,513);  // Use DEFERRED (MMIO removed)  // Not multiple of lba_size
  EXPECT_EQ(cid, NVME_CID_ERROR);
}

TEST(HostIO, Submit_QueueFull) {
  SqFix sq(2);  // Only 2 entries
  sq.q.tail = 0;
  sq.q.head = 1;  // Queue is full when (tail+1) % entries == head
  DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit<CMD_READ, DOORBELL_MMIO>(&sq.q,1,0,512,&b,kPage);
  EXPECT_EQ(cid, NVME_CID_QUEUE_FULL);
}

// ============================================================================
// Polling Tests - ASYNC_TYPE_SYNC
// ============================================================================

TEST(HostIO, Poll_Sync_Success) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=7; cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);  // Success, phase=1
  std::uint16_t got=0;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q,&got);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(got,7u);
  EXPECT_EQ(*cq.q.db,1u);
  EXPECT_EQ(cq.q.head,1u);
}

TEST(HostIO, Poll_Sync_PhaseWrap) {
  CqFix cq(4);
  cq.q.head = 3;  // Near end of queue
  cq.q.phase = 1;
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data() + 3*16);
  cqe->cid=10;
  cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);

  std::uint16_t got=0;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q,&got);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(cq.q.head,0u);  // Wrapped around
  EXPECT_EQ(cq.q.phase,0u);  // Phase flipped
}

TEST(HostIO, Poll_Sync_Error) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=8;
  cqe->status_p=(std::uint16_t)((1<<9)|(0x02<<1)|1);  // Generic error, phase=1

  std::uint16_t got=0;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q,&got);
  EXPECT_TRUE(st.is_error());
  EXPECT_EQ(st.sct, 1);
  EXPECT_EQ(st.sc, 0x02);
}

TEST(HostIO, Poll_Sync_WithPollResult) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=9; cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);

  std::uint16_t got=0;
  PollResult result = POLL_ERROR;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q,&got,&result);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(result, POLL_READY);
}

TEST(HostIO, Poll_Sync_NullQueue) {
  std::uint16_t got=0;
  PollResult result = POLL_READY;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_SYNC>(nullptr,&got,&result);
  EXPECT_TRUE(st.is_error());
  EXPECT_EQ(result, POLL_ERROR);
}

// ============================================================================
// Polling Tests - ASYNC_TYPE_ASYNC
// ============================================================================

TEST(HostIO, Poll_Async_Ready) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=11; cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);

  std::uint16_t got=0;
  PollResult result = POLL_ERROR;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_ASYNC>(&cq.q,&got,&result);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(result, POLL_READY);
  EXPECT_EQ(got, 11u);
}

TEST(HostIO, Poll_Async_NotReady) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->status_p=0;  // Phase bit = 0, doesn't match queue phase (1)

  std::uint16_t got=99;
  PollResult result = POLL_READY;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_ASYNC>(&cq.q,&got,&result);
  EXPECT_EQ(result, POLL_NOT_READY);
  // Note: status may be invalid when POLL_NOT_READY
}

TEST(HostIO, Poll_Async_NullPollResult) {
  CqFix cq(4);
  std::uint16_t got=0;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_ASYNC>(&cq.q,&got,nullptr);
  EXPECT_TRUE(st.is_error());
}

TEST(HostIO, Poll_Async_NullQueue) {
  std::uint16_t got=0;
  PollResult result = POLL_READY;
  NvmeStatus st=host_poll_completion<ASYNC_TYPE_ASYNC>(nullptr,&got,&result);
  EXPECT_EQ(result, POLL_ERROR);
}

// ============================================================================
// Runtime API Tests
// ============================================================================

TEST(HostIO, Runtime_Submit_Read_MMIO) {  // MMIO→Immediate (runtime API defaults to immediate doorbell)
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  auto cid=host_submit_runtime(CMD_READ, nullptr, &sq.q,1,0,512,&b,kPage);
  ASSERT_NE(cid, NVME_CID_ERROR);
  EXPECT_EQ(*sq.q.db,1u);
}

TEST(HostIO, Runtime_Submit_Write_Deferred) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  DeferredDoorbell deferred_db;
  auto cid=host_submit_runtime(CMD_WRITE, &deferred_db, &sq.q,1,0,512,&b,kPage);
  ASSERT_NE(cid, NVME_CID_ERROR);
  EXPECT_EQ(*sq.q.db,0u);
}

TEST(HostIO, Runtime_Submit_InvalidDoorbell) {
  SqFix sq(8); DmaBuf b{}; b.bytes=kPage; b.iova=0x80000000ull;
  // Passing nullptr defaults to immediate doorbell (valid)
  auto cid=host_submit_runtime(CMD_READ, nullptr, &sq.q,1,0,512,&b,kPage);
  EXPECT_NE(cid, NVME_CID_ERROR);
}

TEST(HostIO, Runtime_Poll_Sync) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=12; cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);

  std::uint16_t got=0;
  PollResult result = POLL_ERROR;
  NvmeStatus st=host_poll_completion_runtime(ASYNC_TYPE_SYNC, &cq.q,&got,&result);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(result, POLL_READY);
}

TEST(HostIO, Runtime_Poll_Async) {
  CqFix cq(4); auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid=13; cqe->status_p=(std::uint16_t)((0<<9)|(0<<1)|1);

  std::uint16_t got=0;
  PollResult result = POLL_ERROR;
  NvmeStatus st=host_poll_completion_runtime(ASYNC_TYPE_ASYNC, &cq.q,&got,&result);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(result, POLL_READY);
}

TEST(HostIO, Runtime_Poll_InvalidAsyncType) {
  CqFix cq(4);
  std::uint16_t got=0;
  PollResult result = POLL_READY;
  NvmeStatus st=host_poll_completion_runtime(static_cast<AsyncType>(99), &cq.q,&got,&result);
  EXPECT_TRUE(st.is_error());
  EXPECT_EQ(result, POLL_ERROR);
}
