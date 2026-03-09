#include <gtest/gtest.h>
#include <vector>
#include <cstdint>
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"

namespace {
constexpr std::size_t kPage = 4096;

struct SqFix {
  std::vector<std::uint8_t> ring;
  Queue q{};
  std::uint32_t db{0};

  SqFix(std::uint16_t depth) : ring(depth * 64, 0) {
    q.vaddr = ring.data();
    q.entry_size = 64;
    q.entries = depth;
    q.db = &db;
    q.phase = 1;
    q.qid = 1;
  }
};

struct CqFix {
  std::vector<std::uint8_t> ring;
  Queue q{};
  std::uint32_t db{0};

  CqFix(std::uint16_t depth) : ring(depth * 16, 0) {
    q.vaddr = ring.data();
    q.entry_size = 16;
    q.entries = depth;
    q.db = &db;
    q.phase = 1;
    q.qid = 1;
  }
};

} // namespace

// ============================================================================
// Template Submit Tests - All Combinations
// ============================================================================

TEST(TemplateSubmit, READ_DOORBELL_MMIO) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0x80000000ull;

  auto cid = host_submit<CMD_READ, DOORBELL_MMIO>(&sq.q, 1, 0x1234, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 1u);  // Doorbell rung
}

TEST(TemplateSubmit, WRITE_DOORBELL_MMIO) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0x90000000ull;

  auto cid = host_submit<CMD_WRITE, DOORBELL_MMIO>(&sq.q, 1, 0x5678, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_WRITE);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 1u);  // Doorbell rung
}

TEST(TemplateSubmit, READ_DOORBELL_DEFERRED) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xA0000000ull;

  auto cid = host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q, 1, 0xABCD, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 0u);  // Doorbell NOT rung
}

TEST(TemplateSubmit, WRITE_DOORBELL_DEFERRED) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xB0000000ull;

  auto cid = host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q, 1, 0xDEAD, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_WRITE);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 0u);  // Doorbell NOT rung
}

TEST(TemplateSubmit, READ_DOORBELL_DEFERRED_EVENTIDX) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xC0000000ull;

  auto cid = host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(&sq.q, 1, 0xBEEF, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 0u);  // Doorbell NOT rung
}

TEST(TemplateSubmit, WRITE_DOORBELL_DEFERRED_EVENTIDX) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xD0000000ull;

  auto cid = host_submit<CMD_WRITE, DOORBELL_DEFERRED_EVENTIDX>(&sq.q, 1, 0xCAFE, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_WRITE);
  EXPECT_EQ(cmd->prp1, b.iova);
  EXPECT_EQ(*sq.q.db, 0u);  // Doorbell NOT rung
}

// ============================================================================
// Template Poll Tests - All Combinations
// ============================================================================

TEST(TemplatePoll, ASYNC_TYPE_SYNC_InfiniteWait) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 42;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 1);  // Success, phase=1

  std::uint16_t got = 0;
  NvmeStatus st = host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q, &got);

  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(got, 42u);
  EXPECT_EQ(*cq.q.db, 1u);
}

TEST(TemplatePoll, ASYNC_TYPE_SYNC_WithPollResult) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 99;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 1);

  std::uint16_t got = 0;
  PollResult result;
  NvmeStatus st = host_poll_completion<ASYNC_TYPE_SYNC>(&cq.q, &got, &result);

  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(result, POLL_READY);
  EXPECT_EQ(got, 99u);
}

TEST(TemplatePoll, ASYNC_TYPE_ASYNC_Ready) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 123;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 1);

  std::uint16_t got = 0;
  PollResult result;
  NvmeStatus st = host_poll_completion<ASYNC_TYPE_ASYNC>(&cq.q, &got, &result);

  EXPECT_EQ(result, POLL_READY);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(got, 123u);
}

TEST(TemplatePoll, ASYNC_TYPE_ASYNC_NotReady) {
  CqFix cq(4);
  // No completion entry ready (phase mismatch)
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 999;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 0);  // phase=0, queue phase=1

  std::uint16_t got = 0;
  PollResult result;
  NvmeStatus st = host_poll_completion<ASYNC_TYPE_ASYNC>(&cq.q, &got, &result);

  EXPECT_EQ(result, POLL_NOT_READY);
  // Status is invalid when not ready
}

// ============================================================================
// Runtime Dispatch Tests - All Combinations
// ============================================================================

TEST(RuntimeSubmit, READ_DOORBELL_MMIO) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0x80000000ull;

  // Use nullptr for immediate doorbell
  auto cid = host_submit_runtime(CMD_READ, nullptr, &sq.q, 1, 0x1234, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(*sq.q.db, 1u);
}

TEST(RuntimeSubmit, WRITE_DOORBELL_DEFERRED) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0x90000000ull;

  // Create a DeferredDoorbell instance
  DeferredDoorbell deferred_db;
  auto cid = host_submit_runtime(CMD_WRITE, &deferred_db, &sq.q, 1, 0x5678, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_WRITE);
  EXPECT_EQ(*sq.q.db, 0u);  // Not rung
}

TEST(RuntimeSubmit, READ_DOORBELL_DEFERRED_EVENTIDX) {
  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xA0000000ull;

  // Create an EventIndexedDoorbell instance
  EventIndexedDoorbell eventidx_db;
  auto cid = host_submit_runtime(CMD_READ, &eventidx_db, &sq.q, 1, 0xABCD, 512, &b, kPage);

  ASSERT_NE(cid, NVME_CID_ERROR);
  auto* cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(cmd->opc, OPC_NVM_READ);
  EXPECT_EQ(*sq.q.db, 0u);  // Not rung
}

TEST(RuntimePoll, ASYNC_TYPE_SYNC) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 77;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 1);

  std::uint16_t got = 0;
  PollResult result;
  NvmeStatus st = host_poll_completion_runtime(ASYNC_TYPE_SYNC, &cq.q, &got, &result, 0);

  EXPECT_EQ(result, POLL_READY);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(got, 77u);
}

TEST(RuntimePoll, ASYNC_TYPE_ASYNC) {
  CqFix cq(4);
  auto* cqe = reinterpret_cast<NvmeCqe*>(cq.ring.data());
  cqe->cid = 88;
  cqe->status_p = (std::uint16_t)((0 << 9) | (0 << 1) | 1);

  std::uint16_t got = 0;
  PollResult result;
  NvmeStatus st = host_poll_completion_runtime(ASYNC_TYPE_ASYNC, &cq.q, &got, &result, 0);

  EXPECT_EQ(result, POLL_READY);
  EXPECT_FALSE(st.is_error());
  EXPECT_EQ(got, 88u);
}

// ============================================================================
// Exhaustive Combination Tests
// ============================================================================

// Test all 6 submit combinations via templates
class SubmitTemplateTest : public ::testing::TestWithParam<
    std::tuple<CommandType, DoorbellType>> {};

TEST_P(SubmitTemplateTest, AllCombinations) {
  auto [cmd, doorbell] = GetParam();

  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xF0000000ull;

  std::uint16_t cid;

  // Call appropriate template
  if (cmd == CMD_READ && doorbell == DOORBELL_MMIO) {
    cid = host_submit<CMD_READ, DOORBELL_MMIO>(&sq.q, 1, 0, 512, &b, kPage);
  } else if (cmd == CMD_READ && doorbell == DOORBELL_DEFERRED) {
    cid = host_submit<CMD_READ, DOORBELL_DEFERRED>(&sq.q, 1, 0, 512, &b, kPage);
  } else if (cmd == CMD_READ && doorbell == DOORBELL_DEFERRED_EVENTIDX) {
    cid = host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(&sq.q, 1, 0, 512, &b, kPage);
  } else if (cmd == CMD_WRITE && doorbell == DOORBELL_MMIO) {
    cid = host_submit<CMD_WRITE, DOORBELL_MMIO>(&sq.q, 1, 0, 512, &b, kPage);
  } else if (cmd == CMD_WRITE && doorbell == DOORBELL_DEFERRED) {
    cid = host_submit<CMD_WRITE, DOORBELL_DEFERRED>(&sq.q, 1, 0, 512, &b, kPage);
  } else if (cmd == CMD_WRITE && doorbell == DOORBELL_DEFERRED_EVENTIDX) {
    cid = host_submit<CMD_WRITE, DOORBELL_DEFERRED_EVENTIDX>(&sq.q, 1, 0, 512, &b, kPage);
  }

  ASSERT_NE(cid, NVME_CID_ERROR);

  auto* nvme_cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(nvme_cmd->opc, (cmd == CMD_READ) ? OPC_NVM_READ : OPC_NVM_WRITE);

  // Check doorbell behavior
  if (doorbell == DOORBELL_MMIO) {
    EXPECT_EQ(*sq.q.db, 1u) << "MMIO doorbell should be rung";
  } else {
    EXPECT_EQ(*sq.q.db, 0u) << "Deferred doorbell should NOT be rung";
  }
}

INSTANTIATE_TEST_SUITE_P(
    AllSubmitCombinations,
    SubmitTemplateTest,
    ::testing::Combine(
        ::testing::Values(CMD_READ, CMD_WRITE),
        ::testing::Values(DOORBELL_MMIO, DOORBELL_DEFERRED, DOORBELL_DEFERRED_EVENTIDX)
    )
);

// Test all 6 submit combinations via runtime
class SubmitRuntimeTest : public ::testing::TestWithParam<
    std::tuple<CommandType, DoorbellType>> {};

TEST_P(SubmitRuntimeTest, AllCombinations) {
  auto [cmd, doorbell_type] = GetParam();

  SqFix sq(8);
  DmaBuf b{};
  b.bytes = kPage;
  b.iova = 0xF0000000ull;

  std::uint16_t cid;

  // Create appropriate doorbell instance based on type
  if (doorbell_type == DOORBELL_MMIO) {
    cid = host_submit_runtime(cmd, nullptr, &sq.q, 1, 0, 512, &b, kPage);
  } else if (doorbell_type == DOORBELL_DEFERRED) {
    DeferredDoorbell deferred_db;
    cid = host_submit_runtime(cmd, &deferred_db, &sq.q, 1, 0, 512, &b, kPage);
  } else if (doorbell_type == DOORBELL_DEFERRED_EVENTIDX) {
    EventIndexedDoorbell eventidx_db;
    cid = host_submit_runtime(cmd, &eventidx_db, &sq.q, 1, 0, 512, &b, kPage);
  } else {
    FAIL() << "Unknown doorbell type";
    return;
  }

  ASSERT_NE(cid, NVME_CID_ERROR);

  auto* nvme_cmd = reinterpret_cast<const NvmeCmd*>(sq.ring.data());
  EXPECT_EQ(nvme_cmd->opc, (cmd == CMD_READ) ? OPC_NVM_READ : OPC_NVM_WRITE);

  if (doorbell_type == DOORBELL_MMIO) {
    EXPECT_EQ(*sq.q.db, 1u);
  } else {
    EXPECT_EQ(*sq.q.db, 0u);
  }
}

INSTANTIATE_TEST_SUITE_P(
    AllSubmitCombinations,
    SubmitRuntimeTest,
    ::testing::Combine(
        ::testing::Values(CMD_READ, CMD_WRITE),
        ::testing::Values(DOORBELL_MMIO, DOORBELL_DEFERRED, DOORBELL_DEFERRED_EVENTIDX)
    )
);
