//===- TripleTest_SimpleOS.cpp - Unit tests for SimpleOS triple -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM
// Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Stub unit test — paste into llvm/unittests/TargetParser/TripleTest.cpp.
// This file is NOT compiled standalone; it exists so maintainers can copy
// the TEST() block into the real test file when landing the SimpleOS
// triple patch (see 0001-triple-simpleos.patch.md).
//
//===----------------------------------------------------------------------===//

TEST(TripleTest, SimpleOS) {
  Triple T;

  T = Triple("x86_64-unknown-simpleos");
  EXPECT_EQ(Triple::x86_64, T.getArch());
  EXPECT_EQ(Triple::UnknownVendor, T.getVendor());
  EXPECT_EQ(Triple::SimpleOS, T.getOS());
  EXPECT_EQ(Triple::UnknownEnvironment, T.getEnvironment());
  EXPECT_TRUE(T.isOSBinFormatELF());

  T = Triple("aarch64-unknown-simpleos");
  EXPECT_EQ(Triple::aarch64, T.getArch());
  EXPECT_EQ(Triple::UnknownVendor, T.getVendor());
  EXPECT_EQ(Triple::SimpleOS, T.getOS());
  EXPECT_EQ(Triple::UnknownEnvironment, T.getEnvironment());
  EXPECT_TRUE(T.isOSBinFormatELF());

  T = Triple("riscv64-unknown-simpleos");
  EXPECT_EQ(Triple::riscv64, T.getArch());
  EXPECT_EQ(Triple::SimpleOS, T.getOS());
  EXPECT_TRUE(T.isOSBinFormatELF());

  T = Triple("riscv32-unknown-simpleos");
  EXPECT_EQ(Triple::riscv32, T.getArch());
  EXPECT_EQ(Triple::SimpleOS, T.getOS());

  // Round-trip normalization: a bare `<arch>-simpleos` should expand to
  // `<arch>-unknown-simpleos` and `getOSTypeName(SimpleOS)` should yield
  // the string "simpleos".
  EXPECT_EQ("x86_64-unknown-simpleos",
            Triple::normalize("x86_64-simpleos"));
  EXPECT_EQ("aarch64-unknown-simpleos",
            Triple::normalize("aarch64-simpleos"));
  EXPECT_EQ(StringRef("simpleos"),
            Triple::getOSTypeName(Triple::SimpleOS));
}
