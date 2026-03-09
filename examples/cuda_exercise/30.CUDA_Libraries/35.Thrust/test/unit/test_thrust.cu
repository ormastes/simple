#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <thrust/device_vector.h>
#include <thrust/host_vector.h>
#include <thrust/reduce.h>
#include <thrust/transform.h>
#include <thrust/functional.h>

class ThrustTest : public GpuTest {};

TEST_F(ThrustTest, BasicReduce) {
    thrust::device_vector<int> vec(1000, 1);
    int sum = thrust::reduce(vec.begin(), vec.end());
    EXPECT_EQ(sum, 1000);
}

TEST_F(ThrustTest, Transform) {
    thrust::device_vector<int> input(100, 2);
    thrust::device_vector<int> output(100);
    
    thrust::transform(input.begin(), input.end(), output.begin(),
                      thrust::square<int>());
    
    EXPECT_EQ(output[0], 4);
    EXPECT_EQ(output[99], 4);
}

TEST_F(ThrustTest, VectorCopy) {
    thrust::host_vector<float> h_vec(10, 3.14f);
    thrust::device_vector<float> d_vec = h_vec;
    thrust::host_vector<float> h_result = d_vec;

    EXPECT_FLOAT_EQ(h_result[0], 3.14f);
    EXPECT_FLOAT_EQ(h_result[9], 3.14f);
}
