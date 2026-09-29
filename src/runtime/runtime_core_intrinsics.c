/* Standalone core-C intrinsic owner. The ordinary composition selects
 * runtime.c instead; these owners must never be linked together. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime_core_intrinsics_impl.h"
