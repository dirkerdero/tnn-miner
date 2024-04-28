#ifndef astrotest_h
#define astrotest_h

#include <bitset>

#include "pow.h"
#include "powtest.h"
#include "lookup.h"
#include "lookupcompute.h"

#include "hex.h"

#include <xxhash64.h>

struct OpTestResult {
  unsigned char input[256];
  unsigned char result[256];
  std::chrono::nanoseconds duration_ns;
};

void optest(int op, workerData &worker, byte testData[32], OpTestResult &testRes, bool print=true);
void optest_lookup(int op, workerData &worker, byte testData[32], OpTestResult &testRes, bool print=true);
void optest_avx2(int op, workerData &worker, byte testData[32], OpTestResult &testRes, bool print=true);

#endif