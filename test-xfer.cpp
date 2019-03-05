#include "llvm/ADT/APInt.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/KnownBits.h"
#include <iostream>
#include <ctime>
#include <ratio>
#include <chrono>

using namespace llvm;

const int MaxWidth = 5;

namespace {

void testAll(const int W, ICmpInst::Predicate Pred) {
}

void test(const int W) {
  testAll(W, CmpInst::ICMP_ULT);
}

} // anon namespace
  
int main(void) {
  for (int Width = 1; Width <= MaxWidth; ++Width)
    test(Width);
  return 0;
}
