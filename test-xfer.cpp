#include <chrono>
#include <ctime>
#include <iostream>
#include <ratio>
#include <string>
#include "llvm/ADT/APInt.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/KnownBits.h"

using namespace llvm;

const int MaxWidth = 5;

namespace {

std::string knownBitsString(llvm::KnownBits KB) {
  std::string S = "";
  for (int I = 0; I < KB.getBitWidth(); I++) {
    if (KB.Zero.isNegative())
      S += "0";
    else if (KB.One.isNegative())
      S += "1";
    else
      S += "?";
    KB.Zero <<= 1;
    KB.One <<= 1;
  }
  return S;
}

bool nextKB(KnownBits &x) {
  for (int i = 0; i < x.getBitWidth(); i++) {
    if (!x.Zero[i] && !x.One[i]) {
      x.Zero.setBit(i);
      return true;
    }
    if (x.Zero[i] && !x.One[i]) {
      x.Zero.clearBit(i);
      x.One.setBit(i);
      return true;
    }
    if (!x.Zero[i] && x.One[i]) {
      x.Zero.clearBit(i);
      x.One.clearBit(i);
      continue;
    }
    llvm::report_fatal_error("wow, hosed KB!");
  }
  return false;
}

void testAll(const int W, ICmpInst::Predicate Pred) {
  KnownBits x(W);
  do {
    KnownBits y(W);
    do {
      std::cout << knownBitsString(x) << " " << knownBitsString(y) << "\n";
    } while (nextKB(y));
  } while (nextKB(x));
}

void test(const int W) {
  testAll(W, CmpInst::ICMP_ULT);
}

} // anon namespace
  
int main(void) {
  if (true) {
    test(3);
  } else {
    for (int Width = 1; Width <= MaxWidth; ++Width)
      test(Width);
  }
  return 0;
}
