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
#include "llvm/Analysis/LazyValueInfo.h"

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

enum class Tristate {
  Unknown = -1, False = 0, True = 1
};

const char *printTristate(Tristate t) {
  if (t == Tristate::True)
    return "true";
  if (t == Tristate::False)
    return "false";
  return "unknown";
}

bool isConcrete(KnownBits x) {
  return (x.Zero | x.One).isAllOnesValue();
}

Tristate merge(Tristate a, Tristate b) {
  if (a == Tristate::True && b == Tristate::True)
    return Tristate::True;
  if (a == Tristate::False && b == Tristate::False)
    return Tristate::False;
  return Tristate::Unknown;
}

KnownBits setLowest(KnownBits x) {
  for (int i = 0; i < x.getBitWidth(); i++) {
    if (!x.Zero[i] && !x.One[i]) {
      x.One.setBit(i);
      return x;
    }
  }
  llvm::report_fatal_error("can't set");
}

KnownBits clearLowest(KnownBits x) {
  for (int i = 0; i < x.getBitWidth(); i++) {
    if (!x.Zero[i] && !x.One[i]) {
      x.Zero.setBit(i);
      return x;
    }
  }
  llvm::report_fatal_error("can't set");
}

Tristate compareAll(KnownBits x, KnownBits y) {
  if (!isConcrete(x))
    return merge(compareAll(setLowest(x), y),
		 compareAll(clearLowest(x), y));
  if (!isConcrete(y))
    return merge(compareAll(x, setLowest(y)),
		 compareAll(x, clearLowest(y)));
  // FIXME
  return x.getConstant().ult(y.getConstant()) ? Tristate::True : Tristate::False;
}

void testAll(const int W, ICmpInst::Predicate Pred) {
  KnownBits x(W);
  do {
    KnownBits y(W);
    do {
      auto Res = compareAll(x, y);
      std::cout << knownBitsString(x) << " <u " << knownBitsString(y);
      std::cout << " = " << printTristate(Res) << "\n";
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
