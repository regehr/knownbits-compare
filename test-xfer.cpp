#include "llvm/ADT/APInt.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <ctime>
#include <iostream>
#include <ratio>
#include <string>

using namespace llvm;

const int MaxWidth = 5;

namespace {

///////////////////////////////////////////////////////

enum class Tristate { Unknown = -1, False = 0, True = 1 };

APInt getUMin(KnownBits x) { return x.One; }

APInt getUMax(KnownBits x) { return ~x.Zero; }

APInt getSMin(KnownBits x) { return x.One; }

APInt getSMax(KnownBits x) { return ~x.Zero; }

Tristate myULT(KnownBits x, KnownBits y) {
  if (getUMax(x).ult(getUMin(y)))
    return Tristate::True;
  if (getUMin(x).uge(getUMax(y)))
    return Tristate::False;
  return Tristate::Unknown;
}

///////////////////////////////////////////////////////

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

const char *printTristate(Tristate t) {
  if (t == Tristate::True)
    return "true";
  if (t == Tristate::False)
    return "false";
  return "unknown";
}

bool isConcrete(KnownBits x) { return (x.Zero | x.One).isAllOnesValue(); }

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
  llvm::report_fatal_error("can't clear");
}

Tristate bruteForce(KnownBits x, KnownBits y) {
  if (!isConcrete(x))
    return merge(bruteForce(setLowest(x), y), bruteForce(clearLowest(x), y));
  if (!isConcrete(y))
    return merge(bruteForce(x, setLowest(y)), bruteForce(x, clearLowest(y)));
  // FIXME generalize
  return x.getConstant().ult(y.getConstant()) ? Tristate::True
                                              : Tristate::False;
}

APInt bfUMin(KnownBits x) {
  if (isConcrete(x))
    return x.getConstant();
  auto a = bfUMin(setLowest(x));
  auto b = bfUMin(clearLowest(x));
  return a.ult(b) ? a : b;
}

APInt bfUMax(KnownBits x) {
  if (isConcrete(x))
    return x.getConstant();
  auto a = bfUMax(setLowest(x));
  auto b = bfUMax(clearLowest(x));
  return a.ugt(b) ? a : b;
}

APInt bfSMin(KnownBits x) {
  if (isConcrete(x))
    return x.getConstant();
  auto a = bfSMin(setLowest(x));
  auto b = bfSMin(clearLowest(x));
  return a.slt(b) ? a : b;
}

APInt bfSMax(KnownBits x) {
  if (isConcrete(x))
    return x.getConstant();
  auto a = bfSMax(setLowest(x));
  auto b = bfSMax(clearLowest(x));
  return a.sgt(b) ? a : b;
}

void testMinMax(int W) {
  KnownBits x(W);
  do {
    std::cout << knownBitsString(x);

    std::cout << " UMin = " << getUMin(x).toString(10, false);
    std::cout << " (" << bfUMin(x).toString(10, false) << ")  ";
    std::cout << "UMax = " << getUMax(x).toString(10, false);
    std::cout << " (" << bfUMax(x).toString(10, false) << ")  ";
    if (bfUMin(x).ugt(bfUMax(x)))
      llvm::report_fatal_error("unsigned");

    std::cout << " SMin = " << getSMin(x).toString(10, true);
    std::cout << " (" << bfSMin(x).toString(10, true) << ")  ";
    std::cout << "SMax = " << getSMax(x).toString(10, true);
    std::cout << " (" << bfSMax(x).toString(10, true) << ")\n";
    if (bfSMin(x).sgt(bfSMax(x)))
      llvm::report_fatal_error("signed");

  } while (nextKB(x));
}

void testAll(const int W, ICmpInst::Predicate Pred) {
  KnownBits x(W);
  do {
    KnownBits y(W);
    do {
      auto Res1 = myULT(x, y);
      auto Res2 = bruteForce(x, y);
      std::cout << knownBitsString(x) << " <u " << knownBitsString(y);
      std::cout << " = " << printTristate(Res1) << " (" << printTristate(Res2)
                << ")\n";
    } while (nextKB(y));
  } while (nextKB(x));
}

void test(const int W) {
  if (true)
    testMinMax(W);
  if (false)
    testAll(W, CmpInst::ICMP_ULT);
}

} // namespace

int main(void) {
  if (true) {
    test(3);
  } else {
    for (int Width = 1; Width <= MaxWidth; ++Width)
      test(Width);
  }
  return 0;
}
