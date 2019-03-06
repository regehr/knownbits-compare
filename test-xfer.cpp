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

namespace {

///////////////////////////////////////////////////////

enum class Tristate { Unknown = -1, False = 0, True = 1 };

APInt getUMin(const KnownBits &x) { return x.One; }

APInt getUMax(const KnownBits &x) { return ~x.Zero; }

bool isSignKnown(const KnownBits &x) {
  unsigned W = x.getBitWidth();
  return x.One[W - 1] || x.Zero[W - 1];
}

APInt getSMin(const KnownBits &x) {
  if (isSignKnown(x))
    return x.One;
  APInt Min = x.One;
  Min.setBit(x.getBitWidth() - 1);
  return Min;
}

APInt getSMax(const KnownBits &x) {
  if (isSignKnown(x))
    return ~x.Zero;
  APInt Max = ~x.Zero;
  Max.clearBit(x.getBitWidth() - 1);
  return Max;
}

Tristate myULT(KnownBits x, KnownBits y) {
  if (getUMax(x).ult(getUMin(y)))
    return Tristate::True;
  if (getUMin(x).uge(getUMax(y)))
    return Tristate::False;
  return Tristate::Unknown;
}

Tristate mySLT(KnownBits x, KnownBits y) {
  if (getSMax(x).slt(getSMin(y)))
    return Tristate::True;
  if (getSMin(x).sge(getSMax(y)))
    return Tristate::False;
  return Tristate::Unknown;
}

///////////////////////////////////////////////////////

const bool Verbose = false;

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
    if (Verbose)
      std::cout << knownBitsString(x);
    {
      auto UMin = getUMin(x);
      auto UMinBF = bfUMin(x);
      auto UMax = getUMax(x);
      auto UMaxBF = bfUMax(x);
      if (Verbose) {
        std::cout << " UMin = " << UMin.toString(10, false);
        std::cout << " (" << UMinBF.toString(10, false) << ")  ";
        std::cout << "UMax = " << UMax.toString(10, false);
        std::cout << " (" << UMaxBF.toString(10, false) << ")  ";
      }
      if (UMin != UMinBF)
        llvm::report_fatal_error("UMin");
      if (UMax != UMaxBF)
        llvm::report_fatal_error("UMax");
    }
    {
      auto SMin = getSMin(x);
      auto SMinBF = bfSMin(x);
      auto SMax = getSMax(x);
      auto SMaxBF = bfSMax(x);
      if (Verbose) {
        std::cout << " SMin = " << SMin.toString(10, false);
        std::cout << " (" << SMinBF.toString(10, false) << ")  ";
        std::cout << "SMax = " << SMax.toString(10, false);
        std::cout << " (" << SMaxBF.toString(10, false) << ")\n";
      }
      if (SMin != SMinBF)
        llvm::report_fatal_error("SMin");
      if (SMax != SMaxBF)
        llvm::report_fatal_error("SMax");
    }
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
  if (true) {
    testAll(W, CmpInst::ICMP_ULT);
    testAll(W, CmpInst::ICMP_SLT);
  }
}

} // namespace

int main(void) {
  if (true) {
    test(3);
  } else {
    for (int Width = 1; Width <= 8; ++Width)
      test(Width);
  }
  return 0;
}
