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

enum class Tristate { Unknown, False, True };

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

Tristate myEQ(KnownBits x, KnownBits y) {
  if (x.isConstant() && y.isConstant() && (x.getConstant() == y.getConstant()))
    return Tristate::True;
  if (((x.One & y.Zero) != 0) || ((x.Zero & y.One) != 0))
    return Tristate::False;
  return Tristate::Unknown;
}

Tristate myNE(KnownBits x, KnownBits y) {
  if (x.isConstant() && y.isConstant() && (x.getConstant() == y.getConstant()))
    return Tristate::False;
  if (((x.One & y.Zero) != 0) || ((x.Zero & y.One) != 0))
    return Tristate::True;
  return Tristate::Unknown;
}

Tristate myUGT(KnownBits x, KnownBits y) { return Tristate::Unknown; }

Tristate myUGE(KnownBits x, KnownBits y) { return Tristate::Unknown; }

Tristate myULT(KnownBits x, KnownBits y) {
  if (getUMax(x).ult(getUMin(y)))
    return Tristate::True;
  if (getUMin(x).uge(getUMax(y)))
    return Tristate::False;
  return Tristate::Unknown;
}

Tristate myULE(KnownBits x, KnownBits y) { return Tristate::Unknown; }

Tristate mySGT(KnownBits x, KnownBits y) { return Tristate::Unknown; }

Tristate mySGE(KnownBits x, KnownBits y) { return Tristate::Unknown; }

Tristate mySLT(KnownBits x, KnownBits y) {
  if (getSMax(x).slt(getSMin(y)))
    return Tristate::True;
  if (getSMin(x).sge(getSMax(y)))
    return Tristate::False;
  return Tristate::Unknown;
}

Tristate mySLE(KnownBits x, KnownBits y) { return Tristate::Unknown; }

///////////////////////////////////////////////////////

const bool Verbose = true;

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

Tristate bruteForce(KnownBits x, KnownBits y, ICmpInst::Predicate Pred) {
  if (!isConcrete(x))
    return merge(bruteForce(setLowest(x), y, Pred),
                 bruteForce(clearLowest(x), y, Pred));
  if (!isConcrete(y))
    return merge(bruteForce(x, setLowest(y), Pred),
                 bruteForce(x, clearLowest(y), Pred));
  auto xc = x.getConstant();
  auto yc = y.getConstant();
  bool res;
  switch (Pred) {
  case CmpInst::ICMP_EQ:
    res = xc == yc;
    break;
  case CmpInst::ICMP_NE:
    res = xc != yc;
    break;
  case CmpInst::ICMP_UGT:
    res = xc.ugt(yc);
    break;
  case CmpInst::ICMP_UGE:
    res = xc.uge(yc);
    break;
  case CmpInst::ICMP_ULT:
    res = xc.ult(yc);
    break;
  case CmpInst::ICMP_ULE:
    res = xc.ule(yc);
    break;
  case CmpInst::ICMP_SGT:
    res = xc.sgt(yc);
    break;
  case CmpInst::ICMP_SGE:
    res = xc.sge(yc);
    break;
  case CmpInst::ICMP_SLT:
    res = xc.slt(yc);
    break;
  case CmpInst::ICMP_SLE:
    res = xc.sle(yc);
    break;
  default:
    llvm::report_fatal_error("no implementation for predicate");
  }
  return res ? Tristate::True : Tristate::False;
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

const char *predStr(ICmpInst::Predicate Pred) {
  switch (Pred) {
  case CmpInst::ICMP_EQ:
    return "==";
  case CmpInst::ICMP_NE:
    return "!=";
  case CmpInst::ICMP_UGT:
    return ">u";
  case CmpInst::ICMP_UGE:
    return ">=u";
  case CmpInst::ICMP_ULT:
    return "<u";
  case CmpInst::ICMP_ULE:
    return "<=u";
  case CmpInst::ICMP_SGT:
    return ">s";
  case CmpInst::ICMP_SGE:
    return ">=s";
  case CmpInst::ICMP_SLT:
    return "<s";
  case CmpInst::ICMP_SLE:
    return "<=s";
  default:
    llvm::report_fatal_error("no string for predicate");
  }
}

void testAll(const int W, ICmpInst::Predicate Pred) {
  KnownBits x(W);
  do {
    KnownBits y(W);
    do {
      Tristate Res1;
      switch (Pred) {
      case CmpInst::ICMP_EQ:
        Res1 = myEQ(x, y);
        break;
      case CmpInst::ICMP_NE:
        Res1 = myNE(x, y);
        break;
      case CmpInst::ICMP_UGT:
        Res1 = myUGT(x, y);
        break;
      case CmpInst::ICMP_UGE:
        Res1 = myUGE(x, y);
        break;
      case CmpInst::ICMP_ULT:
        Res1 = myULT(x, y);
        break;
      case CmpInst::ICMP_ULE:
        Res1 = myULE(x, y);
        break;
      case CmpInst::ICMP_SGT:
        Res1 = mySGT(x, y);
        break;
      case CmpInst::ICMP_SGE:
        Res1 = mySGE(x, y);
        break;
      case CmpInst::ICMP_SLT:
        Res1 = mySLT(x, y);
        break;
      case CmpInst::ICMP_SLE:
        Res1 = mySLE(x, y);
        break;
      default:
        llvm::report_fatal_error("no my version of predicate");
      }
      auto Res2 = bruteForce(x, y, Pred);
      if (Verbose) {
        std::cout << knownBitsString(x) << " " << predStr(Pred) << " "
                  << knownBitsString(y);
        std::cout << " = " << printTristate(Res1) << " (" << printTristate(Res2)
                  << ")\n";
      }
      if (Res1 != Res2)
        llvm::report_fatal_error("unsound or imprecise!");
    } while (nextKB(y));
  } while (nextKB(x));
}

void test(const int W) {
  if (false)
    testMinMax(W);
  if (true) {
    testAll(W, CmpInst::ICMP_EQ);
    testAll(W, CmpInst::ICMP_NE);
    // testAll(W, CmpInst::ICMP_UGT);
    // testAll(W, CmpInst::ICMP_UGE);
    testAll(W, CmpInst::ICMP_ULT);
    // testAll(W, CmpInst::ICMP_ULE);
    // testAll(W, CmpInst::ICMP_SGT);
    // testAll(W, CmpInst::ICMP_SGE);
    testAll(W, CmpInst::ICMP_SLT);
    // testAll(W, CmpInst::ICMP_SLE);
  }
  std::cout << "done testing width " << W << ".\n";
}

} // namespace

int main(void) {
  if (true) {
    test(2);
  } else {
    for (int Width = 1; Width <= 8; ++Width)
      test(Width);
  }
  return 0;
}
