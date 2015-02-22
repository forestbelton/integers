module ZZ.Multiplication

import ZZ.Definition
import ZZ.Equality

ZMult : ZZ -> ZZ -> ZZ
ZMult (MZ a b) (MZ c d) = MZ (a * c + b * d) (a * d + b * c)

ZMultOneLeftNeutral : (x : ZZ) -> ZEq (ZMult ZOne x) x
ZMultOneLeftNeutral (MZ a b) =
  rewrite plusCommutative a 0 in
  rewrite plusCommutative a 0 in
  rewrite plusCommutative b 0 in
  rewrite plusCommutative b 0 in
    plusCommutative a b

ZMultOneRightNeutral : (x : ZZ) -> ZEq (ZMult x ZOne) x
ZMultOneRightNeutral (MZ a b) =
  rewrite multOneRightNeutral a in
  rewrite multZeroRightZero b in
  rewrite plusCommutative a 0 in
  rewrite multOneRightNeutral b in
  rewrite multZeroRightZero a in
    plusCommutative a b

ZMultZeroLeftZero : (x : ZZ) -> ZEq (ZMult ZZero x) ZZero
ZMultZeroLeftZero (MZ a b) = Refl

ZMultZeroRightZero : (x : ZZ) -> ZEq (ZMult x ZZero) ZZero
ZMultZeroRightZero (MZ a b) =
  rewrite multZeroRightZero a in
    Refl
