module ZZ.Addition

import ZZ.Definition
import ZZ.Equality

ZPlus : ZZ -> ZZ -> ZZ
ZPlus (MZ a b) (MZ c d) = MZ (a + c) (b + d)

ZPlusZeroLeftNeutral : (x : ZZ) -> ZEq (ZPlus ZZero x) x
ZPlusZeroLeftNeutral (MZ a b) = plusCommutative a b

ZPlusZeroRightNeutral : (x : ZZ) -> ZEq (ZPlus x ZZero) x
ZPlusZeroRightNeutral (MZ a b) =
  rewrite plusCommutative a 0 in
  rewrite plusCommutative b 0 in
  rewrite plusCommutative a b in
    Refl

ZPlusCommutative : (x, y : ZZ) -> ZEq (ZPlus x y) (ZPlus y x)
ZPlusCommutative (MZ a b) (MZ c d) =
  rewrite plusCommutative c a in
  rewrite plusCommutative b d in
  rewrite plusCommutative (d + b) (a + c) in
    Refl

ZPlusAssociative : (x, y, z : ZZ) -> ZEq (ZPlus x (ZPlus y z)) (ZPlus (ZPlus x y) z)
ZPlusAssociative (MZ a b) (MZ c d) (MZ e f) =
  rewrite plusCommutative (b + (d + f)) ((a + c) + e) in
  rewrite plusAssociative a c e in
  rewrite plusAssociative b d f in
    Refl
