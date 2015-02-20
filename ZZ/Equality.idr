module ZZ.Equality

import ZZ.Definition

ZEq : ZZ -> ZZ -> Type
ZEq (MZ a b) (MZ c d) = a + d = b + c

ZEqDecidable : (x, y : ZZ) -> Dec (ZEq x y)
ZEqDecidable (MZ a b) (MZ c d) = decEq (a + d) (b + c)

ZEqReflexive : (x : ZZ) -> ZEq x x
ZEqReflexive (MZ a b) = plusCommutative a b

ZEqSymmetric : (x, y : ZZ) -> ZEq x y -> ZEq y x
ZEqSymmetric (MZ a b) (MZ c d) prf = rewrite plusCommutative d a in
                                     rewrite plusCommutative c b in
                                       sym prf

ZEqTransitive : (x, y, z : ZZ) -> ZEq x y -> ZEq y z -> ZEq x z
ZEqTransitive (MZ a b) (MZ c d) (MZ e f) prf1 prf2 = ?ZEqTransPrf

ZEqTrans1 : (x, y, z : Nat) -> x = y -> x + z = y + z
ZEqTrans1 _ _ z prf = cong {f = \x => x + z} prf

ZEqTrans2 : (a, b, c, d : Nat) -> a + b + (c + d) = (a + d) + (b + c)
ZEqTrans2 a b c d = ?ZEqTrans2Prf

ZEqTrans3 : (a, b, c, d : Nat) -> a + b + (c + d) = (a + c) + (b + d)
ZEqTrans3 a b c d = ?ZEqTrans3Prf

ZEqTrans4 : (a, b, c, d : Nat) -> a = b + c -> c = d -> a = b + d
ZEqTrans4 a b c d prf1 prf2 = rewrite sym prf2 in prf1

ZEqTrans5 : (a, b, c, d, e, f : Nat)
  -> (a + f) + (d + e) = (b + e) + (c + f)
  -> c + f = d + e
  -> (a + f) + (d + e) = (b + e) + (d + e)
ZEqTrans5 a b c d e f prf1 prf2 = ZEqTrans4 ((a + f) + (d + e)) (b + e) (c + f) (d + e) prf1 prf2

plusCancelLemma : (a, b, k : Nat) -> a + S k = b + S k -> a + k = b + k
plusCancelLemma a b k prf = let prf1 = trans (plusSuccRightSucc a k) prf
                                prf2 = trans prf1 (sym (plusSuccRightSucc b k)) in
                            succInjective (a + k) (b + k) prf2

plusCancel : (a, b, c : Nat) -> a + c = b + c -> a = b
plusCancel a b Z prf =
  rewrite sym (plusZeroRightNeutral a) in
  rewrite sym (plusZeroRightNeutral b) in
    prf
plusCancel a b (S k) prf = plusCancel a b k (plusCancelLemma a b k prf)

---------- Proofs ----------

ZZ.Equality.ZEqTransPrf = proof
  intros
  let prf3 = ZEqTrans1 (a + d) (b + c) (e + f) prf1
  let prf4 = sym (ZEqTrans2 a d e f)
  let prf5 = trans prf4 prf3
  let prf6 = ZEqTrans3 b c e f
  let prf7 = trans prf5 prf6
  let prf8 = ZEqTrans5 a b c d e f prf7 prf2
  exact plusCancel (a + f) (b + e) (d + e) prf8

ZZ.Equality.ZEqTrans2Prf = proof
  intros
  rewrite plusAssociative a b (c + d)
  rewrite sym (plusAssociative b c d)
  rewrite plusCommutative d (b + c)
  rewrite sym (plusAssociative a d (b + c))
  refine Refl

ZZ.Equality.ZEqTrans3Prf = proof
  intros
  rewrite sym (plusAssociative (a + b) c d)
  rewrite plusAssociative a b c
  rewrite plusCommutative c b
  rewrite sym (plusAssociative a c b)
  rewrite sym (plusAssociative (a + c) b d)
  trivial

