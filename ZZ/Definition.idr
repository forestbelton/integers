module ZZ.Definition

data ZZ : Type where
  MZ : Nat -> Nat -> ZZ

nat2ZZ : Nat -> ZZ
nat2ZZ x = MZ x Z

ZZero : ZZ
ZZero = MZ 0 0

ZOne : ZZ
ZOne = MZ 1 0
