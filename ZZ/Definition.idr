module ZZ.Definition

data ZZ : Type where
  MZ : Nat -> Nat -> ZZ

nat2ZZ : Nat -> ZZ
nat2ZZ x = MZ x Z
