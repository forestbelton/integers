module ZZ.Multiplication

import ZZ.Definition
import ZZ.Equality

ZMult : ZZ -> ZZ -> ZZ
ZMult (MZ a b) (MZ c d) = MZ (a * c + b * d) (a * d + b * c)
