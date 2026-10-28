# Relative alpha naturality and the scheme-alpha character law

The submission retains original endpoints 038, 039 and 052, with 19 configured obligations. The first two give the original root data, unique alpha frame and pointed-Cartesian base-change naturality at arbitrary universe level. The character law is a separate selected mathematical result.

For the character law, let k be a characteristic-zero field, S a scheme over k, E an elliptic family on S, and M a full level-four marking. Let z be a global scalar and a a global section of the identity cotangent line. Assume `MillerPhase E M z` and `RealizesAlpha E M a`, with the latter retaining the original affine-test and compatible conormal comparison conditions.

For any matrix A over Z/4Z satisfying `PreservesEven A`, the theorem constructs a full level-four marking Mprime satisfying `Changes E M Mprime A` and `MillerPhase E Mprime z`. Here `PreservesEven` requires determinant one and preservation of the quadratic form v0*v1 after reduction modulo two. `Changes` uses the original matrix action on the two marked sections.

Every global cotangent section aprime satisfying `RealizesAlpha E Mprime aprime` obeys the exact transformation formula

```
aprime = z ^ (characterExponent A).val • a
```

The bullet denotes scalar multiplication of sections. The exponent lies in Z/4Z and `.val` is its representative in {0,1,2,3}; it is `A[0,0] - 1` when A[0,0] has odd representative, and `A[0,1]` otherwise. The phase and realization predicates are assumptions of the character theorem. Its conclusion gives a changed marking with that same phase and equality for every realizing section, rather than an unspecified scalar proportionality.

All Lean statements, target selection and original endpoint recovery remain unchanged. Original052 is already covered elsewhere and is not counted twice. This submission does not claim completion of the whole paper.
