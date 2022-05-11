SetLogFile("Examples2.out");
TestEllCurves := [* *];
TestPoints := [* *];

p := 2;

// non-CM case
E := EllipticCurve([1, -1, 1, -41, 96]);
P := E![2, -6];
Append(~TestEllCurves, E);
Append(~TestPoints, P);


// CM case
E := EllipticCurve([0, 0, 0, -36, 0]);
P := E![-2, -8];
Append(~TestEllCurves, E);
Append(~TestPoints, P);


R<x> := PolynomialRing(Rationals());
S := FieldOfFractions(R);


for i in [1..2] do
	E := TestEllCurves[i];
	P := TestPoints[i];
	E;
	P;
	TwoTorsionField := SplittingField(DivisionPolynomial(E,2));

	// compute [2]^{-1}(P)
	phi := MultiplicationByMMap(E,2);
	S := Difference(Pullback(phi,P), BaseScheme(phi));
	TwoDivisionPoints, SplField := PointsOverSplittingField(S);
	// Convert the splitting field of S to
	// an algebraic number field
	p := AbsolutePolynomial(SplField);
	K := NumberField(p);
	assert #RationalPoints(S,K) eq 4;
	// L is the minimal field of definition of
	// the 2-division points of P
	L := sub<K | &cat[ Coordinates(Q) : Q in RationalPoints(S,K) ] >;
	assert #RationalPoints(S,L) eq 4;
	"Kummer degree", Degree(L);
	"Torsion degree", Degree(TwoTorsionField);
end for;




