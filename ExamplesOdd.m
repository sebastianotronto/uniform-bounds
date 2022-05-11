SetLogFile("ExamplesOdd.out");
TestEllCurves := [* *];
TestPrimes := [];
TestPoints := [* *];

// non-CM cases

// p=3
p := 3;
E := EllipticCurve([0, 1, 1, -7, 5]);
P := E![-1, 3];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=5
p := 5;
E := EllipticCurve([0, -1, 0, -1, -1]);
P := E![2, 1];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=7
p := 7;
E := EllipticCurve([1, -1, 0, -389, -2859]);
P := E![26, 51];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=11
p := 11;
E := EllipticCurve([1, -1, 1, -32693, -2267130]);
P := E![212, 438];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=13
p := 13;
E := EllipticCurve([0, 0, 1, -8211, -286610]);
P := E![235, 3280];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// p=17
p := 17;
E := EllipticCurve([1, -1, 1, -27365, -1735513]);
P := E![4047/4, 249623/8];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// p=37
p := 37;
E := EllipticCurve([1,1,1, -208083, -36621194]); 
P := E![1190, 36857];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// CM cases

// p=3;
p := 3;
E := EllipticCurve([0, 0, 1, 0, -34]);
P := E![6, 13];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=7;
p := 7;
E := EllipticCurve([0, 0, 0, -1715, -33614]);
P := E![57, 232];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=11;
p := 11;
E := EllipticCurve([0, -1, 1, -887, -10143]);
P := E![81, 665];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// p=19;
p := 19;
E := EllipticCurve([0, 0, 1, -13718, -619025]);
P := E![2527, 126891];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// p=43;
p := 43;
E := EllipticCurve([0, 0, 1, -1590140, -771794326]);
P := E![66276734/29929, -419567566482/5177717];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);

// p=67
p := 67;
E := EllipticCurve([0, 0, 1, -33083930, -73244287055]);
P := E![49970077554856210455913/1635061583290810756, 10956085084392718114395997318977993/2090745506172424414999081096];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);


// p=163
p := 163;
E := EllipticCurve([0, 0, 1, -57772164980, -5344733777551611]);
P := E![11509239442924885437268908633781200359420118913003369978393345109760\
106879910549333516471934422283642065851592143222941412384176513163782707510544\
62255219601909957/311992022769461830324863650831941796504999213181479488782946\
521369692997803032831890409734615787088941811816830930483142218605079399931371\
0673084161372869121, 845582050130072311275386597783560053187286126452227505238\
961361128589023970974731358601337161665095706235200096614164700116910277815335\
123701887606850046247657712935173132161200083294592082728287513749943483489018\
633303880458566953626601201883/55108074229621251935606667921603236827499658224\
734390517385795522802413365463851334881730587838061307337730981797126572349689\
354868599964017033267324255771221273619143339696093211151999034459007978618073\
50740024000213961207891021464831];
Append(~TestEllCurves, E);
Append(~TestPrimes, p);
Append(~TestPoints, P);
TestFactorisations := [];

assert #TestEllCurves eq #TestPrimes;
assert #TestPoints eq #TestPrimes;

R<x> := PolynomialRing(Rationals());
S := FieldOfFractions(R);

for i in [1..#TestPrimes] do
	E := TestEllCurves[i];
	p := TestPrimes[i];
	P := TestPoints[i];
	"====================";
	"Prime", p;
	E;
	P;	
	time dp := DivisionPolynomial(E,p);
	time ap, bp, cp := DivisionPolynomial(E,p+1);
	time am, bm, cm := DivisionPolynomial(E,p-1);
	time np := x*dp^2 - R!(ap*am/cp);
	xP := P[1]/P[3];
	dpP := np - xP * dp^2;
	time fact := Factorisation(dpP);
	[Degree(p[1]) : p in fact];
end for;

