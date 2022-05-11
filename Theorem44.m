// This script verifies some claims made in the proof of Theorem 4.4
// It is based on the classification by Rouse and Zureick-Brown
// of all possible 2-adic images of Galois for non-CM elliptic curves
// over Q. As such, this script requires the following 4 data files:
// - gl2finedata.txt
// - gl2data.txt
// - curvelist1.txt
// - curvelist2.txt
// which may be obtained from J. Rouse's page https://users.wfu.edu/rouseja/2adic/

SetLogFile("Theorem44.out");

load "gl2finedata.txt";
load "gl2data.txt";
load "curvelist1.txt";
load "curvelist2.txt";

// ==== Helper functions ====

// The next two functions compute a simplified presentation
// of a finitely presented matrix group G. The first one tries
// to find a superfluous generator in the given presentation.
// The second function iterates the first until it reaches
// a non-redundant set of generators.
function EliminateOneGenerator(G)
	GL2 := GL(2,BaseRing(G));
	for i in [1..#Generators(G)] do
		H := sub<GL2 | [ G.j : j in [1..#Generators(G)] | i ne j ]>;
		if #H eq #G then
			return H;
		end if;
	end for;
	return G;
end function;


function SimplifyGroupPresentation(G)
	H := EliminateOneGenerator(G);
	if #Generators(H) eq #Generators(G) then
		return G;
	else
		return SimplifyGroupPresentation(H);
	end if;
end function;


// The next function returns true iff a certain subgroup listed 
// in gl2finedata arises as the 2-adic image of Galois for a 
// non-CM elliptic curve over Q
function RealisableFineSubgroup(X)
	for cl in curvelist2 do
		if cl[1] eq X then
			return true;
		end if;
	end for;
	return false;
end function;

// ==== Main computation ====

// We start by checking that all subgroups contain the scalar 17.
// This is done by checking that each subgroup satisfies at least
// one of the following two conditions:
// - the subgroup is obtained by pullback to GL_2(Z_2) from its
//   reduction modulo 2^k for some k <= 4
// - the subgroup is obtained by pullback from a subgroup G of 
//   GL_2(Z/2^kZ) for some k>4, and 17 belongs to G
// Notice that the subgroups are organised into two separate lists,
// called finesublist and newsublist, that contain slightly different
// information.
for subg in finesublist do
	G := subg[4];
	level := subg[3];
	assert ( (level le 16) or (GL(2,BaseRing(G))!Matrix(BaseRing(G), 2,2, [1+2^4,0,0,1+2^4]) in G) ) ;
end for;

for subg in newsublist do
	G := subg[3];
	level := subg[2];
	assert ( (level le 16) or (GL(2,BaseRing(G))!Matrix(BaseRing(G), 2,2, [1+2^4,0,0,1+2^4]) in G) ) ;
end for;

// Given a subgroup H of GL_2(Z/2^kZ) and an integer toLevel >= k, 
// the next function returns the subgroup G of GL_2(Z/2^{toLevel}Z)
// given by the inverse image of H under the natural reduction map
// from GL_2(Z/2^{toLevel}Z) to GL_2(Z/2^kZ).
// This is done by explicitly adding to an arbitrary lift of H
// a set of matrices that generate the kernel of the reduction map
function LiftSubgroup(H, toLevel)
	fromLevel := #BaseRing(H);
	R := Integers(toLevel);
	GL2 := GL(2,R);
	congruenceGenerators := [ Matrix( R,2,2, [1+fromLevel,0,0,1]), Matrix( R,2,2, [1,0+fromLevel,0,1]), Matrix( R,2,2, [1,0,0+fromLevel,1]), Matrix( R,2,2, [1,0,0,1+fromLevel])   ];
	G := sub<GL2 | [ ChangeRing(ChangeRing(H.i,Integers()), Integers(toLevel)) : i in [1..#Generators(H)]] cat congruenceGenerators >;
	assert #G eq (toLevel/fromLevel)^4*#H;
	return G;
end function;

// Next we list all subgroups that do not contain
// any scalar lambda such that v_2(lambda-1) <= 3.
// Such a scalar certainly exists if G is pulled
// back from a subgroup of GL_2(Z/2^kZ) with k<=3,
// so we only need to run this test when k>3.
// The next lines thus verify a claim made in
// the course of the proof, namely, that one
// just needs to consider the subgroups with
// labels X238a, X238b, X238c, X238d, X239a, 
// X239b, X239c, X239d. We further check that
// all these groups are obtained by pullback
// from GL_2(Z/32Z).
BadSubgroups := [];

"=============================================";
"List of subgroups not containing scalars lambda with v_2(lambda-1) <= 3";

for subg in finesublist do
	if RealisableFineSubgroup(subg[5]) then
		G := subg[4];
		level := subg[3];
		if level ge 16 then
			GL2 := GL(2,BaseRing(G));
			PossibleScalars := [ GL2!(s*IdentityMatrix(BaseRing(G), 2)) : s in [1..level] | Valuation(s-1,2) le 3 and Valuation(s-1,2) ge 1 ];
			if not &or[s in G : s in PossibleScalars] then
				Append(~BadSubgroups, [* G, subg[5] *]);
				subg[5];
				"Level", level;
				assert GL2!(17*IdentityMatrix(BaseRing(G), 2)) in G;
			end if;
		end if;
	end if;
end for;


// We now check another claim made in the course of the proof.
// For a given subgroup G, we look for vectors v in (Z/16Z)^2
// with the property that (g*v-v) is 0 modulo 16 for all g
// in a set of generators of G. In the notation of the proof
// of Theorem 4.4, this is a necessary condition for v to be
// the image modulo 16 of \xi(\lambda). In all cases, we find
// that v is trivial modulo 8.
// Concretely, we list all vectors v in (Z/16Z)^2 by considering
// integral vectors in {0,...,15}^2. For each such v and each g
// in a generating set of G, we compute g*v-v and check whether
// it is divisible by 16 over the integers (equivalently, its
// reduction modulo 16 is trivial). If v satisfies this
// condition for each g, then we add it(s reduction mod 8) to 
// the list of 'candidates' for \xi(\lambda).

"=============================================";
"Checking that \xi(lambda) is trivial modulo 8";

for BadSubgroup in BadSubgroups do
	"Considering group", BadSubgroup[2];
	G := BadSubgroup[1];
	Candidates := {};
	for a in [0..2^4-1] do
	for b in [0..2^4-1] do
	test := true;
	v := Matrix(Integers(),2,1,[a,b]);
	for g in Generators(G) do
		gv := ChangeRing(g,Integers())*v;
		test := test and ((gv-v)[1][1] mod 16 eq 0) and ((gv-v)[2][1] mod 16 eq 0);
	end for;
	if test then
		Candidates := Candidates join { [v[1][1] mod 8, v[2][1] mod 8] };
	end if;
	end for;
	end for;
	"Candidates for \xi(\lambda) mod 8:", Candidates;
	assert #Candidates eq 1;
end for;

// Finally, we perform the computation described at the end of the
// proof of Theorem 4.4. Namely, let G8 be the reduction modulo
// 2^8 of the subgroup G and let H be the subgroup of G8 generated
// by 8th powers. Finally let Q=G8/H (which we compute using a
// simplified presentation for Q8, in order to speed up the
// computation). We then simply invoke MAGMA's internal machinery
// for group cohomology to compute H^1(Q, E[8]) and check that its
// exponent divides 4.

"=============================================";
"Computing the exponent of the cohomology group H^1(Q, E[8])";

for BadSubgroup in BadSubgroups do
	"Considering group", BadSubgroup[2];
	G := BadSubgroup[1];
	G8 := LiftSubgroup(G, 2^8);
	G8s := SimplifyGroupPresentation(G8);
	rk := {g^8 : g in G8s | ChangeRing(g,Integers(8)) eq IdentityMatrix(Integers(8),2)};
	H := sub<G8s | rk>;
	Q := G8s/H;
	CM2 := CohomologyModule(Q, [8,8], [ ChangeRing(G8s.i,Integers()) : i in [1..#Generators(Q)] ]);
	H12 := CohomologyGroup(CM2,1);
	"Structure of H^1(Q, E[8])", H12;
	e := LCM(Moduli(H12));
	"Exponent", e;
	assert (4 mod e) eq 0;
end for;


