//This code is taken from https://github.com/TimoKellerMath/QuadraticPoints/blob/main/models_and_maps.m
//and is associated to the paper http://arxiv.org/abs/2303.12566 "Computing quadratic points on modular curves X_0(N)" 
//by Nikola Adzaga, Timo Keller, Philippe Michaud-Jacobs, Filip Najman, Ekin Ozman, and Borna Vukorepa.

// Code to compute models for X_0(N), Atkin-Lehner group quotients, maps to the quotients, maps to different levels, jmap and more

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

////////////////
/// Contents /// (with brief descriptions, there are many examples throughout)
////////////////

// canonic (auxiliary) : computes canonically embedded curve from cusp forms

// simul_diag (auxiliary) : simultaneously diagonalised involution matrices

// all_diag_basis : gives basis of cusp forms on which AL-involutions are diagonal

// all_diag_X (auxiliary) : model for X_0(N) with diagonalised AL-involutions

// genus_quo : computes the genus of an AL quotient

// atkinlehnersubgrp (auxiliary) : find all AL indices in an AL subgroup

// is_hyper_quo : test if an AL quotient is hyperelliptic

// *** eqs_quos (main) *** : compute model for X_0(N), any quotients by AL groups, and the maps

// is_bi_hyperelliptic : tests if X_0(N) is bi-hyperelliptic

// genera_quo : computes genera of multiple AL quotients

// change_basis_mat (auxiliary) : change of basis matrix for two bases of cuspforms

// coeff_mat (auxiliary) : A coefficient matrix for a basis of cusp forms

// apply_basis_change (auxiliary) : Apply a change of basis matrix to a basis of cusp forms

// coord_change (auxiliary) : change of coordinate map between two canonically embedded models using different bases

// level_basis (auxiliary) : basis for S_2(M) that sits inside S_2(N)

// level_quo : map from X_0(N) to X_0(M) when X_0(M) is canonically embedded

// nicefy (auxiliary) : simplifies matrices using LLL

// find_rels (auxiliary) : expresses q-expansions in terms of cusp forms

// *** jmap (main) : computes the jmap

// *** compute_cusps (main) : computes the cusps as places on X_0(N)

// xy_coords : x- and y-expressions for map to X_0(M) elliptic or hyperelliptic

// construct_map_to_quotient : map to X_0(M) elliptic or hyperelliptic ((can be) SLOW! use xy_coords instead and see examples)

// gen_0_quo : map to X_0(M) of genus 0

// is_nonsing_p : Checks if X_0(N) is nonsingular mod p

// good_eqs_mod_p : Tries to find defining equations with good reduction mod p

// canonic_primes : Tries to construct model with good reduction at certain primes

// canonic_degs : Can compute models with extra defining equations

// mod_para : Computes the modular parametrisation map to an optimal elliptic curve

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

///////////////
/// canonic ///
///////////////

// B is a sequence of cusp forms.
// Computes the canonical embedding.
canonic := function(B);
    N := Level(B[1]);
    prec := 5*N;
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsIrreducible(X) then
			        eqns := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns]; // scale equations
				X:=Curve(ProjectiveSpace(R),eqns); // same curve with scaled equations
				if Genus(X) eq dim then // Can also use ArithmeticGenus as Genus can sometimes stall for some reason, curve smooth so okay
					tf:=true;
				end if;
			end if;
		end if;
	end while;

    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];
    indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

	for eqn in eqns do
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound for Gamma_0(N)
	    Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
		assert Valuation(Evaluate(eqn,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.

 return(X);
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// simul_diag /// (auxiliary function)
//////////////////

// This is an auxiliary function for later code.

// Input: A sequence of matrices that are involutions
// Output: The matrix T that simultaneuosly diagonalised them and the diagonalised matrices.

simul_diag := function(seqw);
    n := NumberOfRows(seqw[1]);
    Vs := [VectorSpace(Rationals(),n)];

    for w in seqw do
        NVs := [];
        for U in Vs do
            BU := Basis(U);
            N1 := Nullspace(w-1) meet U;
            N2 := Nullspace(w+1) meet U;
            NVs := NVs cat [N1,N2];
            Vs := NVs;
        end for;
     end for;

     new_basis := &cat[Basis(V) : V in NVs | Dimension(V) gt 0];
     T := Matrix(new_basis);
     new_als := [T*w*T^(-1) : w in seqw];
     return T, new_als;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////
/// all_diag_basis ///
//////////////////////

// Input: N
// Output: - A basis for the cusp forms of level N for which all AL involutions act as diagonal matrices
// - the matrices of the AL involutions (listed in ascending order by AL index)

all_diag_basis := function(N);
    C := CuspForms(N);
    g := Dimension(C);

    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    al_invols := [AtkinLehnerOperator(C,d) : d in al_inds];

    T, new_als := simul_diag(al_invols);
    B := Basis(C);
    cleardenom := LCM([Denominator(x) : x in Eltseq(T)]);
    NB := [&+[cleardenom*T[i,j]*B[j] : j in [1..g]] : i in [1..g]];
    // Optional code to swap the basis "blocks" if the level is prime
    //if IsPrime(N) then
    //    diag := [(T*al_invols[1]*T^(-1))[i,i] : i in [1..g]];
    //    ind := Index(diag, -1);
    //    NB := [NB[i] : i in [ind..g]] cat [NB[i] : i in [1..ind-1]];
    //end if;
    return NB, new_als;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// all_diag_X ///
//////////////////

// Input: N
// Output:
// - A model for X_0(N) with all the Atkin-Lehner involutions diagonalised
// - the Atkin-Lehner involutions (listed in ascending order by index)
// - basis of cuspforms used
// - The infinity cusp (as a rational point)

// X_0(N) should be of genus > 1 and non-hyperelliptic.

all_diag_X := function(N);
    NB, new_als := all_diag_basis(N);
    X:=canonic(NB);
    A<[x]> := AmbientSpace(X);
    g := Dimension(A)+1;

    als_X := [ iso<X->X | [w[i,i]*x[i] : i in [1..g]], [w[i,i]*x[i] : i in [1..g]]>  : w in new_als];

    cusp_seq := [];
    for f in NB do
        if Coefficient(f,1) ne 0 then
            cusp_seq := cusp_seq cat [1];
        else cusp_seq := cusp_seq cat [0];
        end if;
    end for;
    cusp := X ! cusp_seq;
    return X, als_X, NB, cusp;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////////////////////
/// Hyperelliptic quotient data ///
///////////////////////////////////

// Star quotients
// If N is in this list, the star quotient of X_0(N) is hyperelliptic curve of genus > 2.
// Taken from Theorem 2 of Furemoto--Hasegawa 1999
hyper_stars := [136, 171, 176, 207, 252, 279, 315];

// Non-star quotients (genus >2)
// First entry of the tuple is N
// Second entry is the indices of the Atkin-Lehner involutions that we quotient out by (listed in ascending order)
// Includes all data for different ways of writing the same group
// e.g. <78, [2,3,6]> and <78, [2,3]> correspond to the same curve and are both included.
// Taken from Theorems 3 and 4 of Furemoto--Hasegawa 1999
hyper_data :=  [
<46, [2]>,
<51, [3]>,
<55, [5]>,
<56, [8]>,
<60, [4]>, <60, [12]>, <60, [60]>,
<62, [2]>,
<66, [6]>, <66, [66]>,
<69, [3]>,
<70, [10]>, <70, [14]>,
<78, [6]>, <78, [26]>, <78, [2,3,6]>, <78, [2,3]>, <78, [2,6]>, <78, [3,6]>, <78, [6,13,39]>, <78, [6,13]>, <78, [6,39]>, <78, [13,39]>,
<85, [85]>,
<87, [3]>,
<92, [4]>, <92, [92]>,
<94, [2]>, <94, [94]>,
<95, [5]>, <95, [19]>,
<105, [3,5,15]>, <105, [3,5]>, <105, [3,15]>, <105, [5,15]>, <105, [3,7,21]>, <105, [3,7]>, <105, [3,21]>, <105, [7,21]>, <105, [7,15,105]>, <105, [7,15]>, <105, [7, 105]>, <105, [15, 105]>,
<110, [2,5,10]>, <110, [2,5]>, <110, [2,10]>, <110, [5,10]>, <110, [2,11,22]>, <110, [2,11]>, <110, [2,22]>, <110, [11,22]>, <110, [5,22,110]>, <110, [5,22]>, <110, [5, 110]>, <110, [22, 110]>,
<119, [7]>, <119, [17]>,
<63, [9]>,
<72, [9]>,
<104, [104]>,
<120, [5,24,120]>, <120, [5,24]>, <120, [5,120]>, <120, [24,120]>,
<126, [7,9,63]>, <126, [7,9]>, <126, [7,63]>, <126, [9,63]>, <126, [9,14,126]>, <126, [9,14]>, <126, [9,126]>, <126, [14,126]>,
<168, [21, 24, 56]>, <168, [21,24]>, <168, [21,56]>, <168, [24,56]>
];

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// genus_quo ///
/////////////////

// Input: N and a sequence of AL indices (in ascending order)
// Output: The genus of the corresponding quotient of X_0(N)

// X_0(N) should be of genus > 0.

genus_quo := function(N, seq_al);
    C := CuspForms(N);
    g := Dimension(C);
    // start by simply diagonalising all AL involutions
    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    al_invols := [AtkinLehnerOperator(C,d) : d in al_inds];
    T, new_als := simul_diag(al_invols);
    // pick out those corresponding to seq_al
    seqw_M := [new_als[i] : i in [1..#new_als] | al_inds[i] in seq_al];
    Ss := [Diagonal(Mw) : Mw in seqw_M];
    n := #Ss[1];
    gen_seq := [1 : i in [1..n] | &+[s[i] : s in Ss] eq #Ss];
    if IsNull(gen_seq) then
        g_quo := 0;
    else g_quo := &+gen_seq;
    end if;
    return g_quo;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////////////
/// atkinlehnersubgrp /// (Shiva)
/////////////////////////

// Input: The level N, and a list of Hall divisors of N representing the corresponding Atkin-Lehner involutions.
// Output: The list of all (non-trivial) Hall divisors of N corresponding to all the Atkin-Lehner involutions in the subgroup generated.

function atkinlehnersubgrp(N,seq);
	boo := true;
	subgrp := seq;
	while boo do
		for a in subgrp do
			for b in subgrp do
				c := ExactQuotient(a*b,GCD(a,b)^2);
				if c ne 1 and not c in subgrp then
					Append(~subgrp,c);
					boo := true;
					break a;
				end if;
			end for;
			boo := false;
		end for;
	end while;
	return Sort(subgrp);
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
/// is_hyper_quo ///
////////////////////

// Input: N and a sequence of AL indices
// Output: true or false according to whether the quotient is hyperelliptic or not.

// X_0(N) should be of genus > 0 and non-hyperelliptic.

is_hyper_quo := function(N, seq_al);
    g_quo := genus_quo(N,seq_al);
        if g_quo eq 2 then
           is_hyp := true;
        elif g_quo gt 2 and N in hyper_stars then
            al_group := atkinlehnersubgrp(N,seq_al);
            if #al_group eq 2^(#PrimeFactors(N))-1 then
                is_hyp := true;
            elif <N, seq_al> in hyper_data then
                is_hyp := true;
            else is_hyp := false;
            end if;
        elif g_quo gt 2 and <N, seq_al> in hyper_data then
            is_hyp := true;
        else is_hyp := false;
        end if;
    return is_hyp;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
/// eqs_quos ///
////////////////

// Input: N and a sequence of sequences of Atkin-Lehner indices
// (each sequence of indices should be given in ascending order by index)
// Output:
// - A model for X_0(N), with all the Atkin-Lehner involutions diagonalised when X_0(N) is non-hyperelliptic of genus > 1
// - The Atkin-Lehner involutions on X_0(N) (listed in ascending order by index) (diagonalised if X_0(N) is non-hyperelliptic of genus > 1)
// - A list: for each sequence of AL-indices, a tuple consisting of the corresponding quotient curve and the map to the quotient curve
// - The basis of cuspforms used for the canonical embedding of X when X_0(N) is non-hyperelliptic of genus > 1, otherwise the q-expansions of generators are given
// - the infinity cusp on X (as a rational point)

// If X_0(N) has genus 0 or 1, then pairs will be empty

// auxiliary function to compare the size of two sets

size_comp := function(s1,s2);
    if #s1 gt #s2 then return 1;
    elif #s1 lt #s2 then return -1;
    else return 0; end if;
end function;

eqs_quos := function(N, list_als);
    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then
        X := SmallModularCurve(N);
        al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
        ws := [AtkinLehnerInvolution(X,N,d) : d in al_inds];
        pairs := [* *];
        if Genus(X) gt 1 then
            for seq_al in list_als do
                seqw := [ws[i] : i in [1..#ws] | al_inds[i] in seq_al];
                Y, rho := CurveQuotient(AutomorphismGroup(X,seqw));
                pairs := pairs cat [* <Y, rho> *];
            end for;
        end if;

        L<q> := LaurentSeriesRing(Rationals());
        NB := qExpansionsOfGenerators(N, L, 5*N);
        cusp := Cusp(X, N, N);
        return X, ws, pairs, NB, cusp;
    end if;
    // Now consider case in which X is canonically embedded
    X, ws,NB,cusp := all_diag_X(N);
    A<[x]> := AmbientSpace(X);
    al_inds := [ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    pairs := [* *];
    for seq_al in list_als do
        seqw := [ws[i] : i in [1..#ws] | al_inds[i] in seq_al];
        seqw_M := [Matrix(w) : w in seqw];
        Ss := [Diagonal(Mw) : Mw in seqw_M];
        n := #Ss[1];
        g_quo := genus_quo(N, seq_al);
        is_hyp := is_hyper_quo(N, seq_al);

        PS0 := SetToSequence(Subsets({1..n}));

        if g_quo gt 1 and is_hyp eq false then // can use canonical embeding for quotient curve.
             pos_coords := &meet[{P : P in PS0 | #P gt 0 and &+[s[i] : i in P] eq #P} : s in Ss];
             pos_seq := SetToSequence(pos_coords);
             sizes := [#c : c in pos_seq];
             _,position := Maximum(sizes);
             coords := Sort(SetToSequence(pos_seq[position]));
             Bpl := [NB[i] : i in coords];
             Y := canonic(Bpl);
             rho := map< X ->Y | [x[i] : i in coords] >;
             pairs := pairs cat [* <Y, rho> *];

        else                           // cannot use canonical embedding for quotient curve
                                       // we use a projection map instead (if possible)
                                       // quotient is either elliptic or hyperelliptic or genus 0
            PS := [P : P in PS0 | #P gt 1];
            consts := &meet[{P : P in PS | &+[s[i] : i in P] eq #P or &+[s[i] : i in P] eq -#P} : s in Ss];
            con := SetToSequence(consts);
            con3 := [c : c in con | #c gt 2];
            maxcon3 := con3;
            for s,e in con3 do
                if s subset e and s ne e then
                    Exclude(~maxcon3,s);
                end if;
            end for;
            maxcon3 := Sort(maxcon3, size_comp);
            genY1 := -1;
            for i in [1..#maxcon3] do
                coords := Sort(SetToSequence(maxcon3[i]));
                P := ProjectiveSpace(Rationals(),#coords-1);
                proj := map<A->P|[x[i] : i in coords]>;
                Y1 := Curve(proj(X));
                genY1 := Genus(Y1);
                if genY1 eq g_quo then
                    assert Dimension(Y1) eq 1 and IsIrreducible(Y1);
                    Y := Y1;
                    genY := genY1;
                    rho1 := map<X->Y | [x[i] : i in coords]>;
                    break;
                end if;
            end for;
            if genY1 ne g_quo then
                Y, rho1 := CurveQuotient(AutomorphismGroup(X,seqw));  // longer, only used if projection map does not work.
                assert Dimension(Y) eq 1 and IsIrreducible(Y);
                genY := Genus(Y);
            end if;

            if  genY gt 1 then // curve is hyperelliptic
                 htf, Z, rho2 := IsHyperelliptic(Y);
                 assert htf;
                 H, rho3 := SimplifiedModel(Z);
                 rho := rho1*rho2*rho3;
                 pairs := pairs cat [* <H,rho>*];
             elif genY eq 0 then
                 assert Degree(rho1) eq #AutomorphismGroup(X,seqw); // make sure we haven't quotiented out by anything extra
                 pairs := pairs cat [* <Y, rho1>*];
             else assert Genus(Y) eq 1 and g_quo eq 1;
                 assert Degree(rho1) eq #AutomorphismGroup(X,seqw); // make sure we haven't quotiented out by an extra isogeny
                 Z, rho2 := EllipticCurve(Y,rho1(cusp));
                 E, rho3 := SimplifiedModel(Z);
                 rho := rho1*rho2*rho3;
                 assert IsZero(N mod Conductor(E));
                 pairs := pairs cat [*< E, rho >*];
             end if;
        end if;
    end for;

    return X, ws, pairs, NB, cusp;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////////////
/// is_bi_hyperelliptic /// (Filip)
///////////////////////////

// checks whether X_0(n) has a degree 2 map to a hyperlliptic curve
is_bihyperelliptic:=function(n);
lst:= Divisors(n) ;
lst2:=[];
for a in lst do
if GCD(a, n div a) eq 1 then lst2:=lst2 cat [a]; end if;
end for;
tr:=false;
for w in lst2 do
if w ge 2 then
if (is_hyper_quo(n,[w])) then return true, w, genus_quo(n,[w]); end if;
end if;
end for;
return false;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// genera_quo /// (Filip)
//////////////////

// returns the genera of all X_0(n)/w_d

genera_quo:=procedure(n);
lst:= Divisors(n) ;
lst2:=[];
for a in lst do
if GCD(a, n div a) eq 1 then lst2:=lst2 cat [a]; end if;
end for;
for w in lst2 do
if w ge 2 then
w, genus_quo(n,[w]);
end if;
end for;
end procedure;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
/// Examples ///
////////////////

/*

// Example 1 //

// 1a)
// Let's start by computing a model for X074.
// There are 3 AL involutions.
// We compute them, but we do not compute any quotient information.

time X, ws, pairs, NB, cusp := eqs_quos(74,[]);  // 0.6 seconds

// pairs is an empty list.
// NB is the basis of cusp forms we have used for the canonical embedding.
// cusp is the infinty cusp.


// 1b) This time we compute the quotients by each involution

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2],[37],[74]]);  // 1.5 seconds

// pairs consist of three tuples of a curve and a map
// the first curve is X_0(74) / w_2

Y := pairs[1][1];
assert Genus(Y) eq 4;
rho := pairs[1][2];
PointSearch(Y,1000); // we find 3 rational points

// the third curve is X_0(74) / w_74.
// it is hyperelliptic.

Y := pairs[3][1]; // Hyperelliptic Curve defined by y^2 = x^6 - 2*x^5 - x^4 - x^2 - 2*x + 1
assert Genus(Y) eq 2;
Pts := Points(Y : Bound := 1000); // we find 6 rational points.
// the curve has rank 1 and genus 2
// we should be able to check that this gives all the rational points.
// let's do this.
J := Jacobian(Y);
G := J ! [Pts[1],Pts[6]];
Order(G); // this is 3, so the point has finite order...
// let's pick another point in the Jacobian
G := J ! [Pts[1],Pts[5]];
assert Order(G) eq 0;
assert #Chabauty(G) eq 6;  // we have found all the rational points.

// 1c)  This time we quotient by the full group of Atkin-Lehner involutions.

time X, ws, pairs, NB, cusp := eqs_quos(74,[[2,37]]);  // 1.2 seconds

// this time the quotient curve is an elliptic curve

assert Conductor(pairs[1][1]) eq 37;

rho := pairs[1][2]; // this is the quotient map
// the quotient map is given by a composition of 3 different maps in this case
// if we would like a single map, then we can define
phi := Expand(rho);


// replacing [2,37] by [2,74] or [37,74] or [2,37,74] will give the same output
// (since the group generated by the AL involutions is a C2 x C2.

/////////////////////////////////////////////////////////////////////////////////

// Example 2 //

// We'll try X_0(136) now
// 136 = 8*17

time X, ws, pairs, NB, cusp := eqs_quos(136,[[ 8,17,136 ]]);  // 10 seconds

assert Genus(X) eq 15; // this is quite high, so it took a little longer.
Y := pairs[1][1]; // Hyperelliptic Curve defined by y^2 = x^8 - 6*x^6 - 4*x^5 + x^4 + 4*x^3 + 20*x^2 + 16*x
// this is a genus 3 hyperelliptic curve as expected.

// We can look at an intermediate curve too

time X, ws, pairs, NB, cusp := eqs_quos(136,[[ 8 ]]);  // 9 seconds
Y := pairs[1][1];
assert Genus(Y) eq 7;

// Example 3 //

// Here is an example with X_0(p).
// We'll do p = 163

time X, ws, pairs, NB, cusp := eqs_quos(163,[[ 163 ]]);  // 53 seconds, quite long
assert Genus(X) eq 13;
Y := pairs[1][1];
assert Genus(Y) eq 6;
// The part that takes a long time is computing the model for X_0(163) in this case
// Once this is done the rest is fast.
time X := all_diag_X(163); // 53 seconds
// although if you run this code a second time it is much faster (4 seconds) due to some stored computations

// Example 4 //

// An example with a larger group of automorphisms.

time X, ws, pairs, NB, cusp := eqs_quos(60,[[3],[4],[5],[3,4],[4,5],[3,5],[3,4,5]]); // 5 seconds

Y := pairs[7][1];
assert Genus(Y) eq 0;  // we have a genus 0 quotient here

for pair in pairs do
    Y := pair[1];
    Genus(Y);
    if Genus(Y) eq 1 then
       Conductor(Y);
    end if;
end for;
// We get 4,3,4,2,1,1,0 for the genera
// The two elliptic curves have conductors 30 and 20 (which is as expected).

// Example 5 //

// We do a prime power level

time X, ws, pairs, NB, cusp := eqs_quos(125,[[125]]); // 1 second

Y := pairs[1][1]; // Hyperelliptic Curve defined by y^2 = x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 8*x+ 1
assert Genus(Y) eq 2;

// Example 6 //

// Let's check a model against Galbraith's calculations for a non-hyperelliptic quotient
// (It is easier to check with hyperelliptic quotients)

time X, ws, pairs, NB, cusp := eqs_quos(169,[[169]]);  // 1 second
Y := pairs[1][1];
// this matches Galbraith's model exactly in this case.

// Example 7 //

// Here is an example with X_0(N) hyperelliptic.
// In this case we just use the SmallModularCurve package functionalities

time X, ws, pairs, NB, cusp := eqs_quos(28, [[4], [7], [28], [4,28]]);

*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++


///////////////////////////////////////////////////////
////////////////// FURTHER FUNCTIONS //////////////////
///////////////////////////////////////////////////////

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////////
/// change_basis_mat ///
////////////////////////

// Input: bases B and NB for the same space of cusp forms
// Output: Change of basis matrix from one to the other
// (where space of cusp forms is viewed as a Vector space)

change_basis_mat := function(B, NB);
    C := CuspForms(Level(B[1]));
    V,phi,psi := RSpace(C);
    BV := [psi(b) : b in B];
    NBV := [psi(nb) : nb in NB];
    M := ChangeRing(Matrix(BV), Rationals());
    NM := ChangeRing(Matrix(NBV), Rationals());
    T := M*NM^(-1);
    return T;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// coeff_mat ///
/////////////////

// Input: basis B for a space of cusp forms, m = number of coefficients to consider
// Output: matrix of coefficients up to m

coeff_mat := function(B, m);
    return Matrix([ [Coefficient(f,i) : i in [1..m]] : f in B]);
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////////
/// apply_basis_change ///
//////////////////////////

// Input: A basis B and a change of basis matrix M with integer coefficients
// Output: New basis NB obtained by applying the change of basis matrix to B
// (where space of cusp forms is viewed as a Vector space)

apply_basis_change := function(B, M);
    C := CuspForms(Level(B[1]));
    V,phi,psi := RSpace(C);
    BV := [psi(b) : b in B];
    mat_BV := ChangeRing(Matrix(BV),Rationals());
    M := ChangeRing(M, Rationals());
    new_mat:= mat_BV*M;
    new_mat_list := [new_mat[i] : i in [1..Degree(new_mat[1])]];
    NB := [phi(b) : b in new_mat_list];
    return NB;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
/// coord_change ///
////////////////////

// Input: bases B and NB for the same space of cusp forms
// Output: curves X and NX corresponding to these bases and the coordinate change map between the curves
// The level N should be such that X_0(N) is non-hyperelliptic of genus > 2.
// The basis B should be a 'nice' basis for which one can compute the canonical embedding in a reasonable time

coord_change := function(B, NB);
    X := canonic(B);
    T := change_basis_mat(B,NB);
    A<[x]> := AmbientSpace(X);
    var := Dimension(A)+1;
    R<[x]> := PolynomialRing(Rationals(), var);
    eqX := DefiningEquations(X);
    coord_change_eqs := [&+[(T^(-1))[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    coord_change_eqs_inv := [&+[T[i,j]*x[j] : j in [1..var]] : i in [1..var]];
    coord_change_R := hom<R->R | coord_change_eqs_inv >;

    new_eqX := [coord_change_R(ee) : ee in eqX];
    NX := Curve(ProjectiveSpace(R),new_eqX);
    coord_change_map := map< X -> NX | coord_change_eqs>;
    return X, NX, coord_change_map;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////
/// level_basis ///
///////////////////

// Input: N and M
// Output: a basis for the cusp forms at level N.
// N must be divisible by M
// The code chooses a diagonalised basis for the cusp forms at level M
// and extends this to a basis at level N
// ( uses the inclusion (S_2(M) -> S_2(N)) )

level_basis := function(N, M);
    CN := CuspForms(N);
    V,phi,psi := RSpace(CN);
    BM := all_diag_basis(M); // diagonal basis of cusp forms at level M
    U := sub<V | [psi(f) : f in BM]>; // corresponding subspace
    BU := [psi(bb) : bb in BM];
    VQ := ChangeRing(V, Rationals());
    UQ := ChangeRing(U, Rationals());
    BUQ := [UQ ! bb : bb in BU];
    BVQ := ExtendBasis(BUQ, VQ);
    denom := Denominator(Matrix(BVQ));
    BV := [  V ! [denom*bb[i] : i in [1..Dimension(VQ)]] : bb in BVQ];
    BNM := [phi(bb) : bb in BV];
    return BNM, BM;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////
/// level_quo   ///
///////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N), M divides N
// Output:
// - A map from X = X_0(N) to X_0(M)
// - The curve X_0(M)
// - A different model for X_0(N) for which the quotient map is just a projection map
// - The change of coordinate map from the current model to the new model
// - The quotient (projection) map from the new model to the quotient curve

// X_0(N) and X_0(M) must both be of genus > 2 and non-hyperelliptic.
// I am looking to see what can be done in the quotient is an elliptic curve or hyperelliptic.

level_quo := function(X, N, M);
    BNM, BM := level_basis(N, M);
    B := all_diag_basis(N);
    _, Xl , coord := coord_change(B, BNM);
    XM := canonic(BM);
    A<[x]> := AmbientSpace(Xl);
    proj := map< Xl-> XM | [x[i] : i in [1..#BM]] >;
    phi := map< X -> XM | DefiningEquations(Expand(coord*proj)) >;
    return phi, XM, Xl, coord, proj;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/*

///////////////
/// Example /// (see above for examples of using eqs_quo)
/////////////// (here we see how to use level_quo)

// We will consider an example with N = 86 and M = 43.
// The curve X_0(43) is non-hyperelliptic of genus 3.
// the curve X_0(86) is non-hyperelliptic of genus 10.

time X, ws, pairs, NB, cusp := eqs_quos(86,[[2], [43], [86], [2,43]]); // 4 seconds

// This gives us the curve X_0(86) as well as 4 quotients.
// The first 3 quotients are by individual AL involutions
// The fourth is by the full AL group

// We now want the map to X_0(43) too.

time phi, X_0_43, Xl, coord, proj := level_quo(X, 86, 43); // 1.8 seconds

phi; // we get nice equations for phi

// Mapping from: Crv: X to Crv: X_0_43
// with equations :
// 1/2*x[1] + 1/2*x[6] - 2*x[7] - x[8]
// 1/2*x[2] + x[3] + 1/2*x[9] - x[10]
// 1/2*x[3] - 1/2*x[4] + x[5] + 1/2*x[10]

time assert Degree(phi) eq 3; // 3.5 seconds, sanity check

X_0_43; // we get nice equations for the quotient curve too

// Curve over Rational Field defined by x[1]^4 + 2*x[1]^2*x[2]^2 + 8*x[1]^2*x[2]*x[3] + 16*x[1]^2*x[3]^2 - 3*x[2]^4 + 8*x[2]^3*x[3] + 16*x[2]^2*x[3]^2 + 48*x[2]*x[3]^3 + 64*x[3]^4


// Xl is a different model for X_0(86)
// it's equations are more complicated
// The quotient map, proj, to X_0(43) is just a projection map though
// So it could be easier to work with for certain things
// The coord map allows us to pass from one model to the other

// The map phi can be used to compute the j-invariant of a point on X_0(86)
// by passing to X_0(43), as the j-map factors via phi.

*/





////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////
//// jmap //////
////////////////

// Input: X, N
// X is a diagonalised model for X_0(N) when X is non-hyperelliptic of Genus > 1. Otherwise X is the small modular curve model.
// Output: Equations for the j-map as a map to P^1, a tuple of its numerator and denominator

// When X is non-hyperelliptic of genus > 1 it should be obtained from all_diag_X or eqs_quos
// If you want to run this code using a different model for X of this type then you can by changing the first few lines appropriately

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse

// An auxiliary function to help simplify matrices using LLL reduction

function nicefy(M)
  M0, T := EchelonForm(M);
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  AA := Saturation(M2);
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  newlatbasismat, change := LLL(AA : Proof := false);
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

/////////////////////////////////////////////////////////

// An auxiliary function to find q-expansion relations

// Input:
// L = Laurent series ring
// B = Basis of cusp forms
// Bexp = cusp form expansions in L up to prec
// N = Level of cusp forms
// f = cusp form
// degf = degree as map to P1
// maxd = RR parameter
// prec = precision
// maxprec = precision + 1
// g = #Bexp = genus of X_0(N)

find_rels := function(L, B, Bexp, N, f, degf, maxd, prec, maxprec, g);
    val := Valuation(f);
    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];
    canring := [ <Bexp,vars>];
    for d in [2..maxd] do
        dimen := (2*d-1)*(g-1);
        fouriermat := ZeroMatrix(Rationals(),0,(maxprec-1));
        prds := [ <i,j> : i in [1..g], j in [1..#canring[d-1][1]]];
        done := false;
        curind := 1;
        newfourier := [];
        newvars := [];
        while (done eq false) do
            e1 := prds[curind][1];
            e2 := prds[curind][2];
            pp := Bexp[e1]*canring[d-1][1][e2];
            vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [d..d+maxprec-2]];
            tempfouriermat := VerticalJoin(fouriermat,Matrix(Rationals(),1,(maxprec-1),vecseq));
            if Rank(tempfouriermat) eq NumberOfRows(tempfouriermat) then
                fouriermat := tempfouriermat;
                Append(~newfourier,pp);
                Append(~newvars,canring[1][2][e1]*canring[d-1][2][e2]);
                if NumberOfRows(tempfouriermat) eq dimen then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
            if (done eq false) then
                curind := curind + 1;
                if (curind gt #prds) then
                    done := true;
	                Append(~canring,<newfourier,newvars>);
                end if;
            end if;
        end while;
    end for;

    fmat := ZeroMatrix(Rationals(),0,(maxprec-2));
    for i in [1..#canring[maxd][1]] do
        pp := f*canring[maxd][1][i];
        vecseq := &cat[ Eltseq(Coefficient(pp,j)) : j in [maxd+val..maxd+val+maxprec-3]];
        fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));
    end for;
    for j in [1..#canring[maxd][1]] do
        vecseq := &cat[ Eltseq(-Coefficient(canring[maxd][1][j],i)) : i in [maxd+val..maxd+val+maxprec-3]];
        fmat := VerticalJoin(fmat,Matrix(Rationals(),1,(maxprec-2),vecseq));
    end for;

    NN1 := NullSpace(fmat);
    M1 := Matrix(Basis(NN1));
    cb1 := nicefy(M1);
    fsol := (cb1*M1)[1];

    felt := &+[ fsol[i+#canring[maxd][1]]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]]/&+[ fsol[i]*canring[maxd][2][i] : i in [1..#canring[maxd][1]]];

    num := Numerator(felt);
    denom := Denominator(felt);

    // checks for correctness

    deg_bd := (2*g-2)*maxd;
    prec_bd := Integers() ! (deg_bd + degf + 1);

    if prec lt prec_bd then
        NewBexp := [L!qExpansion(B[i],prec_bd) : i in [1..g]]; // increase precision up to bound
    else NewBexp := Bexp;
    end if;

    mfnum := Evaluate(num,NewBexp);
    mfdenom := Evaluate(denom,NewBexp);
    elt := (mfnum/mfdenom) - f;
    assert IsWeaklyZero(elt); // If this fails then try increasing precision to >5N

    return num, denom;
end function;

///////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////

jmap := function(X, N);
    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then
        jj := jInvariant(X,N);
        num := Numerator(jj);
        denom := Denominator(jj);
        jmap := map<X -> ProjectiveSpace(Rationals(),1) | [num, denom] >;
        return jmap, <num, denom>;
    end if;
    // Now consider case in which X is canonically embedded

    B := all_diag_basis(N);
    g := #B;
    prec := 5*N;
    maxprec := prec+1;

    L<q> := LaurentSeriesRing(Rationals());

    E4 := Eisenstein(4,q : Precision := prec);
    E6 := Eisenstein(6,q : Precision := prec);
    j := 1728*E4^3/(E4^3 - E6^2);
    val := Valuation(j);
    degj := N*(&*[1+1/p : p in PrimeFactors(N)]);

    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];

    r := Ceiling((degj / (2*(g-1))) + 1/2); // When degj / 2g-1 +1/2 is an integer, we should really take this +1, but for N < 200 I found that this worked in these cases (and is slightly nicer) so I will stick with it. For the other functions, we do need and take the +1 in these cases.

    num, denom := find_rels(L, B, Bexp, N, j, degj, r, prec, maxprec, g);

    jmap := map<X -> ProjectiveSpace(Rationals(),1)|[num,denom]>;

    return jmap, <num,denom>;

end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////////////
//// compute_cusps //////
/////////////////////////

// Input:
//- X (obtained from eqs_quos)
//- N
//- (OPTION A) ws, the Atkin--Lehner involutions on X (obtained from eqs_quos for example)
//- (OPTION A) cusp, the infinty cusp on X (obtained from eqs_quos for example)
//- (OPTION B) num_denom (obtained as the second output of the jmap function)
// Optional argument: use_jmap. Default = false. Set to true to work with jmap even in squarefree case.

// Output: Sequence of places corresponding to the cusps of X_0(N)

// If N is squarefree, then AL involutions act transitively on the cusps
// In this case it is usually faster to provide a cusp and the AL involutions
// otherwise the code works with the j-map
// X should be non-hyperelliptic of genus > 2.

compute_cusps := function(X, N, ws, cusp, num_denom: use_jmap := false);
    if IsSquarefree(N) and use_jmap eq false then
       cusps := SetToSequence({Place(cusp)} join {Place(w(cusp)) : w in ws});
       return cusps;
    end if;
    A<[x]> := AmbientSpace(X);
    g := Dimension(A) + 1;
    KX := FunctionField(X);
    KXgens:=[KX!(x[i]/x[g]) : i in [1..(g-1)]] cat [KX!1];
    num := num_denom[1];
    denom := num_denom[2];
    numK := Evaluate(num,KXgens);
    denomK:=Evaluate(denom,KXgens);
    cusps := Poles(numK/denomK);
    return cusps;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// Example 1 /// (here we see how to use jmap)
/////////////////

// We will compute equations for the j-map on X_0(67)

/*

X, ws, _, _, cusp := eqs_quos(67, []);

time j, num_denom := jmap(X,67);  // 6 seconds

pts := PointSearch(X,10);
for p in pts do
    j(p);
end for;

// we see that we have two cusps and one point with j-invariant -147197952000 = -2^15 3^3 5^3 11^3
// this is as expected

// we can also compute the cusps using the compute_cusps function.
// since 67 is squarefree, this is immediate
// For the 5th input parameter, we just use an empty sequence (anything is fine here)

time cusps := compute_cusps(X, 67, ws, cusp, []); // 0.04 seconds

// We have two degree 1 places
// [ Place at (-1 : 0 : 1 : 0 : 0), Place at (1 : 0 : 1 : 0 : 0)]

/////////////////
/// Example 2 ///
/////////////////

// We will compute equations for the j-map on X_0(60)

X, ws, _, _, cusp := eqs_quos(60, []);

time j, num_denom := jmap(X,60);  // 61 seconds

// We compute the cusps
// 60 is not squarefree and we use the j-map
// We just use empty sequences as inputs for the 3rd and 4th parameters

time cusps := compute_cusps(X, 60, [], [], num_denom); // 6 seconds

// We have 12 rational cusps in this case

// This is as expected using the formula for the number of cusps.
assert &+[EulerPhi(GCD(d, Integers() ! (60/d))) : d in Divisors(60)] eq 12;


/////////////////
/// Example 3 ///
/////////////////

// We will compute equations for the j-map on X_0(64)

X, ws, _, _, cusp := eqs_quos(64, []);

time j, num_denom := jmap(X,64);  // 29 seconds

// We compute the cusps
// We just use empty sequences as inputs for the 3rd and 4th parameters

time cusps := compute_cusps(X, 64, [], [], num_denom); // 0.9 seconds

for c in cusps do
    Degree(c);
end for;

// Degrees of fields are: 4, 1, 1, 2, 2, 1, 1
// So we have 12 cusps in total.

// This is as expected using the formula for the number of cusps.
assert &+[EulerPhi(GCD(d, Integers() ! (64/d))) : d in Divisors(64)] eq 12;
*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////////
//// xy_coords ////
/////////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N) (for X_0(N) non-hyperelliptic of Genus > 1)
// X_0(M) must be elliptic or hyperelliptic (see level_quo otherwise)

// If X_0(N) is hyperelliptic, elliptic or genus 0, then the function simply returns the map to X_0(M) and X_0(M)

// Output:
// 1. x-coordinate map as a quotient of polynomials
// 2. y-coordinate map as a quotient of polynomials
// 3. X_0(M) (the small modular curve model obtained from eqs_quos)

// If you want to try and construct the map as a map to X_0(M), or its ambient projective space, then you can do so using the function construct_map_to_quotient which follows this function.
// However, this can be very slow...
// So I prefer to work with these x- and y-maps
// See the examples later for how to use the x- and y-maps to compute the image of points.

// Note that the cusps are in the wrong affine chart to be evaluated at the x- and y-maps

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse

xy_coords := function(X,N,M);

    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then
        Y := eqs_quos(M, []);
        map := ProjectionMap(X,N,Y,M);
        return map, Y;
    end if;

    B := all_diag_basis(N);
    g := #B;
    degN := N*(&*[1+1/p : p in PrimeFactors(N)]);
    degM := M*(&*[1+1/p : p in PrimeFactors(M)]);
    deg_map := Integers() ! (degN / degM);

    prec := 5*N;
    maxprec := prec+1;
    Y := eqs_quos(M, []);

    L<q> := LaurentSeriesRing(Rationals());
    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];
    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];

    qexps := qExpansionsOfGenerators(M, L, prec);
    for f in qexps do
        val := Valuation(f);
        if f eq qexps[1] then
            degf := 2*deg_map;
        else degf := Degree(HyperellipticPolynomials(Y))*deg_map;
        end if;

        r1 := (degf / (2*(g-1))) + 1/2;
        if IsIntegral(r1) then
           r := Integers()! (r1+1);
        else r := Ceiling(r1);
        end if;

        num, denom := find_rels(L, B, Bexp, N, f, degf, r, prec, maxprec, g);

        if f eq qexps[1] then
            xnum := num;
            xdenom := denom;
            xx := xnum / xdenom;
        else ynum := num;
             ydenom := denom;
             yy := ynum / ydenom;
        end if;
    end for;

    return xx, yy, Y;
end function;


///////////////////////////////////
//// construct_map_to_quotient ////
///////////////////////////////////

// As explained above, we can try and construct a map to X_0(M), or its ambient projective space if we really want to.
// The following function takes as input X_0(N), X_0(M), and the x and y expressions from above
// The final input paramter is a true or false Boolean.
// if true then the codomain will be set to X_0(M)
// if false then the codomain will be set to the ambient projective space of X_0(M), this is faster

// Warning! This is very slow / does not terminate in a reasonable time if X_0(M) is hyperelliptic and tf = true
// Do not try and evaluate the map at cusps

construct_map_to_quotient := function(X,Y,xx,yy,tf);
    if tf then
        map := map<X -> Y | [xx,yy,1]>;
    else map := map<X -> AmbientSpace(Y) | [xx,yy,1] >;
    end if;
    return map;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/*

////////////////
/// Examples /// (we see how to work with xy_coords)
////////////////

// We will use the following function, taken from "pullbacks.m" in these examples.
// For convenience we have included the function again here

// Example 1 (elliptic quotient)

N := 85;
M := 17;

al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);  // This is the curve X_0(85)
assert Genus(X) eq 7;

// The curve X_0(17) is an elliptic curve

time xx, yy, E := xy_coords(X,N,M); // 0.9 seconds

// In this case, since X_0(M) is elliptic and the genus of X_0(N) is not too large

// We can construct the map to X_0(M) relatively quickly if we really want to

time Pmap := construct_map_to_quotient(X,E,xx,yy,false); //0.001
Codomain(Pmap); // Projective space of dimension 2 over Rational Field
time Emap := construct_map_to_quotient(X,E,xx,yy,true); // 4.6 seconds
assert Codomain(Emap) eq E;
// However, if we want to work with points, we are best off sticking with the x and y coordinate expressions

// Let's compute some quadratic points on X_0(85) and evaluate our map on them
// We use the "pullback_points" function, available in the "pullbacks.m" file

time pullbacks := pullback_points(X,pairs,N, 10000); // 14 seconds

assert #pullbacks eq 5;

pl := pullbacks[2][1][1]; // this is a quadratic point on X
K<d> := pullbacks[2][2];
assert Discriminant(Integers(K)) eq -4; // So K is the field Q(i)
pl; // (-1/2 : -1/2 : 0 : 1/2*d : -1/2*d : 0 : 1)

EK := ChangeRing(E,K);
ptK := Eltseq(pl);  // Sequence of coordinates of the point
RK := [Evaluate(xx,ptK), Evaluate(yy,ptK), 1];  // The image point
SK := EK ! RK; // the image point on EK is (d + 3 : -4*d - 5 : 1)

// Warning! Trying to base change Emap to K and compute the image directly is too slow
// In this example one can base change Pmap to K and use it
// but in more complicated examples or in the hyperelliptic case it does not work

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Example 2 (hyperelliptic quotient)

// This example will be very similar to Example 1

N := 82;
M := 41;

al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);  // This is the curve X_0(82)
assert Genus(X) eq 9;

// The curve X_0(41) is a hyperelliptic curve of genus 3

time xx, yy, H := xy_coords(X,N,M); // 0.5 seconds

time Pmap := construct_map_to_quotient(X,H,xx,yy,false); // 0.1 seconds

// In this case it is fast to compute the map to weighted projective space

Codomain(Pmap); // Projective Space of dimension 2 over Rational Field with grading 1, 4, 1

// Warning! Do not try to make H the codomain with this example
// It will be too slow

// Again, we use the "pullback_points" function, available in the "pullbacks.m" file to access some quadratic points

time pullbacks := pullback_points(X,pairs,N, 10000); // 7.8 seconds
assert #pullbacks eq 4;

// Let's compute the image of all of these points.

// Warning! Do not try to do this by base changing Pmap to a quadratic field
// it is too slow.
// It is much faster to work with the x- and y-coordinates!

time for pl in pullbacks do  // 0.01 seconds, this is almost instantaneous
    pt := pl[1][1];
    K := pl[2];
    print(Discriminant(Integers(K)));
    HK := BaseChange(H,K);
    ptK := Eltseq(pt);
    RK := [Evaluate(xx,ptK), Evaluate(yy,ptK), 1];
    SK := HK ! RK;
    print(SK);
end for;

// Here is the output
// Note that the fields "K.1" are different for the different points

// -4
// (-1 : K.1 : 1)
// -4
// (1 : -2*K.1 + 1 : 1)
// -4
// (1 : 2*K.1 + 1 : 1)
// -8
// (0 : K.1 : 1)

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Example 3 (large genus hyperelliptic quotient)

N := 118;
M := 59;

time X := eqs_quos(N, []); // 4.7 seconds
assert Genus(X) eq 14;
// X_0(M) is hyperelliptic of genus 5

time xx, yy, H := xy_coords(X,N,M); // 1.4 seconds

// with this larger genus example, we can see how even the map to the ambient projective space is slow
// time Pmap := construct_map_to_quotient(X,H,xx,yy,false); // 193 seconds
// not only is constructing the map slow, but trying to evaluate it at points would be slow too
// it is best to stick with the x and y expressions as in Examples 1 and 2

*/


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////
//// gen_0_quo ///// // see xy_coords and level_quo for other level quotients
////////////////////

// Input: X, N, M
// X is a diagonalised model for X_0(N) for X non-hyperelliptic of Genus > 1.
// X_0(M) is a genus 0 modular curve

// If X_0(N) is hyperelliptic, elliptic or genus 0, then the function simply returns the map to X_0(M) and X_0(M)

// Output: Equations for the map X_0(N) -> X_0(M) = P^1 and a tuple of its numerator and denominator, and the curve X_0(M)

// X should be obtained from all_diag_X or eqs_quos
// If you want to run this code using a different model for X of this type then you can by changing the first few lines appropriately

// The following code is adapted from code sent to me (Philippe) by Jeremy Rouse


gen_0_quo := function(X, N, M);

    // Start with case in which X_0(N) is genus 0, elliptic or hyperelliptic.
    if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [ 11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then
        Y := eqs_quos(M, []);
        map := ProjectionMap(X,N,Y,M);
        return map, Y;
    end if;


    B := all_diag_basis(N);
    g := #B;
    prec := 5*N;
    maxprec := prec+1;

    degN := N*(&*[1+1/p : p in PrimeFactors(N)]);
    degM := M*(&*[1+1/p : p in PrimeFactors(M)]);
    degf := Integers() ! (degN / degM);

    L<q> := LaurentSeriesRing(Rationals());
    Y := eqs_quos(M, []);
    assert Genus(Y) eq 0;

    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];
    f := qExpansionsOfGenerators(M, L, prec)[1];
    val := Valuation(f);
    r1 := (degf / (2*(g-1))) + 1/2;
    if IsIntegral(r1) then
       r := Integers()! (r1+1);
    else r := Ceiling(r1);
    end if;

    num, denom := find_rels(L, B, Bexp, N, f, degf, r, prec, maxprec, g);

    fmap := map<X -> Y|[num,denom]>;
    return fmap, <num, denom>, Y;
end function;

////////////////////////////////////////////////////////////////////////////////

/*

// Example:

X := eqs_quos(111,[]); // This is a genus 11 curve
time map, tup, Y := gen_0_quo(X, 111, 3); // 3.1 seconds
// The map should have degree:
// Index of Gamma_0(N) divided by index of Gamma_0(M), which is

111*(&*[1+1/p : p in PrimeFactors(111)]) / (3*(&*[1+1/p : p in PrimeFactors(3)]));  // this is 38

// It takes a while, but we can check that the map does indeed have the right degree

time assert Degree(map) eq 38; // 22 seconds

*/


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////


///////////////////////
//// is_nonsing_p /////
//////////////////////

// Input: X, N, p, R or []
// X is a smooth model for X_0(N) from canonical embedding, p is a prime, R is any rational point on X, if no point provided, set to []
// e.g. R is the infinity cusp obtained from eqs_quos

// true if X is nonsingular mod p, false if X is singular mod p

// Note: if a point R is supplied then we check geometric integrality by ensuring X_p is smooth at R_p
// otherwise we generate a random point on X_p (which takes more time).

// ALTERNATIVE IF NO POINT IS SUPPLIED it is easy to supply a point so this is really not necessary, and the current method of producing a random point works quickly too with the curves X_0(N), but anyway, for completeness...
// The reason for obtaining a smooth point on X_F_p is to check X_F_p (and its smooth completion / normalisation) are geometrically integral
// It is usually faster to check that X_F_p is geometrically integral using FieldOfGeometricIrreducibility;
// (this works by checking the algebraic closure of F_p in the function field is F_p itself)
// If X_F_p is geometrically integral, then its normalisation will be too and we can apply the same conclusions

is_nonsing_p := function(X, N, p, R);
    if IsZero(N mod p) then
        return false;
    end if;
    Xp := ChangeRing(X,GF(p));
    if Dimension(Xp) ge 2 then
        return false;
    end if;
    if IsIrreducible(Xp) eq false then
        return false;
    end if;
    if IsReduced(Xp) eq false then
        return false;
    end if;
    // Now know the curve is integral. We check the genus condition.
    if Genus(Xp) ne Genus(Gamma0(N)) then // Genus(Gamma_0(N)) is the genus of X, and therefore the arithmetic genus of Xp
        return false;
    end if;
    // We check the curve has a smooth F_p point
    if Eltseq(R) eq [] then
        Rp := RepresentativePoint(RandomPlace(Xp,1));
    else seqp := [GF(p) ! r : r in Eltseq(R)];
        try Rp := Xp ! seqp; // in try in case point has bad representative, won't happen if a cusp
        catch e Rp := RepresentativePoint(RandomPlace(Xp,1));
        end try;
    end if;
    if IsNonsingular(Xp,Rp) then
        return true;
    else return false;
    end if;
end function;


////////////////////////////////////////////////////////////////////////////////

// Example 1:

/*

// We test is_nonsing_p with the curve X_0(100)

N := 100;
X,_,_,_,cusp := eqs_quos(N,[]);
time for p in PrimesUpTo(70) do         // 4 seconds
    tf := is_nonsing_p(X, N, p, cusp);
    print(<p, tf>);
end for;
// output is false for 2 and 5, and true otherwise

// Example 2a:

// We test is_nonsing_p with the curve X_0(100)
N := 103;
X,_,_,_,cusp := eqs_quos(N,[]);
time for p in PrimesUpTo(70) do         // 2.5 seconds
    tf := is_nonsing_p(X, N, p, cusp);
    print(<p, tf>);
end for;
// output is false for 2 and true otherwise.
// X_0(103) will admit some model which is nonsingular at 2, but this one is singular at 2.

// Example 2b:

// We test the same code on X_0(103) without supplying a point
// It takes twice as long with this example (worse for higher genus examples)

N := 103;
X := eqs_quos(N,[]);
time for p in PrimesUpTo(70) do         // 5 seconds
    tf := is_nonsing_p(X, N, p, []);
    print(<p, tf>);
end for;

*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////////
//// good_eqs_mod_p ////
////////////////////////

// (See next function, canonic_alt, for constructing such models from the source)

// Input: X, N, p
// X is a smooth model for X_0(N) from canonical embedding, p is a prime not dividing N

// Output: The same curve X_new with (potentially new) defining equations, true or false
// true means that the curve is nonsingular at p, and false means it is singular at p

// If p is already a prime of good reduction then the original curve is returned
// Otherwise the function tries to find new defining equations for the curve
// Only the equations may change, not the coordinates

// Note: will not work for a diagonalised model mod 2 as otherwise the AL involutions would act trivially mod 2


good_eqs_mod_p := function(X,N,p);
    if is_nonsing_p(X,N,p,[]) then
        return X, true;
    end if;
    eqns := Equations(X);
    max_d := Degree(eqns[#eqns]);
    new_eqns := [];
    for d in [2..max_d] do
        A<[x]> := AmbientSpace(X);
        R := CoordinateRing(A);
        mons := [m : m in MonomialsOfDegree(R,d)];
        Coeffs := [[MonomialCoefficient(e,xx) : e in eqns] : xx in mons];
        M := Transpose(Matrix(Integers(),Coeffs));
        SF, P, Q := SmithForm(M);
        Z := P*M;
        Z := ChangeRing(Z,R);
        mons_mat := Matrix(#mons,1,mons);
        W := Eltseq(Z*mons_mat);
        new_eqns := new_eqns cat W;
    end for;
    new_eqns := [ee : ee in new_eqns | IsZero(ee) eq false];
    X_new := Curve(A,new_eqns);
    assert X_new eq X;
    tf := is_nonsing_p(X_new, N, p, []);
    return X_new, tf;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

////////////////////////
//// canonic_primes ////
////////////////////////

// (see examples after function)

// This is the same as the 'canonic' function, but takes a list of primes as an optional parameter.
// If a list of primes is provided then for each prime p the code will try to find equations such that the curve has good reduction at p. It will output the curve X and a list of tuples to describe what has happened with each prime.
// There are 4 possible tuples:
// <p, "very bad"> if p divides N (nothing can be done here)
// <p, "still good"> if the curve had good reduction at p and the new curve does too
// <p, "still bad"> if the method did not work and the curve still has bad reduction at p after potentially changing the equations
// <p, "now bad"> if the original curve had good reduction at p, but by changing the equations when working with a different prime, the curve now has bad reduction at p
// <p, "now good"> if the method worked and the curve now has good reduction at p (compared to if just canonic had been used)

canonic_primes := function(B: primes := []);
    N := Level(B[1]);
    prec := 5*N;
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsIrreducible(X) then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;

    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

    eqns := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns]; // scale equations
    X := Curve(ProjectiveSpace(R),eqns); // same curve with scaled equations

	for eqn in eqns do
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound for Gamma_0(N)
	    Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
		assert Valuation(Evaluate(eqn,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.
    if primes eq [] then
         return(X);
    end if;
    changes1 := [* *];
    for p in primes do
        if IsZero(N mod p) then
            changes1 := changes1 cat [*<p, "very bad">*];
            continue;
        end if;
        if is_nonsing_p(X,N,p,[]) then // already has good reduction at p
            changes1 := changes1 cat [*<p, "already good">*];
            continue;
        end if;
        X,tf := good_eqs_mod_p(X,N,p);
        if tf then
            changes1 := changes1 cat [*<p, "now good">*];
        else
            changes1 := changes1 cat [*<p,"still bad">*];
        end if;
    end for;
    // We now check that any changes have not made primes that were of good reduction into primes of bad reduction
    changes2 := [* *];
    for change in changes1 do
        if change[2] eq "already good" then
            p := change[1];
            if is_nonsing_p(X,N,p,[]) eq false then
                changes2 := changes2 cat [*<p, "now bad">*];
            else
                changes2 := changes2 cat [*<p, "still good">*];
            end if;
        else
            changes2 := changes2 cat [*change*];
        end if;
    end for;
    return X, changes2;
end function;



////////////////////////////////////////////////////////////////////////////////

/*
// Example 1:

// We try and find a model for X_0(97) with good reduction at 2

// We use the standard Magma basis

B1 := Basis(CuspForms(97));
X := canonic(B1);

X2 := ChangeRing(X,GF(2));
assert IsSingular(X2);   // Model has bad reduction at 2

// Instead, we will use canonic primes and ask the function to try and find new equations

Xn, changes := canonic_primes(B1: primes := [2]);
changes; // [* <2, "now good"> *]
// This is the same curve with different defining equations, but now we have good reduction at 2.

// This process will not work if we work with a diagonalised basis:

Xn2, changes := canonic_primes(all_diag_basis(97): primes := [2]);
changes; // [* <2, "still bad"> *]

/////////////////////////

// Example 2:

// We find a diagonalised model for X_0(38) with good reduction at 3

B2 := all_diag_basis(38);
X := canonic(B2);

X3 := ChangeRing(X,GF(3));
assert IsSingular(X3);   // Model has bad reduction at 3

// Instead, we will use canonic primes and ask the function to try and find new equations

Xn, changes := canonic_primes(B2: primes := [2,3,5,7,11]);
changes;
// [* <2, "very bad">, <3, "now good">, <5, "still good">, <7, "still good">, <11, "still good"> *]
*/

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////
//// canonic_degs ////
//////////////////////

// This function works in the same way as 'canonic', but can take any list of cusp forms and can search for relations of higher degrees.

// Input: List of cusp forms B of level N, max_d to find relations up to
// Output: Model for the curve X_0(N) defined by equations of degree up to max_d.

// Note: a model will be output only if suitable cusp forms and a suitable max_d is provided

canonic_degs := function(B, max_d);
    N := Level(B[1]);
    prec := 5*N;
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
    for d in [1..max_d] do
        mons:=MonomialsOfDegree(R,d);
        monsq:=[Evaluate(mon,Bexp) : mon in mons];
        V:=VectorSpace(Rationals(),#mons);
        W:=VectorSpace(Rationals(),prec-10);
        h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
        K:=Kernel(h);
        eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
    end for;
    eqns := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns]; // scale equations
    X := Curve(ProjectiveSpace(R),eqns); // same curve with scaled equations
    return(X);
end function;

////////////////////////////////////////////////////////////////////////////////

/*
// Example:

// We find some models for X_0(97)

N := 97;
C := CuspForms(N);
B1 := [C ! b : b in Basis(CuspForms(N))];
B2 := [C ! b : b in all_diag_basis(N)];
// We coerce these bases into C so that we can combine them below:
B3 := B1 cat B2;
d := 4;
X := canonic_degs(B2,d);
assert #Equations(X) eq 232;

Equations(X)[1]; // x[1]^2 - x[4]^2 - 8*x[4]*x[6] + 14*x[4]*x[7] + 8*x[5]^2 + 8*x[5]*x[7] -4*x[6]^2 + 15*x[7]^2, a degree 2 relation

Equations(X)[20]; // 2*x[1]*x[2]*x[4] - 2*x[4]^2*x[5] + 7*x[4]*x[6]^2 - 14*x[4]*x[6]*x[7] + 17*x[4]*x[7]^2 + 8*x[5]^3 + x[5]^2*x[6] - 33*x[5]^2*x[7] + 7*x[5]*x[6]^2 - 31*x[5]*x[6]*x[7] + 10*x[5]*x[7]^2 + 7*x[6]^3 - 13*x[6]^2*x[7] + 7*x[6]*x[7]^2 + 21*x[7]^3, a degree 3 relation

assert Degree(Equations(X)[100]) eq 4; // a degree 4 relation

assert Genus(X) eq 7;

//////

d := 2;
X := canonic_degs(B3,d);

AmbientSpace(X); // Projective Space of dimension 13 over Rational Field

// The first few relations are linear relations
Equations(X)[1..3];
// [ 2*x[1] - x[10] - 2*x[11] + x[13] - x[14], 2*x[2] + x[8] - x[9] - 2*x[10] - x[11] - x[12] + 2*x[13] - x[14], 2*x[3] + x[9] - x[12] - 2*x[13] + 2*x[14]]

assert Genus(X) eq 7;

assert #Equations(X) eq 94; // Many equations
*/



////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
//// mod_para ////
//////////////////

// Input: X, B, Elliptic curve E or its Cremona label, q-expansions of elliptic curve coordinates
// X is a model for X_0(N) obtained from a basis of cusp forms B (for X_0(N) non-hyperelliptic of Genus > 1)
// the elliptic curve should be optimal
// The q expansions of the x- and y-coordinates of the elliptic curve should be given up to precision 5*(N+1)
// Magma does not have a functino to compute the q-expansions of the x- and y-coordinates, but this can be done in SageMath or PARI/GP, please see the examples below

// Output:
// The modular paraemtrisation map phi: X -> E, the curve E

mod_para := function(X,B,E,xq,yq);
    if Type(E) eq MonStgElt then
        E := EllipticCurve(E);
    end if;
    deg_map := ModularDegree(E);
    g := #B;
    N := Level(B[1]);
    prec := 5*N;
    maxprec := prec+1;
    L<q> := LaurentSeriesRing(Rationals());
    Bexp:=[L!qExpansion(B[i],maxprec) : i in [1..g]];
    R<[x]> := PolynomialRing(Rationals(),g);
    vars := [R.i : i in [1..g]];

    qexps := [L ! xq, L ! yq];
    for f in qexps do
        val := Valuation(f);
        if f eq qexps[1] then
            degf := 2*deg_map;
        else degf := 3*deg_map;
        end if;

        r1 := (degf / (2*(g-1))) + 1/2;
        if IsIntegral(r1) then
           r := Integers()! (r1+1);
        else r := Ceiling(r1);
        end if;

        num, denom := find_rels(L, B, Bexp, N, f, degf, r, prec, maxprec, g);

        if f eq qexps[1] then
            xnum := num;
            xdenom := denom;
            xx := xnum / xdenom;
        else ynum := num;
             ydenom := denom;
             yy := ynum / ydenom;
        end if;
    end for;
    mod_para_map := map<X -> E | [xx,yy,1]>;
    return mod_para_map, E;
end function;

////////////////////////////////////////////////////////////////////////////////

/*
// Example 1:

// We compute the modular parametrisation map from X_0(116) to the elliptic curve E with Cremona label "116b"

// We must first start by obtaining the q-expansions of the x- and y-coordinates from SageMath (or PARI/GP)

// SageMath code:
// E = EllipticCurve('116b1')
// xq, yq = E.modular_parametrization().power_series(prec = 5*117)

// xq is q^-2 - 1 + 2*q^4 - 6*q^8 + 3*q^10 + ... - 494294760843438*q^582 + O(q^583)
// yq is -q^-3 + q^-1 + 2*q - 5*q^3 + q^5 + ... + 44920287440607470*q^581 + O(q^582)

L<q> := LaurentSeriesRing(Rationals());
// xq := // copy in from SageMath (without the O(q^583))
// yq  := // copy in from SageMath (without the O(q^582))

X := eqs_quos(116,[]); // uses diagoanlised basis
assert Genus(X) eq 13;
time phi, E := mod_para(X, all_diag_basis(116), "116b1",xq,yq);  // 1.6 seconds
E; // Elliptic Curve defined by y^2 = x^3 + x^2 - 4*x + 4 over Rational Field
assert Degree(phi) eq 8; // 1 second

// We can use phi to compute the preimage of some points on E.

ptsE := Points(E: Bound := 1); // E(Q) = Z / 3Z, we have all the rational points
assert #ptsE eq 3;
P := ptsE[2];

// We compute the preimage of P under phi using places

D := Pullback(phi,Place(P));
preimage := Decomposition(D);
// [<Place at (0 : 0 : 0 : 0 : 0 : 0 : 1/160*(-15*$.1 + 18) : 1/80*(-15*$.1 + 18) : 0 : 1/80*(15*$.1 - 18) : 1/160*(15*$.1 - 18) : 1 : 1), 1>,
// <Place at (1/2*$.1 : 1/2*$.1 : 1/4*(3*$.1 + 6)*$.1 + 1/4*(-3*$.1 - 3) : 1/4*(-3*$.1 - 6)*$.1 + 1/4*(3*$.1 + 3) : 1/4*(-3*$.1 - 6)*$.1 + 1/4*(3*$.1 + 3) : 1/4*(-3*$.1 - 6)*$.1 + 1/4*(3*$.1 + 3) : 1/4*(3*$.1 + 3)*$.1 + 1/8*(-3*$.1 - 6) : 0 : 1/2*(-3*$.1 - 3)*$.1 + 1/4*(3*$.1 + 6) : 1/2*(-3*$.1 - 3)*$.1 + 1/4*(3*$.1 + 6) : 1/4*(-3*$.1 - 3)*$.1 + 1/8*(3*$.1 +6) : 1 : 0), 1>,
//<Place at (0 : 0 : 0 : 0 : 0 : 0 : -1/2 : 0 : 0 : 1/2 : 0 : 1 : 0), 1>,
//<Place at (0 : 0 : 0 : 0 : 0 : 0 : 1/2 : 0 : 0 : -1/2 : 0 : 1 : 0), 1>]

// We see that we have two rational cusps, a quadratic point, and a quartic point.
// We can check the fields of definition as follows:

K := ResidueClassField(preimage[2][1]);
AbsoluteDiscriminant(Integers(K)); // 256
assert IsIsomorphic(K, CyclotomicField(8));

L := ResidueClassField(preimage[1][1]);
AbsoluteDiscriminant(Integers(L)); // -4
assert IsIsomorphic(L, QuadraticField(-1));

// Let's check that phi maps the quadratic point back down to P

assert phi(RepresentativePoint(preimage[1][1])) eq P;

///////////

// Example 2:

// We compute the modular paraemtrisation map X_0(55) to E
// where E is the elliptic curve with Cremona label "55a1"

// We start by computing a model for X_0(55) using the standard cusp form basis
// This model has bad reduction at 3, but using canonic primes we use a model with good reduction at 3

B := Basis(CuspForms(55));
X, changes := canonic_primes(B : primes := [2,3,7]);
changes; // [* <2, "still good">, <3, "now good">, <7, "still good"> *]

L<q> := LaurentSeriesRing(Rationals());
// xq := // copy in from SageMath
// yq := // copy in from SageMath
time phi, E := mod_para(X, B, "55a1",xq,yq); // 0.1 seconds
assert Degree(phi) eq 2;
phi; // Mapping from: Crv: X to CrvEll: E with equations : x[3] - x[4] + x[5], -x[2] + x[3] - x[4], x[5]

/////////////

// We can also do the same computations with a diagonalised basis:
B := all_diag_basis(55);
X, changes := canonic_primes(B : primes := [2,3,7]);
changes; // [* <2, "still bad">, <3, "still good">, <7, "still good"> *]

// (We see that we lose good reduction at 2 here, and it can't be fixed as our basis is diagonalised)

time phi, E := mod_para(X, B, "55a1",xq,yq); // 0.1 seconds
assert Degree(phi) eq 2;
phi; // Mapping from: Crv: X to CrvEll: E with equations : 1/2*x[1]*x[2] - x[2]^2 + 3/2*x[2]*x[3] + 1/2*x[2]*x[5], -1/2*x[1]^2 + x[1]*x[2] - x[1]*x[3] - 1/2*x[1]*x[5] + 1/2*x[2]^2 + 1/2*x[2]*x[3] - x[3]*x[5], x[2]*x[3]
*/
