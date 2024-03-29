load "ozmansiksek_TorsHelp.m";
load "X0N_NiceModel.m";
load "HelpTorsion.m";

//We find a model for X0(60), using code taken from Najman-Vukorepa https://github.com/brutalni-vux/QuadPtsBielliptic

C:=CuspForms(60);
"Dimension of CuspForms(60) is:";
Dimension(C);

AL15:=AtkinLehnerOperator(C, 15);
N15:=Nullspace(Matrix(AL15 - 1));

"Dimension of eigenspace lambda=1 for w15 is:";
Dimension(N15);

N15c:=Nullspace(Matrix(AL15 + 1));

"Dimension of eigenspace lambda=-1 for w15 is:";
Dimension(N15c);

B15:=[&+[(Integers()!(2*Eltseq(Basis(N15)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N15)]];
B15c:=[&+[(Integers()!(2*Eltseq(Basis(N15c)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N15c)]];

X60,jMap:= modformeqns(B15c cat B15, 60, 500, 20);
"Model for X0(60) is:";
X60;
"";

RR<[u]>:=CoordinateRing(AmbientSpace(X60));
n:=Dimension(AmbientSpace(X60));

H:=Matrix(RationalField(), 7, 7, [1,0,0,0,0,0,0, 0,1,0,0,0,0,0, 0,0,1,0,0,0,0, 0,0,0,1,0,0,0, 0,0,0,0,1,0,0, 0,0,0,0,0,1,0, 0,0,0,0,0,0,-1]);
rows:=[[&+[RowSequence(H)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]]] ;
w15:=iso<X60->X60 | rows, rows>;
"w15 on X0(60) is given by:";
w15;
"";

X60w15,quotMap15:=CurveQuotient(AutomorphismGroup(X60,[w15]));
"Genus of X0(60) is ", Genus(X60);
"Genus of X0(60)/w15 is ", Genus(X60w15);
"";

//P1, ..., P12 are cusps
P1:=X60![0,0,0,0,-1,0,1];
P2:=X60![0,0,0,0,1,0,1];
P3:=X60![0,0,-1/4,-1/4,1/4,1/4,1];
P4:=X60![0,0,-1/4,1/4,1/4,-1/4,1];
P5:=X60![0,0,1/4,-1/4,-1/4,1/4,1];
P6:=X60![0,0,1/4,1/4,-1/4,-1/4,1];
P7:=X60![-1,0,0,0,0,0,1];
P8:=X60![-1/2,-1/2,-1/4,-1/4,-1/4,-1/4,1];
P9:=X60![-1/2,1/2,-1/4,1/4,-1/4,1/4,1];
P10:=X60![1/2,-1/2,1/4,-1/4,1/4,-1/4,1];
P11:=X60![1/2,1/2,1/4,1/4,1/4,1/4,1];
P12:=X60![1,0,0,0,0,0,1];

"By finding poles of j-map, we find that we have these 12 cusps (P1, ..., P12):";
Poles(jMap);
"";

"Cuspidal group is generated by Di := P1 - Pi, i in {2,3, ..., 12}";
"";

D2:=Divisor(P1)-Divisor(P2);
D3:=Divisor(P1)-Divisor(P3);
D4:=Divisor(P1)-Divisor(P4);
D5:=Divisor(P1)-Divisor(P5);
D6:=Divisor(P1)-Divisor(P6);
D7:=Divisor(P1)-Divisor(P7);
D8:=Divisor(P1)-Divisor(P8);
D9:=Divisor(P1)-Divisor(P9);
D10:=Divisor(P1)-Divisor(P10);
D11:=Divisor(P1)-Divisor(P11);
D12:=Divisor(P1)-Divisor(P12);

// this shows that D2 and D3 are of order 24 and independent
// hence, they generate subgroup Z/24Z + Z/24Z
b,ff := IsPrincipal(24*D2);
"Is D2 of order 24?";
b and not(IsPrincipal(8*D2) or IsPrincipal(12*D2));
"";

"Is D3 of order 24?";
b,ff := IsPrincipal(24*D3);
b and not(IsPrincipal(8*D2) or IsPrincipal(12*D2));
"";

"Is a*D2 = b*D3 while (a,b)!=(0,0) mod 24? (are D2 and D3 linearly dependent?)";
AreDependent(D2,D3,24), ", hence, D2 and D3 generate subgroup iso. to (Z/24Z)^2";
"";

//D2 and D3 generate the following subgroup
G:=[i*D2+j*D3 : i in [-11..12], j in [-11..12]];

// this shows that D5 is of order 24 in torsion group, but also of
// order 24 (coset) in quotient J(60)(Q)_tor/<D2, D3>, hence D5 gives another
// Z/24Z component in J(60)(Q)_tor
b, ff:=IsPrincipal(24*D5);
"Is D5 of order 24?";
b and not (IsPrincipal(12*D5) or IsPrincipal(8*D5));
"";

"Is coset of D5 of order 24 in J(60)(Q)_tor/<D2, D3>?";
not(IsInGroup(12*D5, G) or IsInGroup(8*D5, G)), ", hence, we know that D2, D3, D5 generate a subgroup (Z/24Z)^3";
"";

//Getting the Z/4Z part
D7:=Divisor(P1)-Divisor(P7);
Dt:=D7-4*D2-6*D3;

//Dt is of order 4
b, ff := IsPrincipal(4*Dt);
"Is Dt := D7 - 4*D2 - 6*D3 of order 4?";
b and not (IsPrincipal(2*Dt));
"";

// 2*Dt is of order 2, but 2*Dt and 2*Dt+12*D5 are both not in <D2,D3>
// hence, (coset of) 2*Dt is of order 2 in J(60)(Q)_tor/<D2,D3,D5>
// hence, (coset of) Dt is of order 4 in J(60)(Q)_tor/<D2,D3,D5> so
// Dt gives uz new Z/4Z component

"Is coset of Dt of order 4 in J(60)(Q)_tor/<D2,D3,D5>?";
not(IsInGroup(2*Dt, G) or IsInGroup(2*Dt+12*D5, G));
"Hence we have proven that Dt, D5, D3, D2 generate a subgroup Z/4Z + (Z/24Z)^3";
"";

TOR:=[i*D2 + j*D3 + k*D5 + l*Dt : i in [-11..12], j in [-11..12], k in [-11..12], l in [-1..2]];

//Now that we have J0(60)(Q) in hand, let's see if we can find its cubic points :)) 
//We know that all cubic points on X0(60) come from 1-dimensional RR spaces, by Theorem 6.

print "Searching for cubic points on X0(60)";

//We choose a base point
D0 := Place(P1);

cubicptsindx := [];

for i in [1..#TOR]
    do D := 3*D0 + TOR[i];
       L,phi:=RiemannRochSpace(D);
	   dim:=Dimension(L);
	   //if dim ge 2 then
		//print "The dimension of the RR space is ge 2 so there are no cubic points from RR space";
	   //end if;
	   if dim eq 1 then
			D:=D+Divisor(phi(L.1));
			assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k := ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 3 then
				            print "There is a cubic pt on X0(60)!";
                            print "------------------------------";
                    		Append(~cubicptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 500, 1000, 1500, 2000, 10000, 20000, 30000, 40000, 50000]
        then print "We've reached i = ", i;
    end if;
end for;


if #cubicptsindx eq 0
    then print "There are no cubic pts on X0(60)!";
    else for j in cubicptsindx
            do D:=3*D0 + TOR[j];
               L, phi:=RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D:= D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t>:= ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 3;
               print "The cubic pt corresponding to", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;

print "--------------------------------------------------------------";

//Can we find all primitive degree 4 points in the same way?
//By Theorem 6, they come from 1-dimension RR spaces.

print "Searching for primitive degree 4 points on X0(60)";

D0 := Place(P1)+Place(P2);

primdeg4ptsindx := [];

for i in [1..#TOR]
    do D := 2*D0 + TOR[i];
       L,phi:=RiemannRochSpace(D); 
	   dim:=Dimension(L);
	    //if dim ge 2 then
		//	print "The dimension of the RR sapace is ge 2 so there are no primitive deg4 pts from RR space";
		//end if;
		if dim eq 1 then
			D:=D+Divisor(phi(L.1));
			assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k := ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 4 then
				            print "There is a primitive degree 4 pt on X0(60)!";
                            print "-------------------------------------------";
                    		Append(~primdeg4ptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 500, 1000, 1500, 2000, 10000, 20000, 30000, 40000, 50000]
        then print "We've reached i = ", i;
    end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #primdeg4ptsindx eq 0
    then print "There are no primitive degree 4 pts on X0(60)!";
    else for j in primdeg4ptsindx
            do D := 2*D0 + TOR[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 4;
               print "The quartic pt corresponding to", Decomposition(D)[1][1],
                      "is defined over the", k, "The Galois Group of k has order", Order(GaloisGroup(k)); 
                      if #GaloisGroup(k) in [Factorial(4), Factorial(4)/2]
                        then print "The point is primitive!";
                        else print "The point is not primitive!";
                      end if;
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;

print "--------------------------------------------------------------";

//Can we find all degree 5 points in the same way?
//We know they come from 1-dimensional RR spaces.

print "Searching for degree 5 points on X0(60)";
print "---------------------------------------";

D0 := Place(P1);

deg5ptsindx := [];

for i in [1..#TOR]
    do D := 5*D0 + TOR[i];
    	L,phi:=RiemannRochSpace(D); 
	dim:=Dimension(L);
	//if dim ge 2 then
		//print "The dimension of the RR space is ge 2 so there are no deg 5 pts coming from this RR space.";
	//end if;
	if dim eq 1 then
		D:=D+Divisor(phi(L.1));
		assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k := ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 5 then
				            print "There is a degree 5 pt on X0(60)!";
                            print "---------------------------------";
                    		Append(~deg5ptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 500, 1000, 1500, 2000, 10000, 20000, 30000, 40000, 50000]
        then print "We've reached i = ", i;
    end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

print "------------------------------------------------";

if #deg5ptsindx eq 0
    then print "There are no degree 5 pts on X0(60)!";
    else for j in deg5ptsindx
            do D:= 5*D0 + TOR[j];
               L, phi:= RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D:= D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t>:= ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 5;
               print "The degree 5 pt corresponding to", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;                         
