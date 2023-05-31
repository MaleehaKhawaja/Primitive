//The hyperelliptic modular curve X0(46) has genus 5 and rank 0
//By Theorem 5, X0(46) has finitely many points of degrees 3 and 5,
//and finitely many primitive points of degree 4,
//all of which come from 1-dimensional RR spaces

X := SimplifiedModel(SmallModularCurve(46));
assert Genus(X) eq 5;

J := Jacobian(X);
assert RankBound(J) eq 0;   //We already know this from Bruin-Najman
                            // We also know that J(Q)_tors = Z/11Z x Z/22Z.
ptsX := Points(X : Bound := 100);

P1 := ptsX[1];
P2 := ptsX[2];
P3 := ptsX[3];
P4 := ptsX[4];

//We use P1 as the base point

D2 := P2 - P1;
D3 := P3 - P1;
D4 := P4 - P1;

assert Order(D2) eq 11;
assert Order(D3) eq 22;

//We want to check that D2 and D3 generate J(Q) i.e. that they're linearly independent

J7:=BaseChange(J,GF(7));
B,mu:=AbelianGroup(J7);
A:=FreeAbelianGroup(3);                        
eps:=hom<A->B | [ (J7!Q)@@mu : Q in [D2, D3, D4] ] >;
C:=Image(eps);

mu2 := (J7!D2)@@mu;
mu3 := (J7!D3)@@mu;

cuspGp:=AbelianGroup([11,22]);
delta := hom<cuspGp -> C | [mu2, mu3]>;

assert #Kernel(delta) eq 1;
assert Image(delta) eq C;

//

assert #Set([i*D2 + j*D3 : i in [0..10], j in [0..21]]) eq 11*22;

D2 := Place(P2) - Place(P1);
D3 := Place(P3) - Place(P1);
D4 := Place(P4) - Place(P1);

tors := [i*D2 + j*D3 : i in [0..10], j in [0..21]];

//We search for all cubic points
print "Searching for all cubic pts on X0(46)";
print "-------------------------------------";

D0 := Place(P1);

cubicptsindx := [];

for i in [1..#tors]
    do D := 3*D0 + tors[i];
    	L,phi:=RiemannRochSpace(D); 
	    dim:=Dimension(L);
	    if dim eq 1 then
		    D:=D+Divisor(phi(L.1));
		    assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k := ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 3 then
				            print "There is a cubic point on X0(46)!";
                            print "-----------------------------------";
                    		Append(~cubicptsindx, i);
                	end if;
        	end for;
	end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #cubicptsindx eq 0
    then print "There are no cubic pts on X0(46)!";
    else for j in cubicptsindx
            do D := 3*D0 + tors[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 3;
               print "The cubic pt corresponding to", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;

//We search for all primitive degree 4 pts,
//although the points that we find may not be primitive

oprint "Searching for all primitive degree 4 pts on X0(46)";
print "-----------------------------------";

D0 := Place(P1) + Place(P2);

deg4ptsindx := [];

for i in [1..#tors]
    do D := 2*D0 + tors[i];
    	L,phi:=RiemannRochSpace(D); 
	    dim:=Dimension(L);
	    if dim eq 1 then
		    D:=D+Divisor(phi(L.1));
		    assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k := ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 4 then
				            print "There is a degree 4 pt on X0(46)!";
                            print "-----------------------------------";
                    		Append(~deg4ptsindx, i);
                	end if;
        	end for;
	end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #deg4ptsindx eq 0
    then print "There are no primitive degree 4 pts on X0(46)!";
    else for j in deg4ptsindx
            do D := 2*D0 + tors[j];
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

//We search for all degree 5 points
print "Searching for all degree 5 pts on X0(46)";
print "-----------------------------------";

D0 := Place(P1);

deg5ptsindx := [];

for i in [1..#tors]
    do D := 5*D0 + tors[i];
    	L,phi:=RiemannRochSpace(D); 
	    dim:=Dimension(L);
	    if dim eq 1 then
		    D:=D+Divisor(phi(L.1));
		    assert IsEffective(D);
        	for j in [1..#Decomposition(D)] do
            		k:= ResidueClassField(Decomposition(D)[j][1]);
                	if Degree(k) eq 5 then
				            print "There is a degree 5 pt on X0(46)!";
                            print "-----------------------------------";
                    		Append(~deg5ptsindx, i);
                	end if;
        	end for;
	end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #deg5ptsindx eq 0
    then print "There are no degree 5 pts on X0(46)!";
    else for j in deg5ptsindx
            do D := 5*D0 + tors[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 5;
               print "The degree 5 pt", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;                         



