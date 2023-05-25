//The hyperelliptic modular curve X0(47) has genus 4 and rank 0
//By Theorem 5 of our paper, X0(47) has finitely many points of degrees 3,
//and finitely many primitive points of degree 4,
//all of which come from 1-dimensional RR spaces

X := SimplifiedModel(SmallModularCurve(47));
assert Genus(X) eq 4;

print "We want to find all cubic pts, and all primitive degree 4 points on X0(47)";
print "-----------------------------------";

J := Jacobian(X);
assert RankBound(J) eq 0;   //We already know this from Bruin-Najman
                            // We also know that J(Q)_tors = Z/23Z.
ptsX := Points(X : Bound := 100);

P1 := ptsX[1];
P2 := ptsX[2];

D1 := P1 - P2;
assert Order(D1) eq 23;

print "We know from Bruin-Najman J(Q)=Z/23Z, its generator is the divisor";
print D1;
print "-----------------------------------";

D1 := Place(P1)-Place(P2);

tors := [i*D1 : i in [0..22]];

print "We're searching for cubic points on X0(47).
        We know all cubic pts arise from a 1-dimensional RR space.";
print "-----------------------------------";

//We choose a base point.

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
				            print "There is a cubic pt on X0(47)!";
                                        print "-----------------------------------";
                    		Append(~cubicptsindx, i);
                	end if;
        	end for;
	end if;
end for;

print "We have a list of the indices of the 'torsion part' of the divisor,
so we can find the points explicitly :))"; 
print "-----------------------------------";

if #cubicptsindx eq 0
    then print "There are no cubic pts on X0(47)!";
    else for j in cubicptsindx
            do D := 3*D0 + tors[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 3;
               print "The cubic pt", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;

print "We're searching for primitive quartic points on X0(47).
       We know all primitive quartic pts arise from a 1-dimensional RR space.";
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
				            print "There is a degree 4 pt on X0(47)!";
                                        print "-----------------------------------";
                    		Append(~deg4ptsindx, i);
                	end if;
        	end for;
	end if;
end for;

print "We have a list of the indices of the 'torsion part' of the divisor,
so we can find the points explicitly :))"; 
print "-----------------------------------";

if #deg4ptsindx eq 0
    then print "There are no primitive degree 4 pts on X0(47)!";
    else for j in deg4ptsindx
            do D := 2*D0 + tors[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 4;
               print "The quartic pt", Decomposition(D)[1][1],
                      "is defined over the", k; 
                      print "The Galois group of k has size", Order(GaloisGroup(k));
                      if #GaloisGroup(k) in [Factorial(4), Factorial(4)/2]
                        then print "The point is primitive!";
                        else print "The point is not primitive!";
                      end if;
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;