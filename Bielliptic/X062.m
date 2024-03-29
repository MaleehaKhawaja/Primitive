load "HelpTorsion.m";
load "models_and_maps.m";
load "rank_0_auxiliary.m";

print "We compute a model for X0(62) using the code given in the paper by
//Adzaga, Keller, Michaud-Jacobs, Najman, Ozman, and Vukorepa";
//source: https://github.com/TimoKellerMath/QuadraticPoints

time X62, ws, pairs, NB, cusp := eqs_quos(62,[]);

assert Genus(X62) eq 7;

time j, num_denom := jmap(X62, 62);

//We need the cusps of X62 to compute the torsion subgroup of J62(Q)

cusps := compute_cusps(X62, 62, ws, cusp, num_denom: use_jmap := false);

P1 := cusps[1];
P2 := cusps[2];
P3 := cusps[3];
P4 := cusps[4];

D2 := P2 - P1;
D3 := P3 - P1;
D4 := P4 - P1;

print "Najman-Vukorepa tells us that J0(62)=Z/5Z times Z/120Z (see page 11),
        we want to find its generators.";
print "--------------------------------------------------------------------";

assert IsPrincipal(15*D2);
assert IsPrincipal(3*D2) eq false;
assert IsPrincipal(5*D2) eq false;

assert IsPrincipal(40*D3);
for i in [2, 5, 8, 10, 20]
    do assert IsPrincipal(i*D3) eq false;
end for;

//I think D2 and D3 generate J(Q)=J(Q)_tors
//but I need to check that they aren't linearly dependent
//i.e. that they generate a group of order 600

print "We use code of Adzaga et al to find generators of J0(38)(Q).";
//We use this function to check that D2, D3 generate J0(38)(Q).
findGenerators(X62, 62, cusps, P1, 3);                  

assert #{i*D2+j*D3: i in [0..14], j in [0..39]} eq 600;

TOR := [i*D2+j*D3: i in [0..14], j in [0..39]];

print "----------------------------------------------------------";

//Now that we have J0(62)(Q) in hand, let's see if we can find its cubic points :)) 
//We know that all cubic pts, primitive degree 4 pts, and degree 5 pts
//come from 1-dimension RR spaces


print "Searching for cubic points on X0(62)";
print "------------------------------------";

//We choose a base point
D0 := P1;

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
				            print "There is a cubic pt on X0(62)!";
                            print "------------------------------";
                    		Append(~cubicptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 200, 300, 400, 500]
        then print "We've reached i = ", i;
    end if;
end for;


if #cubicptsindx eq 0
    then print "There are no cubic pts on X0(62)!";
    else for j in cubicptsindx
            do D:=3*D0 + TOR[j];
               L, phi:=RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D:= D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t>:= ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 3;
               print "The cubic pt", Decomposition(D)[1][1],
                      "is defined over the", k, 
                      "The Galois group of k has order", #GaloisGroup(k);
               print "-------------------------------------------";
               print "-------------------------------------------";
         end for;
end if;

print "--------------------------------------------------------------";

//Can we find all primitive degree 4 points in the same way?

print "Searching for primitive degree 4 points on X0(62)";
print "-------------------------------------------------";

D0 := P1 + P2;

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
				            print "There is a primitive degree 4 pt on X0(62)!";
                            print "------------------------------------------";
                    		Append(~primdeg4ptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 200, 300, 400, 500]
        then print "We've reached i = ", i;
    end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #primdeg4ptsindx eq 0
    then print "There are no primitive degree 4 pts on X0(62)!";
    else for j in primdeg4ptsindx
            do D := 2*D0 + TOR[j];
               L, phi := RiemannRochSpace(D);
               assert Dimension(L) eq 1;
               D := D + Divisor(phi(L.1));
               assert IsEffective(D);
               k<t> := ResidueClassField(Decomposition(D)[1][1]);
               assert Degree(k) eq 4;
               print "The quartic pt corresponding to", Decomposition(D)[1][1],
                      "is defined over the", k, "The Galois Group of k has order", 
                      Order(GaloisGroup(k)); 
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

print "Searching for degree 5 points on X0(62)";
print "---------------------------------------";

D0 := P1;

deg5ptsindx := [];

for i in [1..#TOR]
    do D := 5*D0 + TOR[i];
    	L,phi:=RiemannRochSpace(D); // does this work??
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
				            print "There is a degree 5 pt on X0(62)!";
                            print "---------------------------------";
                    		Append(~deg5ptsindx, i);
                	end if;
        	end for;
	end if;
    if i in [1, 10, 100, 200, 300, 400, 500]
        then print "We've reached i = ", i;
    end if;
end for;

//We have a list of the "torsion part" of the divisor,
//so we can find the points explicitly :))

if #deg5ptsindx eq 0
    then print "There are no degree 5 pts on X0(62)!";
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
