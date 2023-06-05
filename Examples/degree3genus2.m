R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(x^6+4*x^4+4*x^2+1);

D := Place(C![1,-1,0]);

J := Jacobian(C);

assert RankBound(J) eq 0;
tors := TorsionSubgroup(J);
assert #tors eq 18;

pts := Points(J : Bound := 100);

D1 := pts[5];
D2 := pts[6];

assert Order(D1) eq 3;
assert Order(D2) eq 6;

assert 2*D2 ne D1;

assert #{a*D1+b*D2: a in [0..2], b in [0..5]} eq 18; //D1 and D2 generate J(Q)

D1 := 2*Place(C![0,-1,1])-Place(C![1,-1,0])-Place(C![1,1,0]);
D2 := Place(C![0,-1,1])-Place(C![1,-1,0]);

for a in [0..2] do
	for b in [0..5] do
		D:=a*D1+b*D2+3*Place(C![1,1,0]);
		L,phi:=RiemannRochSpace(D);
		assert Dimension(L) eq 2;
	end for;
end for;

//Since all RR-spaces have dimension 2, any degree 3 point on C with Galois group A3
//induces a Q-rational point on a "discriminant curve" that is hyperelliptic,
//we construct this curve below 

//
Qx<x> := PolynomialRing(Rationals());
Qu<u>:=FunctionField(Rationals());
Qux<x>:=PolynomialRing(Qu);

Y := HyperellipticCurve(x^6+4*x^4+4*x^2+1);
D1 := 2*Place(Y![0,-1,1])-Place(Y![1,-1,0])-Place(Y![1,1,0]);
D2 := Place(Y![0,-1,1])-Place(Y![1,-1,0]);
infdiv := Place(Y![1,-1,0]);

for a in [0..2] do	
	for b in [0..5] do
		D:=a*D1+b*D2+3*infdiv;
		L,phi:=RiemannRochSpace(D);
		assert Dimension(L) eq 2;
                if #Decomposition(D+Divisor(phi(u*L.1+L.2))) eq 1 then
                	E := Decomposition(D+Divisor(phi(u*L.1+L.2)))[1,1];
                       	F := ResidueClassField(E);
                       	f := MinimalPolynomial(F.1);
                       	assert Degree(f) eq 3;
                       	print a,b, IsIrreducible(f);
                        disc := Discriminant(f);
                        f1 := Numerator(disc);
                        f2 := Denominator(disc);
                        facts1:=Factorisation(f1);
                        facts2:=Factorisation(f2);
                        facts1:=[ <pr[1],(Integers()!pr[2]) mod 2>  : pr in facts1];
                        facts2:=[ <pr[1],(Integers()!pr[2]) mod 2>  : pr in facts2];
                        facts:=facts1 cat facts2;
                        g:=&*[pr[1]^Integers()!pr[2] : pr in facts];
                        c1:=LeadingCoefficient(f1);
                        c2:=LeadingCoefficient(f2);
                        p:=c1*c2;
                        p:=p*Denominator(p)^2;
                        p:=Squarefree(Integers()!p);
                        g:=p*g;
                        d:=LCM([ Denominator(r)  : r in Coefficients(g)]);
                        s,t:=Squarefree(d);
                        g:=s^2*t^2*g;
                        assert IsSquare(disc/g);
			if Degree(g) eq 0 then
				if g eq 1 then
					print "discriminant is a square"; 
					pts:=[ [u1,0,v1] : u1,v1 in [-5..5] | {u1,v1} ne {0} and GCD(u1,v1) eq 1];
				else
					print "discriminant is never a square";
					pts:=[];
				end if;
				gen:=0;
			else
                        	H:=HyperellipticCurve(g);
                               	pts:=Points(H : Bound:=10^5);
				gen:=Genus(H);
			end if;
                       	print H, a,b,gen,pts;
			for pt in pts do
				print "computing the Galois group corresponding to", pt;
				u1:=pt[1];
				v1:=pt[3];
				E1 := Decomposition(D+Divisor(phi(u1*L.1+v1*L.2)));
				if #E1 eq 1 and E1[1,2] eq 1 then
					E1:=E1[1,1];
					F1 := ResidueClassField(E1);
                               		f := Qx!MinimalPolynomial(F1.1);
                               		assert Degree(f) eq 3; G:=GaloisGroup(f);
					print G;
				else
					print "divisor is reducible";
				end if;
			end for;
                    	print "++++++++++++++++++++";
               	end if;
	end for;
end for;


//Sanity check

R<x> := PolynomialRing(Rationals());
Y := HyperellipticCurve(-27*x^4 - 74*x^2 - 27);
assert TwoCoverDescent(Y) eq {};

Y := HyperellipticCurve(-8*x^4 - 11*x^2 - 8);
assert TwoCoverDescent(Y) eq {};

