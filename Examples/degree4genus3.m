Qx<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(-x^6-x^5-x^4+x^2-2,x^4+x^2+x+1);  
C := SimplifiedModel(C);

J := Jacobian(C);
assert RankBound(J) eq 0;
assert BadPrimes(J) eq [ 2, 21017 ];

pts := [C![1,-1,0], C![1,1,0], C! [1,0,1]];

//Want to determine J(Q);

for P,Q in pts
	do Order(P-Q);
end for;

//Returns 1 or 19, we can check that J(Q)=Z/19Z since we know that J(Q) injects into J(F3):

J3 := BaseChange(J, GF(3));
assert #J3 eq 19;

D1 := Place(C![1,1,0])-Place(C![1,-1,0]);
assert Order(C![1,1,0]-C![1,-1,0]) eq 19;

//

Qu<u>:=FunctionField(Rationals());
Qux<x>:=PolynomialRing(Qu);

Y := HyperellipticCurve(-x^6-x^5-x^4+x^2-2,x^4+x^2+x+1);  
Y := SimplifiedModel(Y);
assert #Automorphisms(Y) eq 2;

J := Jacobian(Y);

pts := [Y![1,-1,0], Y![1,1,0], Y![1,0,1]];

D1 := Place(Y![1,1,0])-Place(Y![1,-1,0]);
infdiv := Place(pts[1]) + Place(pts[2]);

resolvant:=function(f);
        assert Degree(f) eq 4;
        f:=f/LeadingCoefficient(f);
        Qv<v>:=Parent(f);
        d,c,b,a := Explode(Coefficients(f));
        assert f eq v^4+a*v^3+b*v^2+c*v+d;
        C:=v^3-2*b*v^2+(b^2+a*c-4*d)*v+(c^2+a^2*d-a*b*c);
        assert Discriminant(C) eq Discriminant(f);
        return C;
end function;

lst:=[* *];
for a in [0..18] do	
	if a ne 0 then
		D:=a*D1+2*infdiv;
		L,phi:=RiemannRochSpace(D);
		assert Dimension(L) eq 2;
                if #Decomposition(D+Divisor(phi(u*L.1+L.2))) eq 1 then
                	E := Decomposition(D+Divisor(phi(u*L.1+L.2)))[1,1];
                       	F := ResidueClassField(E);
                       	f := MinimalPolynomial(F.1);
                       	assert Degree(f) eq 4;
                       	C:=resolvant(f);
                       	print a, IsIrreducible(f), IsIrreducible(C);
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
                       	print H, a,gen,pts;
			for pt in pts do
				print "computing the Galois group corresponding to", pt;
				u1:=pt[1];
				v1:=pt[3];
				E1 := Decomposition(D+Divisor(phi(u1*L.1+v1*L.2)));
				if #E1 eq 1 and E1[1,2] eq 1 then
					E1:=E1[1,1];
					F1 := ResidueClassField(E1);
                               		f := Qx!MinimalPolynomial(F1.1);
                               		assert Degree(f) eq 4;
                               		C:=resolvant(f);
					IsIrreducible(f), IsIrreducible(C); 
					G:=GaloisGroup(f);
					print G;
				else
					print "divisor is reducible";
				end if;
			end for;
                    	print "++++++++++++++++++++";
               	end if;
	end if;
end for;
