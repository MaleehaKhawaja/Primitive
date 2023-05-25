//This code was written by Ozman and Siksek, and was used by Box.
//Vukorepa and Najman adapted it in order to compute a different basis for 
//the cuspforms, as described their article: https://arxiv.org/abs/2112.03226https://arxiv.org/abs/2112.03226https://arxiv.org/abs/2112.03226

//We used this code to obtain a model for X0(60).

//B is a basis for Cuspforms(N)
//N is N for which we want the model for X0(N)
//divN is a divisor of N, used only for jMap, divN = 1 is allowed

modformeqns:=function(B,N,prec,divN)
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

	//We commented out this part because it is slow and only potentially simplifies the equations
	/*eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;*/

	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
    	indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
						 // See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
                        					    // of basis for S 
                        					    // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.

	Z:=SmallModularCurve(divN); 
	KZ:=FunctionField(Z);
	qEZ:=qExpansionsOfGenerators(divN,L,prec); // This gives gives qExpansions of the generators
						// of the function field of Z=X_0(n) as Laurent series in q. 
	KX:=FunctionField(X);
	KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
	coords:=[]; // This will contain the generators of the function field of Z as element of the function of X.
	for u in qEZ do
		//We want to express u as an element of the function field of X=X_0(N).
		Su:={};
		d:=0;
		while #Su eq 0 do
			d:=d+1;
			mons:=MonomialsOfDegree(R,d);
			monsq:=[Evaluate(mon,Bexp) : mon in mons];
			V:=VectorSpace(Rationals(),2*#mons);
			W:=VectorSpace(Rationals(),prec-10);
			h:=hom<V->W | 
				[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
				cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
			K:=Kernel(h);
			for a in [1..Dimension(K)] do
				num:=&+[Eltseq(V!K.a)[j]*mons[j] : j in [1..#mons] ];
				denom:=&+[Eltseq(V!K.a)[j+#mons]*mons[j] : j in [1..#mons] ];
				numK:=Evaluate(num,KXgens); 
				denomK:=Evaluate(denom,KXgens);
				if numK ne KX!0 and denomK ne KX!0 then
					Su:=Su join {numK/denomK};
				end if;
			end for;
		end while;
		assert #Su eq 1;
		coords:=coords cat SetToSequence(Su);
	end for;
	phi:=map<X -> Z | coords cat [1]>;
	jd:=Pullback(phi,jFunction(Z,divN));
		P:=AmbientSpace(X);
		R:=CoordinateRing(P);
		assert Rank(R) eq dim;
		num:=Numerator(FunctionField(P)!jd);
		denom:=Denominator(FunctionField(P)!jd);
		num:=Evaluate(num,[R.i : i in [1..(dim-1)]]);
		denom:=Evaluate(denom,[R.i : i in [1..(dim-1)]]);
		deg:=Max([Degree(num),Degree(denom)]);
		num:=Homogenization(num,R.dim,deg);
		denom:=Homogenization(denom,R.dim,deg);
		assert Evaluate(num,KXgens)/Evaluate(denom,KXgens) eq jd;	
		// We compute the degree of j : X_0(N) --> X(1) using the formula
		// in Diamond and Shurman, pages 106--107.
		assert N gt 2;
		dN:=(1/2)*N^3*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)];
		dN:=Integers()!dN;
		degj:=(2*dN)/(N*EulerPhi(N));
		degj:=Integers()!degj; // Degree j : X_0(N)-->X(1)
		degjd:=&+[-Valuation(jd,P)*Degree(P) : P in Poles(jd)];
		assert degj eq degjd;
		// Now if j \ne jd then the the difference j-jd is a rational
		// function of degree at most 2*degj (think about the poles).
		// Hence to prove that j=jd all we have to check is that their
		// q-Expansions agree up to 2*degj+1.
		jdExpansion:=Evaluate(num,Bexp)/Evaluate(denom,Bexp);
		jdiff:=jdExpansion-jInvariant(q);
		assert Valuation(jdiff) ge 2*degj+1; // We have proven the correctness of the j-map jd on X_0(N)
return X, jd;
end function;
