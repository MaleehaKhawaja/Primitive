//This code written by Ozman and Siksek associated to the article "Quadratic points on modular curves".
//link: https://arxiv.org/pdf/1806.08192.pdf
//It is used by Najman and Vukorepa to determine the torsion subgroup of X0(60)
//in their article, and we use it for the same purpose.

// Section 1: Functions for Abelian group theory.
//
// Section 2: Functions for general non-hyperelliptic curves X/\Q 
//	      of genus \ge 3 with Mordell--Weil rank 0.

//---------------------------------------------------------
//
// Section 1: Functions for Abelian group theory. 
//
//-------------------------------------------------------- 


//                i1       pi1
// Given 0--> C1 -----> A1 -----> B1 -->0
//            |                   |                              
//            phi                mu  
//            |                   |
//            V                   V
//      0--> C2 -----> A2 -----> B2 -->0
//               i2         pi2
// with top and bottom row exact sequence of finite abelian groups
// and phi, mu isomorphisms, is there an isomorphism psi : A1 --> A2
// making the diagram commute?
extenProb:=function(phi,mu,i1,i2,pi1,pi2);
    C1:=Domain(i1);
    C2:=Domain(i2);
    assert C1 eq Domain(phi);
    assert C2 eq Codomain(phi);
    A1:=Domain(pi1);
    A2:=Domain(pi2);
    assert A1 eq Codomain(i1);
    assert A2 eq Codomain(i2);
    B1:=Codomain(pi1);
    B2:=Codomain(pi2);
    assert B1 eq Domain(mu);
    assert B2 eq Codomain(mu);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    assert Image(pi1) eq B1;
    assert Image(pi2) eq B2;
    assert Kernel(pi1) eq Image(i1);
    assert Kernel(pi2) eq Image(i2);
    assert #Kernel(phi) eq 1;
    assert #Kernel(mu) eq 1;
    assert #C1 eq #C2;
    assert #B1 eq #B2;
    if #B1 eq 1 then
        // In this case i1 and i2 are isomorphisms.
        return true, hom<A1->A2 | [ i2(phi(a@@i1)) : a in OrderedGenerators(A1)]>;
    end if;
    Q,modC1:=quo< A1 | sub<A1  | [i1(c) : c in OrderedGenerators(C1)]> >;
    Qgens:=OrderedGenerators(Q);
    r:=#Qgens;
	xs:=[q@@modC1 : q in Qgens]; // x1,..xr together with i1(C1) generates A1.
    ys:=[(mu(pi1(x)))@@pi2 : x in xs];
    Zr:=FreeAbelianGroup(r);
    pretau:=hom<Zr->A1 | xs>;
    Astar,j1,j2,pj1,pj2:=DirectSum(Zr,C1); //Z^r x C_1.
    // j1, j2 are the inclusion maps Z^r --> A^*, C_1 --> A^*.
    // pj1, pj2 are the projection maps A^* --> Z^r, A^* --> C_1.
    //tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@@i1 : d in OrderedGenerators(Astar)]>;
    tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@i1 : d in OrderedGenerators(Astar)]>;
    K:=Kernel(tau);
    Kgens:=OrderedGenerators(K);
    s:=#Kgens;
    clist:=[ i2(phi(pj2(Astar!k))) : k in Kgens];
    nlist:=[ Eltseq(pj1(Astar!k)) : k in Kgens];
    Cr,Crinjs,Crprojs:=DirectSum([C2 : i in [1..r]]);
    Cs,Csinjs,Csprojs:=DirectSum([C2 : i in [1..s]]);
    Crgens:=[ [Crprojs[i](delta) : i in [1..r]] : delta in OrderedGenerators(Cr)];
    dotprod:=func<nn,tt | &+[ nn[i]*tt[i] : i in [1..#tt]]>;
	eta:=hom<Cr->Cs | [  &+[ Csinjs[j](dotprod(nlist[j],crgen)) : j in [1..s]   ]      : crgen in Crgens ]  >;
    testelt:=-1*&+[ Csinjs[j]((clist[j]+dotprod(nlist[j],ys))@@i2) : j in [1..s]];
    I:=Image(eta);
    if testelt in I then
        tlist:=testelt@@eta;
        tlist:=[Crprojs[i](tlist) : i in [1..r]];
        presigma:=hom<Zr->A2 | [ys[i]+i2(tlist[i]) : i in [1..r]]>;
        sigma:=hom<Astar->A2 | [presigma(pj1(d))+i2(phi(pj2(d))) : d in OrderedGenerators(Astar)]>;
        psi:=hom<A1->A2 | [ sigma(a@@tau) : a in OrderedGenerators(A1)]>;
        assert #Kernel(psi) eq 1;
        assert #A1 eq #A2; // psi is really an isomorphism.
        assert &and[psi(i1(c)) eq i2(phi(c)) : c in OrderedGenerators(C1)];
        assert &and[mu(pi1(a)) eq pi2(psi(a)) : a in OrderedGenerators(A1)];
        // And it really makes the diagram commutative.
        return true, psi;
    else
        return false;
    end if;
end function;


// i1 : C --> A1
// i2 : C --> A2
// injective homomorphisms of finite abelian groups.
// Is there an isomomorphism psi: A1 --> A2
// making the triangle commute? 
homExtend:=function(i1,i2);
    assert Domain(i1) eq Domain(i2);
    C:=Domain(i1);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    A1:=Codomain(i1);
    A2:=Codomain(i2);
    if IsIsomorphic(A1,A2) eq false then
            return false;
    end if;
    B1,pi1:=quo<A1 | Image(i1)>;
    B2,pi2:=quo<A2 | Image(i2)>;
    tf,mu1:=IsIsomorphic(B1,B2);
    if tf eq false then
        return false;
    end if;
	phi:=hom<C->C | [c : c in OrderedGenerators(C)]>; // The
    // identity map C-->C.
    mapautB2,autB2:=PermutationRepresentation(AutomorphismGroup(B2));
    for kappa in autB2 do // autB2 is a permutation group that
                        // is isomorphic to the automorphism group of B2.
        eta:=kappa@@mapautB2; // This converts the permutation into an
                            // an automorphism of B2.
        mu:=hom<B1->B2 | [  eta(mu1(b)) : b in OrderedGenerators(B1) ]>;
                        // As kappa runs through the elements of autB2
                        // mu runs through the isomorphisms B1-->B2.
        tf:=extenProb(phi,mu,i1,i2,pi1,pi2);
        if tf then
            return true;
        end if;
    end for;
    return false;
end function;



//---------------------------------------------------------
//
// Section 2: Functions for general non-hyperelliptic curves
//		of genus \ge 3.
//
//-------------------------------------------------------- 

// This code assumes that X/\Q is a non-hyperelliptic
// curve (genus \ge 3) with Mordell-Weil rank 0.

// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.

reduceDiv:=function(X,Xp,D);
	if Type(D) eq DivCrvElt then
		decomp:=Decomposition(D);
		return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;
	assert Type(D) eq PlcCrvElt;
	if  Degree(D) eq 1 then
		P:=D;
		R<[x]>:=CoordinateRing(AmbientSpace(X));
		n:=Rank(R);
		KX:=FunctionField(X);
		inds:=[i : i in [1..n] | &and[Valuation(KX!(x[j]/x[i]),P) ge 0 : j in [1..n]]];	
		assert #inds ne 0;
		i:=inds[1];
		PP:=[Evaluate(KX!(x[j]/x[i]),P) : j in [1..n]];
		denom:=LCM([Denominator(d) : d in PP]);
		PP:=[Integers()!(denom*d) : d in PP];
		g:=GCD(PP);
		PP:=[d div g : d in PP];
		Fp:=BaseRing(Xp);
		PP:=Xp![Fp!d : d in PP];
		return Place(PP);	
	end if;
	I:=Ideal(D);
	Fp:=BaseRing(Xp);
	p:=Characteristic(Fp);
	B:=Basis(I) cat DefiningEquations(X);
	n:=Rank(CoordinateRing(X));
	assert Rank(CoordinateRing(Xp)) eq n;
	R:=PolynomialRing(Integers(),n);
	BR:=[];
	for f in B do
		g:=f*p^-(Minimum([Valuation(c,p) : c in Coefficients(f)]));
		g:=g*LCM([Denominator(c) : c in Coefficients(g)]);
		Append(~BR,g);
	end for;
	J:=ideal<R | BR>;
	J:=Saturation(J,R!p);
	BR:=Basis(J);
	Rp:=CoordinateRing(AmbientSpace(Xp));
	assert Rank(Rp) eq n;
	BRp:=[Evaluate(f,[Rp.i : i in [1..n]]) : f in BR];
	Jp:=ideal<Rp| BRp>;
	Dp:=Divisor(Xp,Jp);
	return Dp;
end function;


// divs are a bunch of known effective divisors,
// P0 is a base point of degree 1,
// p>2 is a prime of good reduction.
// This determines an abstract abelian group Ksub
// isomorphic to the group spanned by [D-deg(D) P_0] 
// where D runs through the elements of divs.  
// It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew]
// generates the same subgroup.
// It also determines a homomorphism 
// h : \Z^r --> Ksub
// where divsNew=[D_1,..,D_r]
// and h([a_1,..,a_r]) is the image of 
// a_1 (D_1-deg(D_1) P_0)+\cdots + a_r (D_r-deg(D_r) P_0)
// in Ksub.

findGenerators:=function(X,divs,P0,p);
	fn:=func<A,B| Degree(A)-Degree(B)>;
	Sort(~divs,fn); // Sort the divisors by degree.
	assert IsPrime(p);
	assert p ge 3;
	Xp:=ChangeRing(X,GF(p));
	assert IsSingular(Xp) eq false; // Now we know that
	// J_X(Q)-->J_X(\F_p) is injective (we're assuming rank 0).
	C,phi,psi:=ClassGroup(Xp);
	Z:=FreeAbelianGroup(1);
	degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
	A:=Kernel(degr); // This is isomorphic to J_X(\F_p).
	Pp0:=reduceDiv(X,Xp,P0);
	divsRed:=[reduceDiv(X,Xp,D) : D in divs];
	divsRedA:=[psi(D-Degree(D)*Pp0) : D in divsRed]; // The image of the divisors in A;
	Ksub1:=sub<A | divsRedA>; // The subgroup of J(\F_p) generated by
							// [D-deg(D)*P_0] with D in divs.	
	// Next we eliminate as many of the divisors as possible
	// while keeping the same image.
	r:=#divs;
	inds:=[i : i in [1..r]];
	i:=r+1;
	repeat
		i:=i-1;
		indsNew:=Exclude(inds,i);
		if sub<A | [divsRedA[j] : j in indsNew]> eq Ksub1 then
			inds:=indsNew;
		end if;
	until i eq 1;
	divsNew:=[divs[j] : j in inds];
	divsRedA:=[divsRedA[j] : j in inds];
	r:=#divsNew;	
	Zr:=FreeAbelianGroup(r);
	h:=hom<Zr->A | divsRedA>;
	Ksub:=Image(h); // Stands from known subgroup.
	assert Ksub eq Ksub1;
	h:=hom<Zr->Ksub | [ Ksub!h(Zr.i) :  i in [1..r] ]>;
	// Restrict the codomain of h so that it is equal to Ksub.
	bas:=[Eltseq(i@@h) : i in OrderedGenerators(Ksub)];
	return h,Ksub,bas,divsNew;
end function;

// Determine all possible subgroups A of J(F_p) 
// that contain the image of Ksub-->J(F_p)
// and return the induced injective maps Ksub-->A.
reduceHoms:=function(X,divs,P0,Xp,Ksub,bas);
    C,phi,psi:=ClassGroup(Xp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
    J:=Kernel(degr); // This is isomorphic to J_X(\F_p).
    Pp0:=reduceDiv(X,Xp,P0);
    divsRed:=[reduceDiv(X,Xp,D) : D in divs];
    r:=#divsRed;
    Zr:=FreeAbelianGroup(r);
    eta:=hom<Zr->J | [psi(D-Degree(D)*Pp0) : D in divsRed]>;
    pi:=hom<Ksub->J | [ eta(Zr!g) : g in bas]>;
    I:=Image(pi);
    Q,mu:=quo<J | I>;
    subs:=Subgroups(Q);
    subs:=[H`subgroup : H in subs];
    subs:=[ sub<J | [g@@mu : g in OrderedGenerators(H) ] cat OrderedGenerators(I)> : H in subs ];
    homs:=[ hom<Ksub -> H | [H!(pi(g)) : g in OrderedGenerators(Ksub)]> : H in subs ];
    return homs;
end function;

// This function uses reduction modulo the primes in prs
// to determine a set of injections Ksub --> A
// such that for one of these injections, A is isomorphic
// to J(\Q), and Ksub --> A is the natural injection.
possibleJList:=function(X,divs,P0,Ksub,bas,prs);
    p:=prs[1];
    hms:=[* reduceHoms(X,divs,P0,ChangeRing(X,GF(p)),Ksub,bas) : p in prs *];
    homs:=hms[1];
    n:=#prs;
    for i in [2..n] do
        homsi:=hms[i];
        homsNew:=homs;
        for h in homs do
            if &and[homExtend(h,hi) eq false : hi in homsi] then
                Exclude(~homsNew,h);
            end if;
        end for;
        homs:=homsNew;
    end for;
    return homs;
end function;
