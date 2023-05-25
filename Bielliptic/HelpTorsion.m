//This code is taken from https://github.com/brutalni-vux/QuadPtsBielliptic
//associated to the paper "Quadratic points on bielliptic modular curves" by F. Najman and B. Vukorepa

//some help funcions for working with torsion of X0(60)(Q)

//for divisors D1 and D2, checks if we have a*D1 ~ b*D2 for some (a,b)!=(0,0) mod maxC
AreDependent:=function(D1,D2,maxC);
	found :=false;

	for i in [0..maxC - 1] do
		for j in [0..maxC - 1] do
			if i eq 0 and j eq 0 then
				continue;
			end if;
			b, ff := IsPrincipal(i*D1 - j*D2);
			found := found or b;
		end for;
	end for;

	return found;
end function;

//for divisor D and an array G, check if D is in G
IsInGroup:=function(D, G);
	ret := false;
	for j in [1..#G] do
		b, ff:=IsPrincipal(D - G[j]);
		ret := ret or b;
	end for;
	return ret;
end function;

//for an array of divisors G, check how many [0]s it has (checks duplicates)
CheckDuplicates:=function(G);
	ret := 0;
	for i in [1..#G] do
		b, ff := IsPrincipal(G[i]);
		if b eq true then
			ret := ret +1;
		end if;
	end for;
	return ret;
end function;
