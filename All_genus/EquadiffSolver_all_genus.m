/*  

    Toolbox for computing isogenies between Jacobians of hyperelliptic curves
    in the p-adics where p is odd. We solve the system of diff equations 
    using a Newton iteration. 
    
    Remark: One should have an initial condition for the ODE in order to use this program 


    Copyright (C) 2020 Elie Eid

*/


/*    The following is a self-contained magma script that implements the algorithm of the paper 
    " Fast compuation of hyperelliptic curve isognies in odd characteristic" by E. Eid. 

*/


Iso_t := recformat<f, X0, Y0, G, PRC0>;
Iso_t1 := recformat<f, X0, Y0, G>;


forward IsoSolveInternal, MyMatrixInv, IsoSolveInternal_op , MySqrtInvE, MySqrtInvPad, MySqrtInv, MatrixChangePrecision, integral, MyInv;



// The main function: we look for an (ell,ell,...,ell)-isogeny defined over the p-adics from 
// the Jacobian of the curve y^2 = hC 
// to 
// the Jacobian of the curve y^2 = hD.

// The normalization matrix is _Mij 
// The initial condition of the differential system is _X0 

// The p-adic precision is equal to PrP


function EquadifSolver(ell , hC , hD , _Mij, _X0, _Y0, _u0 , _v0, PrP)

   
    
    vprintf SEA, 1 : "Precomputations...\n";


    CK := Parent(_u0); /* The p-adic field*/ 
    PDef := DefiningPolynomial(CK);
    p := Prime(CK); 
    K := pAdicQuotientRing(p, PrP); 
    
    if PDef ne Parent(PDef).1-1 then
	K<u> := UnramifiedExtension(K, DefiningPolynomial(CK));
    end if;

    x := PolynomialRing(K).1;
    L := LaurentSeriesRing(K : Precision := ell+2); t := L.1;

    Mij := ZeroMatrix(L, NumberOfRows(_Mij) , NumberOfColumns(_Mij));
    X0 := ZeroMatrix(L , NumberOfRows(_X0) , NumberOfColumns(_X0));
    Y0 :=  ZeroMatrix(L , NumberOfRows(_Y0) , NumberOfColumns(_Y0));

    for i:=1 to  NumberOfRows(_Mij) do  
        X0[i,1]:= K!ChangeUniverse(Eltseq(_X0[i,1]), Integers());
        Y0[i,1]:= K!ChangeUniverse(Eltseq(_Y0[i,1]), Integers());
        for j:=1 to NumberOfColumns(_Mij) do 
            Mij[i,j]:= L!ChangeUniverse(Eltseq(_Mij[i,j]), Integers());
        end for;
    end for;


    u0 := K!ChangeUniverse(Eltseq(_u0), Integers());
    v0 := K!ChangeUniverse(Eltseq(_v0), Integers());

   
    N := ell +1;
    u := t + u0;

    h := Parent(x)![ K!ChangeUniverse(Eltseq(Coefficient(hC , i-1)), Integers()) : i in [1..2*NumberOfColumns(Mij) + 2] ];
    h := Evaluate(h, u);

   

    r0 := 1 div v0;
    r1 := - (Coefficient(h,1) * r0) div (2*Coefficient(h,0));
    r2 := -(r0 * Coefficient(h,2)) div (2*Coefficient(h,0)) - (r1^2) div (2*r0) - ( r1 * Coefficient(h,1)) div Coefficient(h,0);
    vinv := MySqrtInv(h, N : Timings := [], PRC0 := [* 2, [*r0 + r1*t + r2*t^2 *] *] );


    G := Matrix(L , [ [u^i] : i in [0..NumberOfRows(Mij) - 1]  ]);
    G := vinv*Mij * G ;


    h2 := Parent(x)![ K!ChangeUniverse(Eltseq(Coefficient(hD , i-1)), Integers()) : i in [1..2*NumberOfColumns(Mij) + 2] ];
    Prc:= rec<Iso_t1 | f :=h2 , X0:= X0 , Y0 := Y0, G := G>;
    
    tm := Cputime();

    X := IsoSolveInternal_op(4, Prc);
    Yi := Matrix(  [  [MySqrtInvE( Evaluate( h2 , X[i,1]) , 3 , 1/Y0[i,1])]  : i in [1..NumberOfRows(Y0)]] )  ;
    PRC0 := [ [* 2 , [*Yi[i,1]*] *] : i in [1..NumberOfRows(Y0)] ];   

    timings := Cputime(tm);

    Prc:= rec<Iso_t | f :=h2 , X0:= X , Y0 := Y0, G := G, PRC0 := PRC0 >;

    X , Timings := IsoSolveInternal(N , Prc);

    return X, Timings cat [timings];

end function;



function IsoSolveInternal_op(N, Prc);

    L := Parent(Prc`G[1,1]); t := L.1;

    if N le 1 then
	X := MatrixChangePrecision(Prc`X0,N);

	return X, [* 0, [**] *];
    end if;


    M :=Ceiling((N)/2);

    X , PRC0  :=IsoSolveInternal_op(M, Prc) ;
    
   
    
    X:= MatrixChangePrecision(X, N);
    
   
    /* X0'*/
    Xp := Matrix(L , [ [ Derivative(X[i,1]) ] :i in [1..NumberOfRows(X)]]);
    
    
    /* Computation of 1/yi*/
    Yi := Matrix(L , [  [ MySqrtInvE(Evaluate( Prc`f , X[i,1]) , N , 1/ Prc`Y0[i,1])] : i in  [1..NumberOfRows(X)]  ]);


   /* The matrix H */
    n := NumberOfRows(Prc`X0);
    H := ZeroMatrix(L ,n , n);
    for j:= 1 to n do 
        H[1,j]:= Yi[j,1];
    end for;

    for i := 2 to n do  
        for j:= 1 to n do 
            H[i,j]:= X[j,1]*H[i-1, j];
        end for;
    end for;

    /* Inverse H */ 
    Hinv, PRC0 := MyMatrixInv(H, N-1 : PRC0 := PRC0);


    /* Computation of e = G - H * X'*/ 
    e := H * Xp;
    e := Prc`G - e ; 


    /* Computation of the integral of e*/
    for i := 1 to n do 
        e[i,1] := integral(e[i,1]);
    end for;

    /* Computation of the new approx */
    e := Hinv * e;
    X := X + e;
    X := MatrixChangePrecision(X, N);

    
    return X , PRC0 ;

end function;




function IsoSolveInternal(N, Prc : Timings := []);

    L := Parent(Prc`G[1,1]); t := L.1;

    if N le 3 then
    Tm := Cputime();
	vprintf SEA, 1 : "From                1 to (N =) %8o ...", N;
	X := MatrixChangePrecision(Prc`X0,N);

	return X, [RealField(6) | 0 : i in [1..6]] , Prc`PRC0 , [* 0, [**] *];
    end if;


    M := Max(3 , Ceiling((N)/2));

    X ,_Timings, PRC0, PRC1:=IsoSolveInternal(M, Prc : Timings:= Timings) ;
    
    Tm := Cputime();
    vprintf SEA, 1 : "From (M+1 =) %8o to (N =) %8o ...", M+1, N;
    vprintf SEA, 2 : "\n";
    
    X:= MatrixChangePrecision(X, N);
    
    

     idxtm := 0;
    
    /* X0'*/
    
    tm := Cputime();

    Xp := Matrix(L , [ [ Derivative(X[i,1]) ] :i in [1..NumberOfRows(X)]]);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  X'\t\t: %o\n", Cputime(tm);
    
    /* Computation of 1/yi */
    tm := Cputime();

    Yi := Matrix(L , [  [ MySqrtInv(Evaluate( Prc`f , X[i,1]) , N : PRC0:= PRC0[i])] : i in  [1..NumberOfRows(X)]]);
    PRC0 := [ [* Max(N- M , 2) , [* ChangePrecision( Yi[i,1] , N- M) *] *] : i in  [1..NumberOfRows(X)] ];

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Square Roots\t\t: %o\n", Cputime(tm);

   /* The matrix H */
    tm := Cputime();

    n := NumberOfRows(Prc`X0);
    H := ZeroMatrix(L ,n , n);
    for j:= 1 to n do 
        H[1,j]:= Yi[j,1];
    end for;

    for i := 2 to n do  
        for j:= 1 to n do 
            H[i,j]:= X[j,1]*H[i-1, j];
        end for;
    end for;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  The matrix H\t\t: %o\n", Cputime(tm);


    /* Inverse H */ 
    tm := Cputime();
    Hinv, PRC1 := MyMatrixInv(H, N-1 : PRC0 := PRC1);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Inverse of H\t\t: %o\n", Cputime(tm);


    /* Computation of e = G - H * X'*/ 
    tm:= Cputime();

    e := H * Xp;
    e := Prc`G - e ; 

    /* Computation of the integral of e*/

    for i := 1 to n do 
        e[i,1] := integral(e[i,1]);
    end for;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Integral of e\t\t: %o\n", Cputime(tm);

    /* Computation of the new approx */
    tm := Cputime();

    e := Hinv * e;
    X := X + e;
    X := MatrixChangePrecision(X, N);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Newton Formula\t\t: %o\n", Cputime(tm);

    return X , _Timings , PRC0, PRC1;

end function;




function MatrixChangePrecision(M,N)
    n := NumberOfRows(M);
    m := NumberOfColumns(M);
    for i :=1 to n do 
        for j :=1 to m do 
            ChangePrecision(~M[i,j] , N);
        end for;
    end for;
    return M;
end function;

 


function MySqrtInvE(T,N,T0)

    L:=Parent(T); t := L.1;
    ChangePrecision(~T,N);
    if N le 1 then 
        return L!T0;
    end if;

    M := Ceiling( (N)/2);
    
    u := MySqrtInvE(T,M,T0);
    ChangePrecision(~u , N);
    return (u/2)*(-T*u^2 +3);

end function;



function MySqrtInvPad(A, n : Timings := [], PRC0 := [* 2, [**] *])

    L := Parent(A); t := L.1;
    K := BaseRing(L); PR := PolynomialRing(K);

    N := ( AbsolutePrecision(A) - 1 ) div 2;
    
    // Initial condition (precision 2 is needed..)
    if n le PRC0[1] then
	Tm := Cputime();
	
	vprintf SEA, 2 : "\tFrom            1 to (n =) %3o", n;

	if #(PRC0[2]) ne 0 then
	    H := PRC0[2, 1];
	else
	    vprintf SEA, 3 : "\n";

	    FF, redmap := ResidueClassField(K);
	    Px := PolynomialRing(FF); x := Px.1;
	    LF := ChangeRing(L, FF); f := LF.1;
	    
	    tm := Cputime();
	    Cof, v := Coefficients(A);
	    Ax := Px!Cof; if v ne 0 then Ax *:= x^v; end if;
	    h0 := LF!Sqrt(Ax); ChangePrecision(~h0, N+1);
	    vprintf SEA, 3 : "\t\t... h0\t\t\t: %o\n", Cputime(tm);
	    
	
	    tm := Cputime();
	    Cof, v := Coefficients(h0);
	    H := L!Cof; if v ne 0 then H *:= t^v; end if; ChangePrecision(~H, N+1);
	    vprintf SEA, 3 : "\t\t... H0\t\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    G := ChangePrecision(A, N+1) - H^2;
	    Cof, v := Coefficients(G); Gx := Px!((PR!Cof) div 4);
	    g := LF!Coefficients(Gx); if v ne 0 then g *:= t^v; end if; ChangePrecision(~g, N+1);
	    vprintf SEA, 3 : "\t\t... (F-H0^2)/4\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    f0 := 1/h0;
	    vprintf SEA, 3 : "\t\t... f0 := 1/h0\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    g := g*f0^2;
	    vprintf SEA, 3 : "\t\t... g*f0^2\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    Cof, v := Coefficients(f0);
	    F0 := L!Cof; if v ne 0 then F0 *:= t^v; end if; ChangePrecision(~F0, N+1);
	    vprintf SEA, 3 : "\t\t... F0\t\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    F0 := F0^2;
	    vprintf SEA, 3 : "\t\t... F0^2\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    cf := [FF|0 : i in [0..N] ];
	    cf[1] := Roots(x^2 + x + Coefficient(g, 0))[1, 1];	
	    for i := 1 to N do
		e := Coefficient(g, i);
		if i mod 2 eq 0 then e +:= cf[1+(i div 2)]^2; end if;
		cf[1+i] := e;
	    end for;
	    h1 := LF!cf + O(f^(N+1));
	    h1 *:=  h0;
	    vprintf SEA, 3 : "\t\t... h1\t\t\t: %o\n", Cputime(tm);
	    
	    tm := Cputime();
	    Cof, v := Coefficients(h1);
	    H1 := L!Cof; if v ne 0 then H1 *:= t^v; end if; ChangePrecision(~H1, N+1);	
	    H -:= 2*H1;
	    vprintf SEA, 3 : "\t\t... h0-2*h1\t\t: %o\n", Cputime(tm);

	    tm := Cputime();
	    H := H * F0;
	    vprintf SEA, 3 : "\t\t... (h0-2*h1)*F0^2\t: %o\n", Cputime(tm);

	end if;

	vprintf SEA, 2 : "\t... %o s\n", Cputime(Tm);
	    
	    
	return H, [RealField(6) | Cputime(Tm), 0, 0, 0, 0 ];
    end if;

    // Let us recurse
    m := Max(2, (n+2) div 2);
    R, _Timings   := MySqrtInvPad(A, m : Timings := Timings, PRC0 := PRC0);

    vprintf SEA, 2 : "\tFrom   (m+1=) %3o to (n =) %3o", m+1, n;
	vprintf SEA, 3 : "\n";
    Tm := Cputime(); idxtm := 1;

    _A := ChangePrecision(A, N+1); _R := ChangePrecision(R, N+1);

    // Newton iteration
    tm := Cputime();
    H := -_R^2;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... R^2 \t\t: %o\n", Cputime(tm);

    tm := Cputime();
    H *:= _A; H +:= 3;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... 3-A*R^2\t\t: %o\n", Cputime(tm);

    tm := Cputime();
    Cof, v := Coefficients(H);
    H := L!Coefficients((PR!Cof) div 2); if v ne 0 then H *:= t^v; end if; ChangePrecision(~H, N+1);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... (3-A*R^2)/2\t\t: %o\n", Cputime(tm);

    tm := Cputime();
    H *:= _R;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... R*(3-A*R^2)/2\t: %o\n", Cputime(tm);

    vprintf SEA, 2 : "\t... %o s\n", Cputime(Tm);

    return H, _Timings;

end function;


// R_(i+1) = R_i + R_i/2 * (A*R_i^2 - 1)
function MySqrtInv(A, N : Timings := [], PRC0 := [* 2, [**] *] )

    L := Parent(A); t := L.1;
    K := BaseRing(L); PR := PolynomialRing(K);

    // Initial condition
    N0 := PRC0[1];
    if N le N0 then
	Tm := Cputime();
	
	vprintf SEA, 2 : "\tFrom            1 to (n =) %3o", N;

	if #(PRC0[2]) ne 0 then
	    H := PRC0[2, 1]; _Timings := [RealField(6) | Cputime(Tm), 0, 0, 0, 0 ];
	else
	    H, _Timings := MySqrtInvPad(ChangePrecision(A, N+1), Precision(K));
	end if;
	vprintf SEA, 2 : "\t... %o s\n", Cputime(Tm);
	    
	return H, [RealField(6) | Cputime(Tm), 0, 0, 0, 0 ];
    end if;

    // Let us recurse
    M := Max(N0, ((N+2)) div 2);

    R, _Timings, _   := MySqrtInv(A, M : Timings := Timings, PRC0 := PRC0);

    vprintf SEA, 2 : "\tFrom   (M+1=) %3o to (N =) %3o", M+1, N;
    vprintf SEA, 3 : "\n";
    Tm := Cputime(); idxtm := 1;

    _A := ChangePrecision(A, N+1); _R := ChangePrecision(R, N+1);

    // Newton iteration
    tm := Cputime();
    H := -_R^2;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... R^2 \t\t: %o\n", Cputime(tm);

    tm := Cputime();
    H *:= _A; H +:= 3;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... 3-A*R^2\t\t: %o\n", Cputime(tm);

    tm := Cputime();
    Cof, v := Coefficients(H);
    H := L!Coefficients((PR!Cof) div 2); if v ne 0 then H *:= t^v; end if; ChangePrecision(~H, N+1);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... (3-A*R^2)/2\t\t: %o\n", Cputime(tm);

    tm := Cputime();
    H *:= _R;

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 3 : "\t\t... R*(3-A*R^2)/2\t: %o\n", Cputime(tm);

    vprintf SEA, 2 : "\t... %o s\n", Cputime(Tm);

    return H, _Timings;

end function;


function integral(f)  //Outputs g = int(f) such that g(0)=0

    if IsWeaklyZero(f) then
        return ChangePrecision(f, AbsolutePrecision(f)+1);
    else
        coeff, a := Coefficients(f);
        return ChangePrecision(Parent(f) ! ([0 : i in [0..a]] cat [coeff[i] div (i+a) : i in [1..Degree(f)-a+1]]), AbsolutePrecision(f)+1);
    end if;
    
end function;



function MyInv(A, N : PRC0 := [* 0, [**] *])

    L := Parent(A); t := L.1;

    if N lt PRC0[1] or N eq 0 then
	if #(PRC0[2]) eq 0 then
	    H := Coefficient(A, 0)^(-1) + O(t);
	    return H, [* 0, [* H *] *];
	end if;
	return PRC0[2, 1], PRC0;
    end if;

    // Let us recurse
    B, _ := MyInv(A, N div 2 : PRC0 := PRC0);
    ChangePrecision(~B, N+1);

    H  := 2 - B * ChangePrecision(A, N+1);
    H *:= B;
    
    return H, [* N, [* H *] *];
    
end function;


function PartialGCD(U, V, z, s)

    Px := Parent(U); X := Px.1; n := Degree(U);

    if s gt Degree(V) then
    return IdentityMatrix(Px, 2);
    end if;

    if s eq Degree(V) then
    return Matrix(2,2,[Px | 0, 1, 1, - (U div V) ]);
    end if;

    m := s - (n - z);
    pi_left := $$(U div X^m, V div X^m, z-m, Ceiling((z+s)/2)-m);

    next := Vector([U, V])*pi_left;
    nU := next[1]; nV := next[2];

    m := 2*s - Degree(nU);
    pi_right := $$(nU div X^m, nV div X^m, Ceiling((z+s)/2)-m,s-m);

    return pi_left * pi_right;

end function;


function FastBerlekampMassey(ell, T)

    L := Parent(T); t := L.1;
    K := CoefficientRing(L); PR := PolynomialRing(K); x := PR.1;

    U := x^(2*ell);

    C, v := Coefficients(T);
    V := (x^v * Parent(x)!C) mod U;

    vprintf SEA, 2 : "\t PartialGCD ";
    Tm := Cputime();
    PI := PartialGCD(U, V, (2*ell), (2*ell +1) div 2);
    vprintf SEA, 2 : "... done in %o\n", Cputime(Tm);

    A := V*PI[2, 2] mod x^(2*ell);
    B := PI[2, 2];
    return A, B;

end function;



function PadicToFF(T)

    L := Parent(T); K := BaseRing(L);

    FF, redmap := ResidueClassField(K);
    Px := PolynomialRing(FF); x := Px.1;
    
    Lp := ChangeRing(L, FF);

    Tp := Lp!T;

return Tp;

end function;


function MyMatrixInv(A, N : PRC0 := [* 0, [**] *])

    L := CoefficientRing(A); t := L.1;
    F := BaseRing(L);

    if N lt PRC0[1] or N eq 0 then
	if #(PRC0[2]) eq 0 then
        n := NumberOfRows(A); m := NumberOfColumns(A);
        A0 := ZeroMatrix(F , n ,m);
        for i:= 1 to n do 
            for j:= 1 to m do 
                A0[i,j]:= Coefficient(A[i,j],0);
            end for;
        end for;
        H := A0^(-1);
        H := MatrixChangePrecision(Matrix(L ,H ) , 1);
	    return H, [* 0, [* H *] *];
	end if;

	return PRC0[2, 1], PRC0;

    end if;

    // Let us recurse
    B, _ := MyMatrixInv(A, N div 2 : PRC0 := PRC0);
    B:= MatrixChangePrecision(B, N+1);

    H  := 2*B -  B*MatrixChangePrecision(A, N+1)*B ;
  
    
    return H, [* N, [* H *] *];
    
end function;



function Tree(a) // Given a vector a0,...,am compute the subproduct tree 
                // defined with the polynomials x-a0,...,x-am.
    
     _<x> := PolynomialRing(Parent(a[1]));
    M0j := [x-i : i in a];
    T := [M0j]; 
    m0 := #a;
    m := [m0]; h:=[];

    for i := 1 to Ceiling(Log(2,#a)) do
        h0 := Floor(m0/2); Append(~h,h0);
        for j := 0 to h0-1 do
            M0j[j+1] := M0j[2*j+1]*M0j[2*j+2];   end for;
        if m0 mod 2 eq 0 then   m0:= h0;  M0j := [M0j[i] : i in [1..m0]];
        else M0j[h0+1] := M0j[m0]; m0:= h0+1; M0j := [M0j[i] : i in [1..m0]]; end if;


    Append(~T,M0j); Append(~m , m0);
      
    end for;
    Append(~h,0);

    return <T, m,h> ;

end function;



// Scalar multiplication in the Jacobian of a hyperelliptic curve (Cantor algorithm)

function WeakPolynomial(f)
    coef := Coefficients(f);
    for i := 1 to #coef do  
        if IsWeaklyZero(coef[i]) then coef[i]:=0; end if;
    end for;
    return Parent(f)!coef;
end function;



function DivisorComposition(D,Dp,f,g)

    u := D[1]; v:= D[2]; up := Dp[1]; vp := Dp[2];
    
    if u eq 1 then return [up,vp]; end if;
    if up eq 1 then return [u,v]; end if;

    dp,e,ep := XGCD(u,up);

    if dp eq 0 then 
        uu := WeakPolynomial(u);
        uup := WeakPolynomial(up);
        dp,e,ep := XGCD(uu, uup);
    end if;


    d,c,cp := XGCD(dp, v+ vp);

    if d eq 0 then 
        dp := WeakPolynomial(dp);
        vvp := WeakPolynomial(v+vp);
        d,c,cp := XGCD(dp, vvp);
    end if;


    s := c*e; s2 := c* ep; s3 := cp;
    upp := (u*up) div d^2;
    vpp := ((s*u*vp + s2*up*v + s3*(v*vp + f)) div d) mod upp;

    while Degree(upp) gt g do  
        upp := WeakPolynomial(upp);
        vpp := WeakPolynomial(vpp);

        U := (f-vpp^2) div upp; V := (-vpp) mod U;
        upp:=U;
        vpp:=V;
    end while;

return [upp , vpp] ;

end function;


function DoubleAndAdd(D , n)

    J:=Parent(D);
    H := Curve(J);
    f, _ := HyperellipticPolynomials(H);
    g := Genus(H);

    L := Reverse(IntegerToSequence(n , 2));
    R:=[*[1,0], [1,0]*];

    for i in L do 
        R[2]:= DivisorComposition(R[2],R[2],f,g);
        R[i+1] := DivisorComposition(R[i+1]  , D , f,g);
    end for;
    return R[2];

end function;
