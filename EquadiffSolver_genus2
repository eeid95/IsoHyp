/*  

    Toolbox for computing isogenies between Jacobians of genus two curves
    in the p-adics where p is odd. We solve the system of diff equations 
    using a Newton iteration. 
    
    Remark: One should have an initial condition for the ODE in order to use this program 


    Copyright (C) 2020 Elie Eid

*/


/*    The following is a self-contained magma script that implements the algorithm of the paper 
    " Fast compuation of hyperelliptic curve isognies in odd characteristic" by E. Eid, for genus 2 curves. 

*/


Iso_t := recformat<f, X0, Y0, G, PRC0>;

Iso_t1 := recformat<f, X0, Y0, G>;


forward IsoSolveInternal, MySqrtInvE, MySqrtInvPad, MySqrtInv, MatrixChangePrecision, integral, MyInv,IsoSolveInternal_op;


// The main function: we look for an (ell,ell)-isogeny defined over the p-adics from 
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
    L := LaurentSeriesRing(K : Precision := 4*ell+2); t := L.1;

    _m11 := _Mij[1,1]; _m12 := _Mij[1,2]; _m21 := _Mij[2,1]; _m22:= _Mij[2,2];
    _x1_0 := _X0[1,1]; _x2_0:= _X0[2,1];
    _y1_0 := _Y0[1,1]; _y2_0:= _Y0[2,1];

    m11  := K!ChangeUniverse(Eltseq(_m11), Integers());
    m21  := K!ChangeUniverse(Eltseq(_m21), Integers());
    m12  := K!ChangeUniverse(Eltseq(_m12), Integers());
    m22  := K!ChangeUniverse(Eltseq(_m22), Integers());
    x1_0 := K!ChangeUniverse(Eltseq(_x1_0), Integers());
    x2_0 := K!ChangeUniverse(Eltseq(_x2_0), Integers());
    y1_0 := K!ChangeUniverse(Eltseq(_y1_0), Integers());
    y2_0 := K!ChangeUniverse(Eltseq(_y2_0), Integers());
    u0 := K!ChangeUniverse(Eltseq(_u0), Integers());
    v0 := K!ChangeUniverse(Eltseq(_v0), Integers());

    Mij := Matrix( K , [ [m11,m12 ] , [m21,m22]]);
    X0 :=  Matrix( L, [ [x1_0] , [x2_0]]);
    Y0 := Matrix( L , [ [y1_0] , [y2_0]]);

    N := ell +1;
    u := t + u0;

    h := Parent(x)![ K!ChangeUniverse(Eltseq(Coefficient(hC , i-1)), Integers()) : i in [1..6] ];
    h := Evaluate(h, u);

    r0 := 1 div v0;
    r1 := - (Coefficient(h,1) * r0) div (2*Coefficient(h,0));
    r2 := -(r0 * Coefficient(h,2)) div (2*Coefficient(h,0)) - (r1^2) div (2*r0) - ( r1 * Coefficient(h,1)) div Coefficient(h,0);
    vinv := MySqrtInv(h, N : Timings := [], PRC0 := [* 2, [*r0 + r1*t + r2*t^2 *] *] );

    g1 := m11+ m21*u;
    g1:= g1*vinv;

    g2 := m12 + m22*u;
    g2:= g2*vinv;

    G := Matrix(Parent(g1) , [[g1],[g2]]);

    h2 := Parent(x)![ K!ChangeUniverse(Eltseq(Coefficient(hD , i-1)), Integers()) : i in [1..6] ];
    Prc:= rec<Iso_t1 | f :=h2 , X0:= X0 , Y0 := Y0, G := G>;
    
    X := IsoSolveInternal_op(4, Prc);

    _y1 := MySqrtInvE( Evaluate( h2 , X[1,1]) , 3 , 1/Y0[1,1]);
    _y2 := MySqrtInvE( Evaluate( h2 , X[2,1]) , 3 , 1/Y0[2,1]); 

    PRC0 := [ [* 2 , [*_y1*] *] ,[* 2 , [*_y2*] *] ];   

    Prc:= rec<Iso_t | f :=h2 , X0:= X , Y0 := Y0, G := G, PRC0 := PRC0 >;
    return IsoSolveInternal(N , Prc);

end function;




function IsoSolveInternal_op(N, Prc);

    L := Parent(Prc`G[1,1]); t := L.1;

    if N le 1 then
	    X := MatrixChangePrecision(Prc`X0,N);
	    return X;
    end if;


    M :=Ceiling((N)/2);

    X :=IsoSolveInternal_op(M, Prc) ;
    
    
    X:= MatrixChangePrecision(X, N);
    x1 := X[1,1];
    x2 := X[2,1];

    /*
     * N > 1
     ********/

    /* X0'*/
    
    x1p:= Derivative(x1);
    x2p := Derivative(x2);


    /* Computation of 1/yi */
    
    tm := Cputime();
    _y1 := MySqrtInvE(Evaluate( Prc`f , x1) , N , 1/ Prc`Y0[1,1]);
    _y2:= MySqrtInvE(Evaluate( Prc`f , x2) , N , 1/ Prc`Y0[2,1]); 


   /* The matrix G */
   
    tm := Cputime();
    x1y1 :=x1p*_y1;
    x2y2 :=  x2p*_y2;
    g1 := Prc`G [1,1];  g1 := g1 - x1y1 - x2y2;
    g2 := Prc`G [2,1];  g2 := g2 - x1*x1y1 - x2*x2y2;
    
    G  := Matrix (Parent(g1) , [ [integral(g1)] , [integral(g2)]]);

    x1x2 := MyInv(_y1*_y2*(x2-x1), N); 
    M:= Matrix(Parent(g1), [  [x2*_y2 , -_y2] , [-x1*_y1 , _y1] ]   );

    G :=x1x2* M * G;
    
    // The result

    X := X + G;
    X := MatrixChangePrecision(X, N);
    return X ;

end function;




function IsoSolveInternal(N, Prc : Timings := []);

    L := Parent(Prc`G[1,1]); t := L.1;

    if N le 3 then
    Tm := Cputime();
	vprintf SEA, 1 : "From                1 to (N =) %8o ...", N;
	X := MatrixChangePrecision(Prc`X0,N);

	return X, [RealField(6) | 0 : i in [1..5]] , Prc`PRC0 , [* 0, [**] *];
    end if;


    M := Max(3 , Ceiling((N)/2));


    X ,_Timings, PRC0, PRC1:=IsoSolveInternal(M, Prc : Timings:= Timings) ;
    
    Tm := Cputime();
    vprintf SEA, 1 : "From (M+1 =) %8o to (N =) %8o ...", M+1, N;
    vprintf SEA, 2 : "\n";
    
    X:= MatrixChangePrecision(X, N);
    x1 := X[1,1];
    x2 := X[2,1];

    /*
     * N > 1
     ********/
     
    idxtm := 0;
    
    /* X0'*/
    
    tm := Cputime();
    x1p:= Derivative(x1);
    x2p := Derivative(x2);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  X'\t\t: %o\n", Cputime(tm);
    
    /* Computation of 1/yi */
    tm := Cputime();
    _y1 := MySqrtInv( Evaluate( Prc`f , x1) , N : PRC0 := PRC0[1]); 
    PRC01 := [* Max(N-M , 2) , [* ChangePrecision( _y1 , N-M) *] *];
    _y2 := MySqrtInv( Evaluate( Prc`f , x2) , N: PRC0 := PRC0[2]);
    PRC02 := [* Max(N-M ,2), [* ChangePrecision( _y2 , N-M) *] *];
    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Square Roots\t\t: %o\n", Cputime(tm);

   /* The matrix G */
    tm := Cputime();
    x1y1 :=x1p*_y1;
    x2y2 :=  x2p*_y2;
    g1 := Prc`G [1,1];  g1 := g1 - x1y1 - x2y2;
    g2 := Prc`G [2,1];  g2 := g2 - x1*x1y1 - x2*x2y2;
    

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  G - H(X)X'\t\t: %o\n", Cputime(tm);

    tm := Cputime();
    G  := Matrix (Parent(g1) , [ [integral(g1)] , [integral(g2)]]);

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  Integral of G \t\t: %o\n", Cputime(tm);
    
    tm := Cputime();
    x1x2, PRC1 := MyInv(_y1*_y2*(x2-x1), N: PRC0 := PRC1); 
    M:= Matrix(Parent(g1), [  [x2*_y2 , -_y2] , [-x1*_y1 , _y1] ]   );


    vprintf SEA, 2 : "...  The result\t\t: %o\n", Cputime(tm);
    G :=x1x2* M * G;
    

    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "...  The result\t\t: %o\n", Cputime(tm);

    X := X + G;
    X := MatrixChangePrecision(X, N+1);
    return X , _Timings , [PRC01 , PRC02], PRC1;

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


//Newton iteration for computing 1/Sqrt(T)

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



// Newtion iteration for computing 1/A

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
