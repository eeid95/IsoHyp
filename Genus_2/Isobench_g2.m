load "EquadifSolver_padics_g2.m";

SetVerbose("SEA", 1);	


p := 7; 
ell := 30; PadicTimings := [];

repeat 

    repeat ell := ell+1; until ell mod p ne 0;

    PrP :=  1+ Floor(Log(p, 4*ell^2));

    "---"; 
    "- p =", p, ", ell =", ell, ", degree =", ell^2, ", PrP = ", PrP;
    "-----------------------------------------";

repeat 

repeat

    FF := GF(p);
    _<x> := PolynomialRing(FF); L<t> := LaurentSeriesRing(FF, 4*ell^2); 
    repeat 
    hC := RandomIrreduciblePolynomial(FF,5);
    H := HyperellipticCurve(hC);
    until #H ne 1;

    J := Jacobian(H);
    repeat Pt:= Random(H); until Pt[2] ne 0 ; P := J![x - Pt[1] , Pt[2]]; Q := ell *P;
   

    until Degree(Q[1]) eq 2 and SplittingField(Q[1]) eq FF and Discriminant(Q[1]) ne 0;


    
    FF := pAdicField(p,40);

    _<x> := PolynomialRing(FF); L<t> := LaurentSeriesRing(FF, 4*ell^2); 
    hC := Parent(x)!hC;
    H := HyperellipticCurve(hC);
    J := Jacobian(H);

    P:= Points(H , - Coefficient(P[1], 0))[1]; P := J![x - P[1] , P[2]];

    Q := J!DoubleAndAdd(P, ell);
    R := Roots(Q[1]);

    until #R eq 2;
   
    Q1 := H![R[1,1] , Evaluate( Q[2] , R[1,1])];
    Q2:= H![R[2,1] , Evaluate( Q[2] , R[2,1])];
    

    FF := pAdicField(p,PrP);
    W<x> := PolynomialRing(FF); L<t> := LaurentSeriesRing(FF, 4*ell^2); 

    _u0 := FF!Evaluate(-P[1] ,0) ; _v0 := FF!Evaluate(P[2],0);
    _X0 := Matrix( FF , [ [Q1[1]] , [Q2[1]] ]);
    _Y0 := Matrix( FF , [ [Q1[2]] , [Q2[2]] ]);
    _Mij := Matrix( FF , [ [ell ,0] , [0 , ell]]);

    
    X, timings := EquadifSolver(4*ell^2  , W!hC , W!hC , _Mij, _X0, _Y0, _u0 , _v0, PrP);

    x1 := X[1,1]; x1 := PadicToFF(x1);
    x2 := X[2,1]; x2 := PadicToFF(x2);

    L<t> := LaurentSeriesRing(GF(p) , 2*ell^2+1);

    tm := Cputime();

    S := x1 + x2;
    Num, Denom:= FastBerlekampMassey( 2*ell^2, S );
    
    
    P:=x1*x2;
    
    Num1 := L!Coefficients(Denom)*L!P;

    Append(~PadicTimings , <ell^2 , &+timings , Cputime(tm)>);
    

until ell gt 50;

