% operadores proposicionales
:- op(700,xfy,v).
:- op(600,xfy,^).
:- op(500,fy,~).

%semantica de los operadores
v(X,Y) :- X;Y.
^(X,Y) :- X,Y.
~(X) :- \+ X.
=>(X,Y). 

% llama recursivamente a implfree para cada argumento del and
impl_free(X^Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=((Izq) ^ (Der)).

% cambia la implicación X => Y por ~X v Y
impl_free(X=>Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=(~(Izq) v (Der)),!.

impl_free(X,X).
       %IMPLFREE=X.