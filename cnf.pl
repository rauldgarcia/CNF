% operadores proposicionales
:- op(700,xfy,v).
:- op(600,xfy,^).
:- op(500,fy,~).

%semantica de los operadores
v(X,Y) :- X;Y.
^(X,Y) :- X,Y.
~(X) :- \+ X.
 

% caso base si es una literal regresa la literal
impl_free(X,X):-
    atom(X).

% caso base si es una literal negada regresa la literal negada
impl_free(~X,~X):-
    atom(X).

% llama recursivamente a implfree para cada argumento del and
impl_free(X ^ Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=((Izq) ^ (Der)).

% llama recursivamente a implfree para cada argumento del and
impl_free(X v Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=((Izq) v (Der)).

% cambia la implicación X => Y por ~X v Y
impl_free(X => Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=(~(Izq) v (Der)).


% NNF ---------------------------------------------------------------------------------
% caso base si es una literal regresa la literal
nnf(X,X):-
    atom(X).

% caso base si es una literal regresa la literal
nnf(~X,~X):-
    atom(X).

% elimina doble negación
nnf(~(~X),X).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con ^
nnf(X ^ Y,NNF):-
    nnf(X,Izq),
    nnf(Y,Der),
    NNF=((Izq)^(Der)).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con v
nnf(X v Y,NNF):-
    nnf(X,Izq),
    nnf(Y,Der),
    NNF=((Izq) v (Der)).

% llama a nnf para el lado izquierdo negado y derecho negado y el resultado lo une con ^
nnf(~(X ^ Y),NNF):-
    nnf(~X,Izq),
    nnf(~Y,Der),
    NNF=((Izq) v (Der)).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con v
nnf(~(X v Y),NNF):-
    nnf(~X,Izq),
    nnf(~Y,Der),
    NNF=((Izq) ^ (Der)).

% CNF ---------------------------------------------------------------------------------------------

% si es literal regresa literal
cnf(X,X):-
    atom(X).

% si es literal negada regresa literal negada
cnf(~X,~X):-
    atom(X).

% si es and llama recursivamente a cnf para cada lado y regresa el and de ambos
cnf(X ^ Y,CNF):-
    cnf(X,Izq),
    cnf(Y,Der),
    CNF=((Izq) ^ (Der)).

% si es or llama recursivamente a cnf para cada lado y llama a distr con ambos
cnf(X v Y,CNF):-
    cnf(X,Izq),
    cnf(Y,Der),
    distr(Izq,Der,CNF),!.

% llama a impl_free para quitar las implicaciones
% llama a nnf con lo que regrese implfree
% para llevar las negaciones a las literales
cnf(X,CNF):-
    impl_free(X,IMPLFREE),
    nnf(IMPLFREE,NNF),
    cnf(NNF,CNF),!.

% DISTR ---------------------------------------------------------

% si X es and llama recursivamente con X1 y Y y con X2 y Y
% y regresa el and de lo que regrese la llamada recursiva
distr(X,Y,DISTR):-
    X= X1 ^ X2,
    distr(X1,Y,Izq),
    distr(X2,Y,Der),
    DISTR=(Izq ^ Der).

% si Y es and recursivamente con X y Y1 y con X y Y2
% y regresa el and de lo que regrese la llamada recursiva
distr(X,Y,DISTR):-
    Y= Y1 ^ Y2,
    distr(X,Y1,Izq),
    distr(X,Y2,Der),
    DISTR=(Izq ^ Der).

% si no hay and regresa el or de ambos
distr(X,Y,DISTR):-
    DISTR=(X v Y).