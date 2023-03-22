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
impl_free(X^Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=((Izq) ^ (Der)).

% cambia la implicación X => Y por ~X v Y
impl_free(X=>Y,IMPLFREE):-
    impl_free(X,Izq),
    impl_free(Y,Der),
    IMPLFREE=(~(Izq) | (Der)).




% caso base si es una literal regresa la literal
nnf(X,X):-
    atom(X).

% caso base si es una literal regresa la literal
nnf(~X,~X):-
    atom(X).

% elimina doble negación
nnf(~(~X),X).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con ^
nnf(X^Y,NNF):-
    nnf(X,Izq),
    nnf(Y,Der),
    NNF=((Izq)^(Der)).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con v
nnf(X|Y,NNF):-
    nnf(X,Izq),
    nnf(Y,Der),
    NNF=((Izq) | (Der)).

% llama a nnf para el lado izquierdo negado y derecho negado y el resultado lo une con ^
nnf(~(X^Y),NNF):-
    nnf(~X,Izq),
    nnf(~Y,Der),
    NNF=((Izq)|(Der)).

% llama a nnf para el lado izquierdo y derecho y el resultado lo une con v
nnf(~(X|Y),NNF):-
    nnf(~X,Izq),
    nnf(~Y,Der),
    NNF=((Izq) ^ (Der)).

