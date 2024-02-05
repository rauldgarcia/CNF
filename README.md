Representación del conocimiento

Tarea 2

Raúl Daniel García Ramón rauld.garcia95@gmail.com

28 de marzo de 2023

**Índice**

1. [**COVID](#_page1_x125.80_y129.78) **2**
1. [**Implementación CNF](#_page2_x125.80_y238.08) **3**
1. [**Caso sospechoso CNF](#_page7_x125.80_y129.78) **8**
1. [**CNF y SAT](#_page7_x125.80_y426.25) **8**

<a name="_page1_x125.80_y129.78"></a>**1. COVID**

A partir del lineamiento estandarizado para la vigilancia epidemiológica y por laboratorio de COVID-19 de la Secretaría de Salud (disponible en el repositorio Teams), defina en lógica proposicional los conceptos de caso sospechoso y caso confirmado de COVID-19 (pág. 12). Defina otro concepto del documento. [30/100]

Caso sospechoso:

Persona de cualquier edad que presente enfermedad respiratoria aguda leve o grave y que cuente con alguno de los siguientes antecedentes hasta 14 días del inicio de síntomas:

- Haber estado en contacto con un caso confirmado o bajo investigación a COVID-19, o
  - Viaje o estancia a países con transmisión local comunitaria\* de COVID-

    19\. (\*China, Hong Kong, Corea del Sur, Japón, Italia, Irán y Singapur)

Al definirlo en lógica proposicional queda de la siguiente manera:

*PersonaXEdad*∧*EnfermedadRespiratoria*∧((*ContactoCasoConfirmado*∨ *ContactoCasoBajoInvestigacion*) ∨ *V iaje*) =⇒ *CasoSospechoso*

Caso confirmado:

Persona que cumpla con la definición operacional de caso sospechoso y que cuente con diagnóstico confirmado por laboratorio emitido por el In- DRE.

Al definirlo en lógica proposicional quedaría de la siguiente manera: *CasoSospechoso* ∧ *DiagnosticoConfirmado* =⇒ *CasoConfirmado*

El médico de primer contacto después de identificar a un paciente con sospecha de COVID-19, deberá realizar el interrogatorio y atención del caso bajo medidas de precaución estándar y por gotas en un cubículo aislado,

bien ventilado y mantener la puerta cerrada.

Al definirlo en lógica proposicional queda de la siguiente forma:

*IdentificarPacienteConSospecha* =⇒ *RealizarInterrogatorio*∧*AtencionBajoEstandar*∧ *PorGotasEnCubiculoAislado* ∧ *BienV entilado* ∧ *PuertaCerrada*

2. **Implementación<a name="_page2_x125.80_y238.08"></a> CNF**

Implemente en Prolog el algoritmo CNF visto en clase, para convertir una fbf proposicional en su equivalente en forma normal conjuntiva. Pruebe su implementación con el ejemplo visto en clase. [30/100]

El código implementado es el siguiente:

1  *% operadores proposicionales*
1  :- op(700,xfy,v).
1  :- op(600,xfy,^).
1  :- op(500,fy,~).

5

6  *% caso base si es una literal regresa la literal*
6  impl\_free(X,X):-

8 atom(X).

9

10  *% caso base si es una literal negada regresa la literal negada*
10  impl\_free(~X,~X):-

12 atom(X).

13

14  *% llama recursivamente a implfree para cada argumento del and*
14  impl\_free(X ^ Y,IMPLFREE):-

16 impl\_free(X,Izq),

17 impl\_free(Y,Der),

18 IMPLFREE=((Izq) ^ (Der)).

19

20  *% llama recursivamente a implfree para cada argumento del and*
20  impl\_free(X v Y,IMPLFREE):-

22 impl\_free(X,Izq),

23 impl\_free(Y,Der),

24 IMPLFREE=((Izq) v (Der)).

25

26  *% cambia la implicación X => Y por ~X v Y*
26  impl\_free(X => Y,IMPLFREE):-

28 impl\_free(X,Izq),

29 impl\_free(Y,Der),

30 IMPLFREE=(~(Izq) v (Der)).

31

32

33  *% NNF ---------------------------------------------------*
33  *% caso base si es una literal regresa la literal*
33  nnf(X,X):-

36 atom(X).

37

38  *% caso base si es una literal regresa la literal*
38  nnf(~X,~X):-

40 atom(X).

41

42  *% elimina doble negación*
42  nnf(~(~X),X).

44

45  *% llama a nnf para el lado izquierdo y derecho*
45  *% y el resultado lo une con ^*
45  nnf(X ^ Y,NNF):-

48 nnf(X,Izq),

49 nnf(Y,Der),

50 NNF=((Izq)^(Der)).

51

52  *% llama a nnf para el lado izquierdo y derecho y*
52  *% el resultado lo une con v*
52  nnf(X v Y,NNF):-

55 nnf(X,Izq),

56 nnf(Y,Der),

57 NNF=((Izq) v (Der)).

58

59  *% llama a nnf para el lado izquierdo negado*
59  *% y derecho negado y el resultado lo une con ^*
59  nnf(~(X ^ Y),NNF):-

62 nnf(~X,Izq),

63 nnf(~Y,Der),

64 NNF=((Izq) v (Der)).

65

66  *% llama a nnf para el lado izquierdo y derecho*
66  *% y el resultado lo une con v*
66  nnf(~(X v Y),NNF):-

69 nnf(~X,Izq),

70 nnf(~Y,Der),

71 NNF=((Izq) ^ (Der)).

72

73  *% CNF --------------------------------------------------*
73  *% si es literal regresa literal*
73  cnf(X,X):-

76 atom(X).

77

78  *% si es literal negada regresa literal negada*
78  cnf(~X,~X):-

80 atom(X).

81

82  *% si es and llama recursivamente a cnf para cada lado*
82  *% y regresa el and de ambos*
82  cnf(X ^ Y,CNF):-

85 cnf(X,Izq),

86 cnf(Y,Der),

87 CNF=((Izq) ^ (Der)).

88

89  *% si es or llama recursivamente a cnf para cada lado*
89  *% y llama a distr con ambos*
89  cnf(X v Y,CNF):-

92 cnf(X,Izq),

93 cnf(Y,Der),

94 distr(Izq,Der,CNF),!.

95

96  *% llama a impl\_free para quitar las implicaciones*
96  *% llama a nnf con lo que regrese implfree*
96  *% para llevar las negaciones a las literales*
96  cnf(X,CNF):-

100 impl\_free(X,IMPLFREE),

101 nnf(IMPLFREE,NNF),

102 cnf(NNF,CNF),!.

103

104 *% DISTR -----------------------------------------------------* 105

106  *% si X es and llama recursivamente con X1 y Y y con X2 y Y*
106  *% y regresa el and de lo que regrese la llamada recursiva*
106  distr(X,Y,DISTR):-

109 X= X1 ^ X2,

110 distr(X1,Y,Izq),

111 distr(X2,Y,Der),

112 DISTR=(Izq ^ Der).

113

114  *% si Y es and recursivamente con X y Y1 y con X y Y2*
114  *% y regresa el and de lo que regrese la llamada recursiva*
114  distr(X,Y,DISTR):-

117 Y= Y1 ^ Y2,

118 distr(X,Y1,Izq),

119 distr(X,Y2,Der),

120 DISTR=(Izq ^ Der).

121

122  *% si no hay and regresa el or de ambos*
122  distr(X,Y,DISTR):-

124 DISTR=(X v Y).

La función impl-free en el ejemplo visto en clase obtiene lo siguiente:

1  ?- impl\_free(~p ^ q => p ^ (r => q), IMPLFREE).
1  IMPLFREE = (~ (~p^q)v p^(~r v q))

Mientras que al probar el código desarrollado se obtiene lo siguiente:

1  ?- impl\_free(~p ^ q => p ^ (r => q), IMPLFREE).
1  IMPLFREE = (~ (~p^q)v p^(~r v q)).

   Como se puede ver se obtiene el mismo resultado que en el ejemplo visto en clase. Ahora, al probar este resultado con el NNF en el ejemplo visto en clase, se obtiene lo siguiente:

1  ?- impl\_free(~p ^ q => p ^ (r => q), IMPLFREE), nnf(IMPLFREE,NNF).
1  IMPLFREE = (~ (~p^q)v p^(~r v q)),
1  NNF = ((p v ~q)v p^(~r v q))

Al probar el código implementado se obtiene lo siguiente:

1  ?- impl\_free(~p ^ q => p ^ (r => q), IMPLFREE), nnf(IMPLFREE,NNF).
1  IMPLFREE = (~ (~p^q)v p^(~r v q)),
1  NNF = ((p v ~q)v p^(~r v q))

   Como se puede observar se obtiene el mismo resultado que en el ejemplo visto en clase. A continuación, al probar el CNF con el ejemplo visto en clase se obtiene lo siguiente:

1  ?- cnf(~p ^ q => p ^ (r => q), CNF).
1  CNF = ((p v ~q)v p)^((p v ~q)v~r v q)

Probándolo en la implementación del código se obtiene:

1  ?- cnf(~p ^ q => p ^ (r => q), CNF).
1  CNF = ((p v ~q)v p)^((p v ~q)v~r v q).

   Se puede ver que el resultado es el mismo que el ejemplo visto en clase. Finalmente, al probar el último ejemplo visto en clase se debe obtener lo siguiente:

1  ?- cnf(r => (s => (t ^ s => r)), CNF).
1  CNF = (~r v ~s v (~t v ~s)v r)

Al probarlo en el código implementado se obtiene lo siguiente:

1  ?- cnf(r => (s => (t ^ s => r)), CNF).
1  CNF = (~r v ~s v (~t v ~s)v r).

   Como se puede observar se obtiene el mismo resultado que en el ejemplo visto en clase, por lo que todos los ejemplos vistos en clase se implementaron de manera correcta.

3. **Caso<a name="_page7_x125.80_y129.78"></a> sospechoso CNF**

Convierta la definición de caso sospechoso a forma normal conjuntiva, usando su programa CNF. [20/100]

Caso sospechoso:

*PersonaXEdad*∧*EnfermedadRespiratoria*∧((*ContactoCasoConfirmado*∨ *ContactoCasoBajoInvestigacion*) ∨ *V iaje*) =⇒ *CasoSospechoso*

Al convertirlo a forma normal conjuntiva con el programa queda de la siguiente manera:

1  cnf(((personaxedad ^ enfermedadrespiratoria) ^
1  ((contactocasoconfirmado v contactocasobajoinvestigacion) v viaje)) =>
1  casosospechoso, CNF).
1  CNF = ((((~personaxedad v ~enfermedadrespiratoria)v~contactocasoconfirmado)v
1  casosospechoso)^(((~personaxedad v ~enfermedadrespiratoria)v
1  ~contactocasobajoinvestigacion)v casosospechoso))^
1  (((~personaxedad v ~enfermedadrespiratoria)v~viaje)v casosospechoso).
4. **CNF<a name="_page7_x125.80_y426.25"></a> y SAT**

Utilice los algoritmos CNF y SAT (disponible en el repositorio de Teams) para verificar que *p* =⇒ *q* es equivalente a ¬*p* ∨ *q* (Ejercicio 3 de la tarea

anterior). [20/100]

8

Al correr el algoritmo CNF con

1  ?- cnf(p => q,CNF).
1  CNF = (~p v q).

   Al correr en el algoritmo SAT el siguiente:

*p* =⇒ *q* se obtiene lo siguiente:

¬*p* ∨ *q* obtenido con CNF se obtiene lo



1  ?- Clauses = [[false-P,true-Q]],sat(Clauses,[P,Q]).
1  Clauses = [[false-true, true-true]],
1  P = Q, Q = true ;
4  Clauses = [[false-false, true-true]],
4  P = false,
4  Q = true ;
4  Clauses = [[false-false, true-false]],
4  P = Q, Q = false.

   De acuerdo a lo observado se puede notar que si es satisfacible, por lo que si son equivalentes.

**Referencias**

Bratko, I. (2012). *Prolog programming for Artificial Intelligence*. Pearson,

fourth edition.

Clocksin, W. F. and Melish, C. S. (2003). *Programming in Prolog, using the*

*ISO standard*. Springer-Verlag, Berlin-Heidelberg, Germany.

Labra, J. (1998). *Programación Práctica en Prolog*. Universidad de Oviedo. Nilsson, U. and Maluszynski, J. (2000). *Logic, Programming and Prolog*.

John Wiley & Sons Ltd, 2nd edition.

Norvig, P. (1992). *Paradigms of Artificial Intelligence Programming: Case*

*Studies in Common Lisp*. Morgan Kauffman Publishers.
9
