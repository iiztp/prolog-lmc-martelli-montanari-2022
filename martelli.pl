#!/usr/bin/env swipl

:- op(20,xfy,?=).

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).
% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): affiche T
echo(T) :- echo_on, !, write(T).
echo(_).

:- set_echo, initialization(main, main).

% Fonction main
main(Argv) :-
    echo(Argv).

%------------------------------------------------------------------------------
%//////////////////////////////////////////////////////////////////////////////
%////                           Question 1                                 ////
%//////////////////////////////////////////////////////////////////////////////
%------------------------------------------------------------------------------

%--------------------------------------------------------
% Prédicats pour savoir si on peut appliquer les règles.
%--------------------------------------------------------

% Prédicat de renommage d'une variable
% Vrai si X et T sont des variables.
regle(X ?= T, rename) :- var(X), var(T).

% Prédicat de renommage pour une constante (simplification)
% Vrai si X est une variable et T est une constante.
regle(X ?= T, simplify) :- var(X), not(var(T)), functor(T, _, 0).

% Prédicat d'expansion
% Vrai si X est une variable, T est composé et X n'apparaît pas dans T.
regle(X ?= T, expand) :- var(X), compound(T), not(occur_check(X, T)).

% Prédicat d'occur-check
% Vrai si X est une variable et que X apparaît dans T.
regle(X ?= T, check) :- var(X), occur_check(X, T), X \== T.

% Prédicat d'orientation
% Vrai si T n'est pas une variable et que X est une variable.
regle(T ?= X, orient) :- not(var(T)), var(X).

% Prédicat de décomposition
% Vrai si F1 et F2 sont deux fonctions avec la même arité N.
regle(F1 ?= F2, decompose) :- not(var(F1)), not(var(F2)), functor(F1, F, N), functor(F2, F, N).

% Prédicat de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité ou deux fonctions qui n'ont pas le même nom.
regle(F ?= G, clash) :- not(var(F)), not(var(G)), functor(F, _, N), functor(G, _, M), not(N==M).
 regle(F ?= G, clash) :- not(var(F)), not(var(G)), functor(F, FNAME, _), functor(G, GNAME, _), not(FNAME==GNAME).

% Prédicat d'occur-check
% Vrai si V apparaît dans T.
occur_check(V, T) :- contains_var(V, T).

%--------------------------------------------------------
% Prédicats de réduction pour appliquer les règles
%--------------------------------------------------------

% Application de la règle du renommage
% Vrai si on peut appliquer la règle du renommage, alors X prend la valeur de T et Q de P.
reduit(rename, X ?= T, NEXT, Q) :- regle(X ?= T, rename), X = T, Q = NEXT.

% Application de la règle du renommage pour une constante (simplification)
% Vrai si on peut appliquer la règle de simplification, alors X prend la valeur de T et Q de P.
reduit(simplify, X ?= T, NEXT, Q) :- regle(X ?= T, simplify), X = T, Q = NEXT.

% Application de la règle d'expansion
% Vrai si on peut appliquer la règle d'expansion, alors X prend la valeur de T et Q de P.
reduit(expand, X ?= T, NEXT, Q) :- regle(X ?= T, expand), X = T, Q = NEXT.

% Application de la règle d'occur-check
% Vrai si on peut appliquer la règle d'occur-check, alors fail.
reduit(check, X ?= T, _, _) :- regle(X ?= T, check), fail.

% Application de la règle d'orientation
% Vrai si on peut appliquer la règle d'orientation, alors X prend la valeur de T.
reduit(orient, T ?= X, NEXT, Q) :- regle(T ?= X, orient), Q = [X ?= T|NEXT].

% Application de la règle de décomposition
% Vrai si on peut appliquer la règle de décomposition, alors on applique les arguments de F1 à F2.
reduit(decompose, F1 ?= F2, NEXT, Q) :- regle(F1 ?= F2, decompose), F1 =.. [_|LIST1], F2 =.. [_|LIST2], decomposition(LIST1, LIST2, RES), append(RES, NEXT, X), Q = X.

% Application de la règle de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité, alors fail.
reduit(clash, F ?= G, _, _) :- regle(F ?= G, clash), fail.

% Décomposition de deux listes pour appliquer l'opérateur sur ses membres
decomposition([A|NEXT1], [B|NEXT2], [A ?= B|RES]) :- decomposition(NEXT1, NEXT2, RES).
decomposition([], [], []).

%--------------------------------------------------------
% Prédicats pour unifier
%--------------------------------------------------------
unifie(P) :- unifie(P, choix_premier).


%------------------------------------------------------------------------------
%//////////////////////////////////////////////////////////////////////////////
%////                           Question 2                                 ////
%//////////////////////////////////////////////////////////////////////////////
%------------------------------------------------------------------------------

unifie([], _).
unifie(P, choix_premier) :- choix_premier(P, Q, _, _), !, unifie(Q, choix_premier).

choix_premier([X|NEXT], Q, X, R) :- reduit(R, X, NEXT, Q).