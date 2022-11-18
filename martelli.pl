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

rule_test(X) :- (X -> echo('true') ; echo('false')).
rule_test(X, R) :- echo('Test \''), echo(X), echo('\' : '), rule_test(regle(X, R)), echo('\n').
rule_tests(R) :-
    rule_test(X ?= Y, R),
    rule_test(X ?= a, R),
    rule_test(X ?= foo(a, Y), R),
    rule_test(X ?= foo(a, X), R),
    rule_test(foo(a, Y) ?= X, R),
    rule_test(foo(a, X) ?= X, R),
    rule_test(foo(X, Y) ?= foo(a, Y), R),
    rule_test(foo(X, Y, Z) ?= foo(a, X), R),
    rule_test(foo(a, Y) ?= bar(X, Y), R).

reduct_test(reduit(R, X, [X], Q)) :- (reduit(R, X, [X], Q) -> echo([X]) ; echo('Unapplicable')).
reduct_test(R, X) :- echo('Test \''), echo(X), echo('\' : '), reduct_test(reduit(R, X, [X], Q)), echo('\n').
reduct_tests(R) :- 
    reduct_test(R, X ?= Y),
    reduct_test(R, X ?= a),
    reduct_test(R, X ?= foo(a, Y)),
    reduct_test(R, X ?= foo(a, X)),
    reduct_test(R, foo(a, Y) ?= X),
    reduct_test(R, foo(a, X) ?= X),
    reduct_test(R, foo(X, Y) ?= foo(a, Y)),
    reduct_test(R, foo(X, Y, Z) ?= foo(a, X)),
    reduct_test(R, foo(a, Y) ?= bar(X, Y)).

full_rule_tests() :-
    echo('\n------Test de la règle rename------\n\n'), rule_tests(rename),
    echo('\n-----Test de la règle simplify-----\n\n'), rule_tests(simplify),
    echo('\n------Test de la règle expand------\n\n'), rule_tests(expand),
    echo('\n------Test de la règle check------\n\n'), rule_tests(check),
    echo('\n------Test de la règle orient------\n\n'), rule_tests(orient),
    echo('\n-----Test de la règle decompose-----\n\n'), rule_tests(decompose),
    echo('\n-------Test de la règle clash-------\n\n'), rule_tests(clash).

full_reduct_tests() :-
    echo('\n------Test de la réduction rename------\n\n'), reduct_tests(rename),
    echo('\n-----Test de la réduction simplify-----\n\n'), reduct_tests(simplify),
    echo('\n------Test de la réduction expand------\n\n'), reduct_tests(expand),
    echo('\n------Test de la réduction check------\n\n'), reduct_tests(check),
    echo('\n------Test de la réduction orient------\n\n'), reduct_tests(orient),
    echo('\n-----Test de la réduction decompose-----\n\n'), reduct_tests(decompose),
    echo('\n-------Test de la réduction clash-------\n\n'), reduct_tests(clash).

% Fonction main
main(Argv) :-
    echo('Début des tests :\n'),
    echo('//////////////Test des règles//////////////////\n'), full_rule_tests(),
    nl,
    echo('////////////Test des réductions////////////////\n'), full_reduct_tests(),
    nl.
    

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
regle(F ?= G, clash) :- not(var(F)), not(var(G)), functor(F, _, N), functor(G, _, M), not(N==M);
    not(var(F)), not(var(G)), functor(F, FNAME, N), functor(G, GNAME, M), not(FNAME==GNAME).

% Prédicat d'occur-check
% Vrai si V apparaît dans T.
occur_check(V, T) :- contains_var(V, T).

%--------------------------------------------------------
% Prédicats de réduction pour appliquer les règles
%--------------------------------------------------------

% Application de la règle du renommage
% Vrai si on peut appliquer la règle du renommage, alors X prend la valeur de T et Q de P.
reduit(rename, X ?= T, [X?=T|NEXT], Q) :- regle(X ?= T, rename), X = T, Q = NEXT.

% Application de la règle du renommage pour une constante (simplification)
% Vrai si on peut appliquer la règle de simplification, alors X prend la valeur de T et Q de P.
reduit(simplify, X ?= T, [X?=T|NEXT], Q) :- regle(X ?= T, simplify), X = T, Q = NEXT.

% Application de la règle d'expansion
% Vrai si on peut appliquer la règle d'expansion, alors X prend la valeur de T et Q de P.
reduit(expand, X ?= T, [X?=T|NEXT], Q) :- regle(X ?= T, expand), X = T, Q = NEXT.

% Application de la règle d'occur-check
% Vrai si on peut appliquer la règle d'occur-check, alors fail.
reduit(check, X ?= T, P, Q) :- regle(X ?= T, check), fail.

% Application de la règle d'orientation
% Vrai si on peut appliquer la règle d'orientation, alors X prend la valeur de T.
reduit(orient, T ?= X, [T?=X|NEXT], Q) :- regle(T ?= X, orient), X = T, Q = NEXT.

% Application de la règle de décomposition
% Vrai si on peut appliquer la règle de décomposition, alors on applique les arguments de F1 à F2.
reduit(decompose, F1 ?= F2, [F1?=F2|NEXT], Q) :- regle(F1 ?= F2, decompose), F1 =.. [NAME1|LIST1], F2 =.. [NAME2|LIST2], decomposition(LIST1, LIST2, RES), Q = [RES|NEXT].

% Application de la règle de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité, alors fail.
reduit(clash, F ?= G, P, Q) :- regle(F ?= G, clash), fail.

% Décomposition de deux listes pour appliquer l'opérateur sur ses membres
decomposition([A|NEXT1], [B|NEXT2], RES) :- decomposition(NEXT1, NEXT2, [RES|A ?= B]).
decomposition([], [], RES).

%--------------------------------------------------------
% Prédicats pour lancer l'unification
%--------------------------------------------------------

unifie([U]) :- reduit(_,A,U,Q), unifie(Q). 
unifie([]).