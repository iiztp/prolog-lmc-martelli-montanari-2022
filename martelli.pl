#/usr/bin/env swipl

:- op(20,xfy,?=).

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).
% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): affiche T
echo(T) :- echo_on, !, write(T).
echo(_).

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
reduit(rename, X ?= T, P, Q) :- regle(X ?= T, rename), echo_rule(rename, X ?= T), X = T, select(X?=T, P, Q).

% Application de la règle du renommage pour une constante (simplification)
% Vrai si on peut appliquer la règle de simplification, alors X prend la valeur de T et Q de P.
reduit(simplify, X ?= T, P, Q) :- regle(X ?= T, simplify), echo_rule(simplify, X ?= T), X = T, select(X ?= T, P, Q).

% Application de la règle d'expansion
% Vrai si on peut appliquer la règle d'expansion, alors X prend la valeur de T et Q de P.
reduit(expand, X ?= T, P, Q) :- regle(X ?= T, expand), echo_rule(expand, X ?= T), X = T, select(X ?= T, P, Q).

% Application de la règle d'occur-check
% Vrai si on peut appliquer la règle d'occur-check, alors fail.
reduit(check, X ?= T, _, _) :- regle(X ?= T, check), echo_rule(check, X ?= T), fail.

% Application de la règle d'orientation
% Vrai si on peut appliquer la règle d'orientation, alors X prend la valeur de T.
reduit(orient, T ?= X, P, Q) :- regle(T ?= X, orient), echo_rule(orient, T ?= X), select(T ?= X, P, RES), append(RES, [X ?= T], Q).

% Application de la règle de décomposition
% Vrai si on peut appliquer la règle de décomposition, alors on applique les arguments de F1 à F2.
reduit(decompose, F1 ?= F2, P, Q) :- 
    regle(F1 ?= F2, decompose), echo_rule(decompose, F1 ?= F2),
    F1 =.. [_|LIST1], F2 =.. [_|LIST2],
    decomposition(LIST1, LIST2, RES),
    select(F1?=F2, P, NEXT),
    append(RES, NEXT, Q).

% Application de la règle de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité, alors fail.
reduit(clash, F ?= G, _, _) :- regle(F ?= G, clash), echo_rule(clash, F ?= G), fail.

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

%--------------------------------------------------------
% Faits listant les règles (ordonnées)
%--------------------------------------------------------
rule_list([[clash], [check], [rename], [simplify], [orient], [decompose], [expand]]).
ponde_1([[clash, check], [rename, simplify], [orient], [decompose], [expand]]).
ponde_2([[decompose], [expand, check], [orient], [clash, simplify], [rename]]).

%--------------------------------------------------------
% Prédicats d'unification par stratégie
%--------------------------------------------------------
unifie([], _).
unifie(P, choix_premier) :- echo_tab(P), choix_premier(P, Q), unifie(Q, choix_premier).
unifie(P, choix_pondere_1) :- echo_tab(P), choix_pondere_1(P, Q), unifie(Q, choix_pondere_1).
unifie(P, choix_pondere_2) :- echo_tab(P), choix_pondere_2(P, Q), unifie(Q, choix_pondere_2).
unifie(P, choix_formule_aleatoire) :- echo_tab(P), choix_formule_aleatoire(P, Q), unifie(Q, choix_formule_aleatoire).
unifie(P, choix_regle_aleatoire) :- echo_tab(P), choix_regle_aleatoire(P, Q), unifie(Q, choix_regle_aleatoire).

%--------------------------------------------------------
% Prédicats choisissant les formules / règles
%--------------------------------------------------------
choix_premier(P, Q) :- [X|_] = P, reduit(_, X, P, Q).

choix_pondere_1(P, Q) :- ponde_1(RULES), apply_rules(P, Q, RULES), write("P: "), writeln(P), write("Q: "), writeln(Q), choix_pondere_1(Q, _).
% choix_pondere_2([X|NEXT], Q) :- ponde_2(RULES), apply_rules(NEXT, Q, X, RULES).

choix_formule_aleatoire(P, Q) :- random_permutation(P, NP), choix_premier(NP, Q).
choix_regle_aleatoire(P, Q) :- rule_list(REGLES), random_permutation(REGLES, NREGLES), apply_rules(P, Q, NREGLES).

% Prédicat appliquant les règles dans l'ordre de la liste à l'équation E   '
apply_rules(P, Q, [RULES|NEXT_RULES]) :-
    try_rules(P, Q, RULES);
    apply_rules(P, Q, NEXT_RULES).

try_rules(P, Q, [RULE|NEXT]) :-
    reduit_all(RULE, P, P, Q), !
    ;
    try_rules(P, Q, NEXT).

reduit_all(RULE, [E|NEXT], P, Q) :-
    reduit(RULE, E, P, Q), !
    ;
    reduit_all(RULE, P, NEXT, Q).

% Prédicat de test pour vérifier le runtime de chaque stratégie
statistics_on(P, S) :- statistics(runtime,[START|_]),
                    unifie(P, S),
                    statistics(runtime,[STOP|_]),
                    RUNTIME is STOP - START,
                    write("Resultat pour "), write(S), write(", runtime : "), write(RUNTIME), writeln("ms").

%------------------------------------------------------------------------------
%//////////////////////////////////////////////////////////////////////////////
%////                           Question 3                                 ////
%//////////////////////////////////////////////////////////////////////////////
%------------------------------------------------------------------------------

unif(P, S) :- clr_echo, unifie(P, S).
trace_unif(P, S) :- set_echo, unifie(P, S).

echo_tab(P) :- echo('system: '), echo(P), echo('\n').
echo_rule(R, X) :- echo(R), echo(': '), echo(X), echo('\n').
