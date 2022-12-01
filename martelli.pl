#!/usr/bin/env swipl

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
regle(X ?= T, simplify) :- var(X), \+(var(T)), functor(T, _, 0).

% Prédicat d'expansion
% Vrai si X est une variable, T est composé et X n'apparaît pas dans T.
regle(X ?= T, expand) :- var(X), compound(T), \+(occur_check(X, T)).

% Prédicat d'occur-check
% Vrai si X est une variable et que X apparaît dans T.
regle(X ?= T, check) :- var(X), occur_check(X, T), \+(X==T).

% Prédicat d'orientation
% Vrai si T n'est pas une variable et que X est une variable.
regle(T ?= X, orient) :- \+(var(T)), var(X).

% Prédicat de décomposition
% Vrai si F1 et F2 sont deux fonctions avec la même arité N.
regle(F1 ?= F2, decompose) :- \+(var(F1)), \+(var(F2)), functor(F1, F, N), functor(F2, F, N).

% Prédicat de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité ou deux fonctions qui n'ont pas le même nom.
regle(F ?= G, clash) :- \+(var(F)), \+(var(G)), functor(F, _, N), functor(G, _, M), \+(N==M).
regle(F ?= G, clash) :- \+(var(F)), \+(var(G)), functor(F, FNAME, _), functor(G, GNAME, _), \+(FNAME==GNAME).

% Prédicat d'occur-check
% Vrai si V apparaît dans T.
occur_check(V, T) :- contains_var(V, T).

%--------------------------------------------------------
% Prédicats de réduction pour appliquer les règles
%--------------------------------------------------------

% Application de la règle du renommage
% Vrai si on peut appliquer la règle du renommage, alors X prend la valeur de T et Q de P.
reduit(rename, X ?= T, P, Q) :- X = T, ord_subtract(P, [X?=T], Q).

% Application de la règle du renommage pour une constante (simplification)
% Vrai si on peut appliquer la règle de simplification, alors X prend la valeur de T et Q de P.
reduit(simplify, X ?= T, P, Q) :- X = T, ord_subtract(P, [X ?= T], Q).

% Application de la règle d'expansion
% Vrai si on peut appliquer la règle d'expansion, alors X prend la valeur de T et Q de P.
reduit(expand, X ?= T, P, Q) :- X = T, ord_subtract(P, [X ?= T], Q).

% Application de la règle d'occur-check
% Vrai si on peut appliquer la règle d'occur-check, alors fail.
reduit(check, _, _, _) :- false.

% Application de la règle d'orientation
% Vrai si on peut appliquer la règle d'orientation, alors X prend la valeur de T.
reduit(orient, T ?= X, P, Q) :- ord_subtract(P, [T ?= X], RES), append(RES, [X ?= T], Q).

% Application de la règle de décomposition
% Vrai si on peut appliquer la règle de décomposition, alors on applique les arguments de F1 à F2.
reduit(decompose, F1 ?= F2, P, Q) :- 
        F1 =.. [_|LIST1], F2 =.. [_|LIST2],
        ord_subtract(P, [F1?=F2], NEXT),
        decomposition(LIST1, LIST2, RES),
        append(RES, NEXT, Q).

% Application de la règle de conflit
% Vrai si F et G sont deux fonctions qui n'ont pas la même arité, alors fail.
reduit(clash, _, _, _) :- false.

% Décomposition de deux listes pour appliquer l'opérateur sur ses membres
decomposition([A|NEXT1], [B|NEXT2], RES) :- decomposition(NEXT1, NEXT2, T), append([A ?= B], T, RES).
decomposition([], [], []).

%--------------------------------------------------------
% Prédicats pour unifier
%--------------------------------------------------------
unifie(P) :- clr_echo, unifie(P, choix_premier).

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
unifie(P, S) :- echo_tab(P), call(S, P, Q, E, R), echo_rule(R, E), (reduit(R, E, P, Q) -> unifie(Q, S); false).

%--------------------------------------------------------
% Prédicats choisissant les formules / règles
%--------------------------------------------------------
choix_premier([E|_], _, E, R) :- regle(E, R).
choix_pondere_1(P, _, E, R) :- ponde_1(RULES), select_eq(P, RULES, E, R).
choix_pondere_2(P, _, E, R) :- ponde_2(RULES), select_eq(P, RULES, E, R).
choix_formule_aleatoire(P, _, E, R) :- random_permutation(P, RP), choix_premier(RP, _, E, R).
choix_regle_aleatoire(P, _, E, R) :- rule_list(REGLES), random_permutation(REGLES, RREGLES), select_eq(P, RREGLES, E, R).

%--------------------------------------------------------
% Prédicats auxiliaires
%--------------------------------------------------------

% Prédicats permettant de choisir l'équation E en fonction de l'ordre d'une liste de règles ordonnées
select_eq(P, [RULES|NEXT], E, R) :- select_eq_aux(P, RULES, E, R); select_eq(P, NEXT, E, R).
select_eq_aux(P, [RULE|NEXT], E, R) :- select_eq_aux2(P, RULE, E, R); select_eq_aux(P, NEXT, E, R).
select_eq_aux2([EQ|NEXT], RULE, E, R) :- regle(EQ, RULE) -> E = EQ, R = RULE; select_eq_aux2(NEXT, RULE, E, R).

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

%--------------------------------------------------------
% Prédicats d'unification par affichage (ou non)
%--------------------------------------------------------

% Prédicat d'unification : inhibe l'affichage puis unifie P avec la stratégie S
unif(P, S) :- clr_echo, unifie(P, S).
% Prédicat d'unification : déclare l'affichage puis unifie P avec la stratégie S
trace_unif(P, S) :- set_echo, unifie(P, S).

%--------------------------------------------------------
% Prédicats de mise en page d'affichage
%--------------------------------------------------------

% Affiche le tableau entier
echo_tab(P) :- echo('system: '), echo(P), echo('\n').
% Affiche la règle appliquée sur quelle formule
echo_rule(R, X) :- echo(R), echo(': '), echo(X), echo('\n').
