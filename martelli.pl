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

regle(X ?= T, rename) :- var(X), var(T).
regle(X ?= T, simplify) :- var(X), functor(T, _, 0).
regle(X ?= T, expand) :- var(X), compound(T), not(occur_check(X, T)).
regle(X ?= T, check) :- var(X), occur_check(X, T), X \== T.
regle(T ?= X, orient) :- not(var(T)), var(X).
regle(F1 ?= F2, decompose) :- functor(F1, F, N), functor(F2, F, N).
regle(F ?= G, clash) :- functor(F, _, _), functor(G, _, _).


occur_check(V, T) :- contains_var(V, T).
