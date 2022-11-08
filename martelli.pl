#!/usr/bin/env swipl

:- op(20,xfy,?=).

% echo(T): affiche T
echo(T) :- write(T).
echo(_).

:- initialization(main, main).

% Fonction main
main(Argv) :-
    echo(Argv).