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

/*
echo('Début des tests :\n'),
    echo('//////////////Test des règles//////////////////\n'), full_rule_tests(),
    nl,
    echo('////////////Test des réductions////////////////\n'), full_reduct_tests(),
    nl.*/