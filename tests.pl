reduct_test(reduit(R, X, [X], Q)) :- (regle(X, R) -> (reduit(R, X, [X], Q) -> echo(Q) ; echo('False')); echo('Unapplicable')).
reduct_test(R, X) :- echo('Test \''), echo(X), echo('\' : '), reduct_test(reduit(R, X, [X], Q)), echo('\n').
reduct_tests() :- 
    trace_unif([B ?= x, h(C, a) ?= D], choix_pondere_2).

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