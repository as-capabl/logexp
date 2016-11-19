% -*- prolog -*-
:- module(axiom, [
              vary/3,
              def_equiv/2,
              def_rewrite/2,
              alias/2,
              test/1
          ]).
:- use_module(engine).
:- set_rule_module(axiom).

% equivalence
:- discontiguous vary/3.
:- discontiguous def_equiv/2.
:- discontiguous def_rewrite/2.
:- discontiguous alias/2.
:- discontiguous test/1.

:- discontiguous commute/3.
:- discontiguous acommute/3.
:- discontiguous contract/4.
:- discontiguous unit_elem/2.
:- discontiguous associative/1.
:- discontiguous leibniz/1.

% util
zip([], [], []).
zip([X|XS], [Y|YS], [(X, Y)|ZS]) :- zip(XS, YS, ZS).

% operator
vary(opr(O, X), opr(O, Y), [(X, Y)]).
vary(oparr(O, L1), oparr(O, L2), L) :- zip(L1, L2, L).
%def_rewrite(oparr(O, [X|Y]), oparr(O, [X|Z])) :- rewrite(oparr(O, Y), oparr(O, Z)).

% bracket
%op_brace(opr(O, _)) :- brace(O).

% arithmetic
def_rewrite(oparr(_, [X]), X).
def_rewrite(oparr(O, X), oparr(O, Y)) :- associative(O), flatten_oparr(O, X, Y).
def_rewrite(oparr(O, X), Opa) :- unit_elem(O, Unit), select_oparr(oparr(O, X), Unit, Opa).
def_rewrite(oparr(O, []), Unit) :- unit_elem(O, Unit).

cons_oparr(oparr(O, [X|Tail]), X, oparr(O, Tail)).

select_oparr(oparr(O, [X|Tail]), X, oparr(O, Tail)).
select_oparr(oparr(O, [X|Tail]), Y, oparr(O, [X|T2])) :-
    select_oparr(oparr(O, Tail), Y, oparr(O, T2)), commute(O, X, Y).
select_oparr(oparr(O, [X|XS]), Y, Opa) :-
    select_oparr(oparr(O, XS), Y, oparr(O, YS)),
    acommute(O, X, Y, Exc),
    append(Exc, YS, Z),
    (rewrite(oparr(O, Z), Opa),!; Opa = oparr(O, Z)).

flatten_oparr(O, [oparr(O, X)|XS], L) :- may_flatten_oparr(O, XS, Y), append(X, Y, L).
flatten_oparr(O, [X|XS], [X|L]) :- flatten_oparr(O, XS, L).
may_flatten_oparr(O, [oparr(O, X)|XS], L) :- !, may_flatten_oparr(O, XS, Y), append(X, Y, L).
may_flatten_oparr(O, [X|XS], [X|L]) :- may_flatten_oparr(O, XS, L).
may_flatten_oparr(_, [], []).


def_equiv(oparr(O, [X|XS]), Opa2) :-
    select_oparr(Opa2, Y, Opa3), equiv(X, Y), equiv(oparr(O, XS), Opa3).

def_rewrite(Opa1, oparr(O, [Z|ZS])) :-
    select_oparr(Opa1, X, Opa2), select_oparr(Opa2, Y, oparr(O, ZS)),
    contract(O, X, Y, Z).

% Sum
alias(X+Y, oparr('+', [X, Y])).
associative('+').
commute('+', _, _).
unit_elem('+', 0).
contract('+', I, J, K) :- number(I), number(J), K is I + J.

alias(X-Y, oparr('+', [X, oparr(*, [-1, Y])])).
alias(-X, oparr(*, [-1, X])).

% Product
alias(X*Y, oparr('*', [X, Y])).
associative('*').
unit_elem('*', 1).
acommute('*', X, Y, [-1, X]) :- grassmann(X), grassmann(Y).
commute('*', X, Y) :- not(acommute('*', X, Y, _)).
contract('*', I, J, K) :- number(I), number(J), K is I * J.
contract('*', 0, _, 0).

% Distribution law
distributive('*', '+').

def_rewrite(oparr(O, L), oparr(P, M)) :- distributive(O, P), distrib(P, L, M), length_at_least(M, 2).

distrib(P, [oparr(P, X) | XS], L) :-
    length_at_least(X, 2), !, distrib(P, XS, L2), prepend_to_oparr(P, X, L2, L).
distrib(P, [X|XS], L) :- distrib(P, XS, L2), prepend_to_oparr(P, [X], L2, L).
distrib(_, [], [oparr('*', [U])]) :- unit_elem('*', U).

length_at_least(L, N) :- length(L, Len), Len >= N.

prepend_to_oparr(P, [X|XS], TailOps, L) :-
    pto_sub(P, X, TailOps, Y), prepend_to_oparr(P, XS, TailOps, YS), append(Y, YS, L).
prepend_to_oparr(P, [X|XS], [], [oparr('*', [X])|YS]) :- prepend_to_oparr(P, XS, [], YS).
prepend_to_oparr(_, [], _, []).

pto_sub(_, X, [oparr(O, XS)|L], [oparr(O, [X|XS])|M]) :- pto_sub(_, X, L, M).
pto_sub(_, _, [], []).

def_rewrite(Opa, oparr(P, [oparr(O, [Z|W])|L])) :-
    Opa = oparr(P, _),
    distributive(O, P),
    unit_elem(O, Unit),
    select_oparr(Opa, X0, Opa2),
    select_oparr(Opa2, Y0, oparr(P, L)),
    (X0 = oparr(O, M), !; M = [X0]),
    (Y0 = oparr(O, N), !; N = [Y0]),
    select_oparr(oparr(O, [Unit|M]), X, XS),
    select_oparr(oparr(O, [Unit|N]), Y, YS),
    contract(P, X, Y, Z),
    equiv(XS, YS),
    !,
    XS = oparr(O, W).


% Test
test(x+(y+z) ≡ (x+y)+z).
test(x+y ≡ y+x).
test(y+(z+x) ≡ (x+y)+z).
test(1+1 ≡ 2).
test(-(-x) ≡ x).
test(x-x ≡ 0).
test(2*4*x ≡ 8*x).
test(2*x*3 ≡ 6*x).
test(2*(3+x) ≡ 6 + 2*x).
test((3+x)*2 ≡ 6 + 2*x).
test((3+x)*(5+x) ≡ x*x + 8*x + 15).

grassmann(testg1).
grassmann(testg2).
test(testg1*testg2 ≡ -testg2*testg1).


% leibniz opr
def_rewrite(opr(D, FG), opr(D,F) + opr(D,G)) :-
    leibniz(D),
    FG = oparr(+, _),
    cons_oparr(FG, F, G).
def_rewrite(opr(D, FG), opr(D,F) * G + F * opr(D,G)) :-
    leibniz(D),
    FG = oparr(*, _),
    cons_oparr(FG, F, G).
def_rewrite(opr(D, I), 0) :- leibniz(D), number(I).

alias(testdiff(X), opr(testdiff, X)).
alias(test2diff(X), opr(testdiff, opr(testdiff, X))).
leibniz(testdiff).


test(testdiff(x+y) ≡ testdiff(x) + testdiff(y)).
test(testdiff(x*y) ≡ testdiff(x)*y + x*testdiff(y)).
test(test2diff(x+y) ≡ test2diff(x) + test2diff(y)).
