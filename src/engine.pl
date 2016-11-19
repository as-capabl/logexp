% -*- prolog -*-
:- module(engine, [
              rule_module/1,
              set_rule_module/1,
              runtest/0,
              equiv/2,
              rewrite/1,
              rewrite/2,
              '≡'/2,
              op(700, xfx, ≡)]
         ).

:- discontiguous def_equiv_/2.
:- discontiguous def_rewrite_/2.

:- op(900, xfx, @).

% Module management
:- dynamic rule_module/1.
% rule_module(user).

set_rule_module(M) :- rule_module(M), !.
set_rule_module(M) :- asserta(rule_module(M)).

vary_(X, Y, L) :- rule_module(M), M:vary(X, Y, L).

alias_(X, Y) :- rule_module(M), M:alias(X, Y).


% a brief test framework
runtest :- rule_module(M), M:test(X), runtestDo(X), false.
runtest.
runtestDo(X) :- X, !.
runtestDo(X) :- print_message(error, test_failure(X)).


% :- op(700, xfx, ≡).
X ≡ Y :- equiv(X, Y).

equiv(X, Y) :- may_rewrite(X, P), may_rewrite(Y, Q), def_equiv_(P, Q).

def_equiv_(X, Y) :- rule_module(M), M:def_equiv(X, Y).
def_equiv_(X, X).

rewrite(X, Y) :- def_rewrite_(X, Z), !, may_rewrite(Z, Y).

may_rewrite(X, Y) :- rewrite(X, Y), !.
may_rewrite(X, X).

rewrite([(X, Y)|Tail]) :- rewrite(X, Y), may_rewrite(Tail).
rewrite([(X, X)|Tail]) :- rewrite(Tail).

may_rewrite([]).
may_rewrite([(X, Y)|Tail]) :- may_rewrite(X, Y), may_rewrite(Tail).

def_rewrite_(X, Y) :- rule_module(M), M:def_rewrite(X, Y).
def_rewrite_(X, Y) :- alias_(X, Y).
% def_rewrite_(X, Y) :- rule_module(M), def_rewrite(X2, Y)@M, ralias(X2, X3), X3 = X.
def_rewrite_(X, Y) :- vary_(X, Y, L), rewrite(L).

may_ralias(X, Y) :- ralias(X, Y), !.
may_ralias(X, X).
ralias(X, X) :- var(X), !.
ralias(X, Y) :- alias_(X, Z), !, may_ralias(Z, Y).
ralias(X, Y) :- vary_(X, Y, L), ralias_sub(L).
ralias_sub([(X, Y)|Tail]) :- may_ralias(X, Y), ralias_sub(Tail).
ralias_sub([]).

