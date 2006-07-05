%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Author:	Tom Schrijvers
% Email:	Tom.Schrijvers@cs.kuleuven.be
% Copyright:	K.U.Leuven 2004
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(builtins,
	[
		negate_b/2,
		entails_b/2,
		binds_b/2,
		builtin_binds_b/2
	]).

:- use_module(hprolog).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
negate_b(A,B) :- once(negate(A,B)).
negate((A,B),NotB) :- A==true,negate(B,NotB). % added by jon
negate((A,B),NotA) :- B==true,negate(A,NotA). % added by jon
negate((A,B),(NotA;NotB)) :- negate(A,NotA),negate(B,NotB). % added by jon
negate((A;B),(NotA,NotB)) :- negate(A,NotA),negate(B,NotB). % added by jon
negate(true,fail).
negate(fail,true).
negate(X =< Y, Y < X).
negate(X > Y, Y >= X).
negate(X >= Y, Y > X).
negate(X < Y, Y =< X).
negate(X == Y, X \== Y). % added by jon
negate(X \== Y, X == Y). % added by jon
negate(X =:= Y, X =\= Y). % added by jon
negate(X is Y, X =\= Y). % added by jon
negate(X =\= Y, X =:= Y). % added by jon
negate(X = Y, X \= Y). % added by jon
negate(X \= Y, X = Y). % added by jon
negate(var(X),nonvar(X)).
negate(nonvar(X),var(X)).
negate(\+ X,X). % added by jon
negate(X,\+ X). % added by jon

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
entails_b(fail,_) :-!.
entails_b(A,B) :-
	( var(B) ->
		entails(A,B,[A])
	;
		once((
			entails(A,C,[A]),
			B == C
		))
	).

entails(A,A,_).
entails(A,C,History) :-
	entails_(A,B),
	\+ hprolog:memberchk_eq(B,History),
	entails(B,C,[B|History]).		

entails_(X > Y, X >= Y).
entails_(X > Y, Y < X).
entails_(X >= Y, Y =< X).
entails_(X =< Y, Y >= X). %added by jon
entails_(X < Y, Y > X).
entails_(X < Y, X =< Y).
entails_(X > Y, X \== Y).
entails_(X \== Y, Y \== X).
entails_(X == Y, Y == X).
entails_(X == Y, X =:= Y) :- ground(X). %added by jon
entails_(X == Y, X =:= Y) :- ground(Y). %added by jon
entails_(X \== Y, X =\= Y) :- ground(X). %added by jon
entails_(X \== Y, X =\= Y) :- ground(Y). %added by jon
entails_(X =:= Y, Y =:= X). %added by jon
entails_(X =\= Y, Y =\= X). %added by jon
entails_(X == Y, X >= Y). %added by jon
entails_(X == Y, X =< Y). %added by jon
entails_(ground(X),nonvar(X)).
entails_(compound(X),nonvar(X)).
entails_(atomic(X),nonvar(X)).
entails_(number(X),nonvar(X)).
entails_(atom(X),nonvar(X)).
entails_(fail,true).

builtin_binds_b(G,Vars) :-
	builtin_binds_(G,L,[]),
	sort(L,Vars).

builtin_binds_(var(_),L,L).
builtin_binds_(nonvar(_),L,L).
builtin_binds_(ground(_),L,L).
builtin_binds_(compound(_),L,L).
builtin_binds_(number(_),L,L).
builtin_binds_(atom(_),L,L).
builtin_binds_(atomic(_),L,L).
builtin_binds_(integer(_),L,L).
builtin_binds_(float(_),L,L).

builtin_binds_(_ > _ ,L,L).
builtin_binds_(_ < _ ,L,L).
builtin_binds_(_ =< _,L,L).
builtin_binds_(_ >= _,L,L).
builtin_binds_(_ =:= _,L,L).
builtin_binds_(_ =\= _,L,L).
builtin_binds_(_ == _,L,L).
builtin_binds_(_ \== _,L,L).
builtin_binds_(true,L,L).

builtin_binds_(X is _,[X|L],L).
builtin_binds_((G1,G2),L,T) :-
	builtin_binds_(G1,L,R),
	builtin_binds_(G2,R,T).
builtin_binds_((G1;G2),L,T) :-
	builtin_binds_(G1,L,R),
	builtin_binds_(G2,R,T).
builtin_binds_((G1->G2),L,T) :-
	builtin_binds_(G1,L,R),
	builtin_binds_(G2,R,T).

builtin_binds_(\+ G,L,T) :-
	builtin_binds_(G,L,T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
binds_b(G,Vars) :-
	binds_(G,L,[]),
	sort(L,Vars).

binds_(var(_),L,L).
binds_(nonvar(_),L,L).
binds_(ground(_),L,L).
binds_(compound(_),L,L).
binds_(number(_),L,L).
binds_(atom(_),L,L).
binds_(atomic(_),L,L).
binds_(integer(_),L,L).
binds_(float(_),L,L).

binds_(_ > _ ,L,L).
binds_(_ < _ ,L,L).
binds_(_ =< _,L,L).
binds_(_ >= _,L,L).
binds_(_ =:= _,L,L).
binds_(_ =\= _,L,L).
binds_(_ == _,L,L).
binds_(_ \== _,L,L).
binds_(true,L,L).

binds_(X is _,[X|L],L).
binds_((G1,G2),L,T) :-
	binds_(G1,L,R),
	binds_(G2,R,T).
binds_((G1;G2),L,T) :-
	binds_(G1,L,R),
	binds_(G2,R,T).
binds_((G1->G2),L,T) :-
	binds_(G1,L,R),
	binds_(G2,R,T).

binds_(\+ G,L,T) :-
	binds_(G,L,T).

binds_(G,L,T) :- term_variables(G,GVars),append(GVars,T,L).	%jon
