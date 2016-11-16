/*  Part of CHR (Constraint Handling Rules)

    Author:        Tom Schrijvers
    E-mail:        Tom.Schrijvers@cs.kuleuven.be
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2005-2011, K.U. Leuven
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(deadcode,[deadcode/2]).

:- use_module(library(chr)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- constraints
	defined_predicate(+any),
	calls(+any,+any),
	live(+any),
	print_dead_predicates.

defined_predicate(P) \ defined_predicate(P) <=> true.

calls(P,Q) \ calls(P,Q) <=> true.

live(P) \ live(P) <=> true.

live(P), calls(P,Q) ==> live(Q).

print_dead_predicates \ live(P), defined_predicate(P) <=> true.
print_dead_predicates \ defined_predicate(P) <=>
	writeln(P).
print_dead_predicates \ calls(_,_) <=> true.
print_dead_predicates \ live(_) <=> true.
print_dead_predicates <=> true.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

deadcode(File,Starts) :-
	readfile(File,Clauses),
	exported_predicates(Clauses,Exports),
	findall(C, ( member(C,Clauses), C \= (:- _) , C \= (?- _)), Cs),
	process_clauses(Cs),
	append(Starts,Exports,Alive),
	live_predicates(Alive),
	print_dead_predicates.

exported_predicates(Clauses,Exports) :-
	( member( (:- module(_, Exports)), Clauses) ->
		true
	;
		Exports = []
	).
process_clauses([]).
process_clauses([C|Cs]) :-
	hb(C,H,B),
	extract_predicates(B,Ps,[]),
	functor(H,F,A),
	defined_predicate(F/A),
	calls_predicates(Ps,F/A),
	process_clauses(Cs).

calls_predicates([],FA).
calls_predicates([P|Ps],FA) :-
	calls(FA,P),
	calls_predicates(Ps,FA).

hb(C,H,B) :-
	( C = (H :- B) ->
		true
	;
		C = H,
		B = true
	).

live_predicates([]).
live_predicates([P|Ps]) :-
	live(P),
	live_predicates(Ps).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
extract_predicates(!,L,L) :- ! .
extract_predicates(_ < _,L,L) :- ! .
extract_predicates(_ = _,L,L) :- ! .
extract_predicates(_ =.. _ ,L,L) :- ! .
extract_predicates(_ =:= _,L,L) :- ! .
extract_predicates(_ == _,L,L) :- ! .
extract_predicates(_ > _,L,L) :- ! .
extract_predicates(_ \= _,L,L) :- ! .
extract_predicates(_ \== _,L,L) :- ! .
extract_predicates(_ is _,L,L) :- ! .
extract_predicates(arg(_,_,_),L,L) :- ! .
extract_predicates(atom_concat(_,_,_),L,L) :- ! .
extract_predicates(atomic(_),L,L) :- ! .
extract_predicates(b_getval(_,_),L,L) :- ! .
extract_predicates(call(_),L,L) :- ! .
extract_predicates(compound(_),L,L) :- ! .
extract_predicates(copy_term(_,_),L,L) :- ! .
extract_predicates(del_attr(_,_),L,L) :- ! .
extract_predicates(fail,L,L) :- ! .
extract_predicates(functor(_,_,_),L,L) :- ! .
extract_predicates(get_attr(_,_,_),L,L) :- ! .
extract_predicates(length(_,_),L,L) :- ! .
extract_predicates(nb_setval(_,_),L,L) :- ! .
extract_predicates(nl,L,L) :- ! .
extract_predicates(nonvar(_),L,L) :- ! .
extract_predicates(once(G),L,T) :- !,
	( nonvar(G) ->
		extract_predicates(G,L,T)
	;
		L = T
	).
extract_predicates(op(_,_,_),L,L) :- ! .
extract_predicates(prolog_flag(_,_),L,L) :- ! .
extract_predicates(prolog_flag(_,_,_),L,L) :- ! .
extract_predicates(put_attr(_,_,_),L,L) :- ! .
extract_predicates(read(_),L,L) :- ! .
extract_predicates(see(_),L,L) :- ! .
extract_predicates(seen,L,L) :- ! .
extract_predicates(setarg(_,_,_),L,L) :- ! .
extract_predicates(tell(_),L,L) :- ! .
extract_predicates(term_variables(_,_),L,L) :- ! .
extract_predicates(told,L,L) :- ! .
extract_predicates(true,L,L) :- ! .
extract_predicates(var(_),L,L) :- ! .
extract_predicates(write(_),L,L) :- ! .
extract_predicates((G1,G2),L,T) :- ! ,
	extract_predicates(G1,L,T1),
	extract_predicates(G2,T1,T).
extract_predicates((G1->G2),L,T) :- !,
	extract_predicates(G1,L,T1),
	extract_predicates(G2,T1,T).
extract_predicates((G1;G2),L,T) :- !,
	extract_predicates(G1,L,T1),
	extract_predicates(G2,T1,T).
extract_predicates(\+ G, L, T) :- !,
	extract_predicates(G, L, T).
extract_predicates(findall(_,G,_),L,T) :- !,
	extract_predicates(G,L,T).
extract_predicates(bagof(_,G,_),L,T) :- !,
	extract_predicates(G,L,T).
extract_predicates(_^G,L,T) :- !,
	extract_predicates(G,L,T).
extract_predicates(_:Call,L,T) :- !,
	extract_predicates(Call,L,T).
extract_predicates(Call,L,T) :-
	( var(Call) ->
		L = T
	;
		functor(Call,F,A),
		L = [F/A|T]
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% File Reading

readfile(File,Declarations) :-
	see(File),
	readcontent(Declarations),
	seen.

readcontent(C) :-
	read(X),
	( X = (:- op(Prec,Fix,Op)) ->
		op(Prec,Fix,Op)
	;
		true
	),
	( X == end_of_file ->
		C = []
	;
		C = [X | Xs],
		readcontent(Xs)
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

