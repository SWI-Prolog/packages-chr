/*  $Id$

    Part of CHR (Constraint Handling Rules)

    Author:        Christian Holzbaur and Tom Schrijvers
    E-mail:        christian@ai.univie.ac.at
		   Tom.Schrijvers@cs.kuleuven.be
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2003-2004, K.U. Leuven

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.

    Distributed with SWI-Prolog under the above conditions with
    permission from the authors.
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%       _                             _   _                
%%   ___| |__  _ __   _ __ _   _ _ __ | |_(_)_ __ ___   ___ 
%%  / __| '_ \| '__| | '__| | | | '_ \| __| | '_ ` _ \ / _ \
%% | (__| | | | |    | |  | |_| | | | | |_| | | | | | |  __/
%%  \___|_| |_|_|    |_|   \__,_|_| |_|\__|_|_| |_| |_|\___|
%%
%% hProlog CHR runtime:
%%
%% 	* based on the SICStus CHR runtime by Christian Holzbaur
%% 
%%          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%          %  Constraint Handling Rules		      version 2.2 %
%%          %								  %
%%          %  (c) Copyright 1996-98					  %
%%          %  LMU, Muenchen						  %
%% 	    %								  %
%%          %  File:   chr.pl						  %
%%          %  Author: Christian Holzbaur	christian@ai.univie.ac.at %
%%          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%%	
%%	* modified by Tom Schrijvers, K.U.Leuven, Tom.Schrijvers@cs.kuleuven.be
%%		- ported to hProlog
%%		- modified for eager suspension removal
%%
%%      * First working version: 6 June 2003
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SWI-Prolog changes
%% 
%% 	* Added initialization directives for saved-states
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(chr_runtime,
	  [ 'chr sbag_del_element'/3,
	    'chr sbag_member'/2,
	    'chr merge_attributes'/3,

	    'chr run_suspensions'/1,
	    'chr run_suspensions_loop'/1,
	    
	    'chr run_suspensions_d'/1,
	    'chr run_suspensions_loop_d'/1,

	    'chr insert_constraint_internal'/5,
	    'chr remove_constraint_internal'/2,
	    'chr allocate_constraint'/4,
	    'chr activate_constraint'/3,

	    'chr default_store'/1,

	    'chr via_1'/2,
	    'chr via_2'/3,
	    'chr via'/2,
	    'chr newvia_1'/2,
	    'chr newvia_2'/3,
	    'chr newvia'/2,

	    'chr lock'/1,
	    'chr unlock'/1,
	    'chr not_locked'/1,
	    'chr none_locked'/1,

	    'chr error_lock'/1,
	    'chr unerror_lock'/1,
	    'chr not_error_locked'/1,
	    'chr none_error_locked'/1,

	    'chr update_mutable'/2,
	    'chr get_mutable'/2,
	    'chr create_mutable'/2,

	    'chr novel_production'/2,
	    'chr extend_history'/2,
	    'chr empty_history'/1,

	    'chr gen_id'/1,

	    'chr debug_event'/1,
	    'chr debug command'/2,	% Char, Command

	    'chr chr_indexed_variables'/2,
	
	    'chr all_suspensions'/3,
	    'chr new_merge_attributes'/3,
	    'chr normalize_attr'/2,

	    'chr select'/3,

	    chr_show_store/1,	% +Module
	    find_chr_constraint/1,

	    chr_trace/0,
	    chr_notrace/0,
	    chr_leash/1
	  ]).

%% SWI begin
:- set_prolog_flag(generate_debug_info, false).
%% SWI end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                                       
:- use_module(library(dialect/hprolog)).
:- include(chr_op).

%% SICStus begin
%% :- use_module(hpattvars).
%% :- use_module(b_globval).
%% SICStus end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%   I N I T I A L I S A T I O N

%% SWI begin
:- dynamic user:exception/3.
:- multifile user:exception/3.

user:exception(undefined_global_variable, Name, retry) :-
	chr_runtime_global_variable(Name),
	chr_init.

chr_runtime_global_variable(chr_id).
chr_runtime_global_variable(chr_global).
chr_runtime_global_variable(chr_debug).
chr_runtime_global_variable(chr_debug_history).

chr_init :-
	nb_setval(chr_id,0),
	nb_setval(chr_global,_),
	nb_setval(chr_debug,mutable(off)),          % XXX
	nb_setval(chr_debug_history,mutable([],0)). % XXX
%% SWI end

%% SICStus begin
%% chr_init :-
%% 	        nb_setval(chr_id,0).
%% SICStus end

:- initialization chr_init.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Contents of former chr_debug.pl
%   
%	chr_show_store(+Module)
%	
%	Prints all suspended constraints of module   Mod to the standard
%	output.

chr_show_store(Mod) :-
	(
		Mod:'$enumerate_constraints'(Constraint),
		print(Constraint),nl, % allows use of portray to control printing
		fail
	;
		true
	).

find_chr_constraint(Constraint) :-
	chr:'$chr_module'(Mod),
	Mod:'$enumerate_constraints'(Constraint).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Inlining of some goals is good for performance
% That's the reason for the next section
% There must be correspondence with the predicates as implemented in chr_mutable.pl
% so that       user:goal_expansion(G,G). also works (but do not add such a rule)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% SWI begin
:- multifile user:goal_expansion/2.
:- dynamic   user:goal_expansion/2.

user:goal_expansion('chr get_mutable'(Val,Var),    Var=mutable(Val)).
user:goal_expansion('chr update_mutable'(Val,Var), setarg(1,Var,Val)).
user:goal_expansion('chr create_mutable'(Val,Var), Var=mutable(Val)).
user:goal_expansion('chr default_store'(X),        nb_getval(chr_global,X)).
%% SWI end

% goal_expansion seems too different in SICStus 4 for me to cater for in a
% decent way at this moment - so I stick with the old way to do this
% so that it doesn't get lost, the code from Mats for SICStus 4 is included in comments


%% Mats begin
%% goal_expansion('chr get_mutable'(Val,Var),    Lay, _M, get_mutable(Val,Var), Lay).
%% goal_expansion('chr update_mutable'(Val,Var), Lay, _M, update_mutable(Val,Var), Lay).
%% goal_expansion('chr create_mutable'(Val,Var), Lay, _M, create_mutable(Val,Var), Lay).
%% goal_expansion('chr default_store'(A),        Lay, _M, global_term_ref_1(A), Lay).
%% Mats begin


%% SICStus begin
%% :- multifile user:goal_expansion/2.
%% :- dynamic   user:goal_expansion/2.
%% 
%% user:goal_expansion('chr get_mutable'(Val,Var),    get_mutable(Val,Var)).
%% user:goal_expansion('chr update_mutable'(Val,Var), update_mutable(Val,Var)).
%% user:goal_expansion('chr create_mutable'(Val,Var), create_mutable(Val,Var)).
%% user:goal_expansion('chr default_store'(A),        global_term_ref_1(A)).
%% SICStus end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr run_suspensions'( Slots) :-
	    run_suspensions( Slots).

'chr run_suspensions_loop'([]).
'chr run_suspensions_loop'([L|Ls]) :-
	run_suspensions(L),
	'chr run_suspensions_loop'(Ls).

run_suspensions([]).
run_suspensions([S|Next] ) :-
	arg( 2, S, Mref), % ARGXXX
	'chr get_mutable'( Status, Mref),
	( Status==active ->
	    'chr update_mutable'( triggered, Mref),
	    arg( 4, S, Gref), % ARGXXX
	    'chr get_mutable'( Gen, Gref),
	    Generation is Gen+1,
	    'chr update_mutable'( Generation, Gref),
	    arg( 3, S, Goal), % ARGXXX
	    call( Goal),
	    'chr get_mutable'( Post, Mref),
	    ( Post==triggered ->
		'chr update_mutable'( active, Mref)	% catching constraints that did not do anything
	    ;
		true
	    )
	;
	    true
	),
	run_suspensions( Next).

'chr run_suspensions_d'( Slots) :-
	    run_suspensions_d( Slots).

'chr run_suspensions_loop_d'([]).
'chr run_suspensions_loop_d'([L|Ls]) :-
	run_suspensions_d(L),
	'chr run_suspensions_loop_d'(Ls).

run_suspensions_d([]).
run_suspensions_d([S|Next] ) :-
	arg( 2, S, Mref), % ARGXXX
	'chr get_mutable'( Status, Mref),
	( Status==active ->
	    'chr update_mutable'( triggered, Mref),
	    arg( 4, S, Gref), % ARGXXX
	    'chr get_mutable'( Gen, Gref),
	    Generation is Gen+1,
	    'chr update_mutable'( Generation, Gref),
	    arg( 3, S, Goal), % ARGXXX
	    ( 
		'chr debug_event'(wake(S)),
	        call( Goal)
	    ;
		'chr debug_event'(fail(S)), !,
		fail
	    ),
	    (
		'chr debug_event'(exit(S))
	    ;
		'chr debug_event'(redo(S)),
		fail
	    ),	
	    'chr get_mutable'( Post, Mref),
	    ( Post==triggered ->
		'chr update_mutable'( active, Mref)   % catching constraints that did not do anything
	    ;
		true
	    )
	;
	    true
	),
	run_suspensions_d( Next).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% L O C K I N G
%
%	locking of variables in guards

%= IMPLEMENTATION 1: SILENT FAILURE ============================================

%- attribute handler -----------------------------------------------------------
% 	intercepts unification of locked variable unification

locked:attr_unify_hook(_,_) :- fail.

%- locking & unlocking ---------------------------------------------------------
'chr lock'(T) :-
	( var(T)
	-> put_attr(T, locked, x)
        ;  term_variables(T,L),
           lockv(L)
	).

lockv([]).
lockv([T|R]) :- put_attr( T, locked, x), lockv(R).

'chr unlock'(T) :-
	( var(T)
	-> del_attr(T, locked)
	;  term_variables(T,L),
           unlockv(L)
	).

unlockv([]).
unlockv([T|R]) :- del_attr( T, locked), unlockv(R).

%- checking for locks ----------------------------------------------------------

'chr none_locked'( []).
'chr none_locked'( [V|Vs]) :-
	( get_attr(V, locked, _) ->
		fail
	;
		'chr none_locked'(Vs)
	).

'chr not_locked'(V) :-
	( var( V) ->
  		( get_attr( V, locked, _) ->
			fail
		;
			true
		)
	;
		true
	).

%= IMPLEMENTATION 2: EXPLICT EXCEPTION =========================================

%- LOCK ERROR MESSAGE ----------------------------------------------------------
lock_error(Term) :-
	throw(error(instantation_error(Term),context(_,'CHR Runtime Error: unification in guard not allowed!'))).

%- attribute handler -----------------------------------------------------------
% 	intercepts unification of locked variable unification

error_locked:attr_unify_hook(_,Term) :- lock_error(Term).

%- locking & unlocking ---------------------------------------------------------
'chr error_lock'(T) :-
	( var(T)
	-> put_attr(T, error_locked, x)
        ;  term_variables(T,L),
           error_lockv(L)
	).

error_lockv([]).
error_lockv([T|R]) :- put_attr( T, error_locked, x), error_lockv(R).

'chr unerror_lock'(T) :-
	( var(T)
	-> del_attr(T, error_locked)
	;  term_variables(T,L),
           unerror_lockv(L)
	).

unerror_lockv([]).
unerror_lockv([T|R]) :- del_attr( T, error_locked), unerror_lockv(R).

%- checking for locks ----------------------------------------------------------

'chr none_error_locked'( []).
'chr none_error_locked'( [V|Vs]) :-
	( get_attr(V, error_locked, _) ->
		fail
	;
		'chr none_error_locked'(Vs)
	).

'chr not_error_locked'(V) :-
	( var( V) ->
  		( get_attr( V, error_locked, _) ->
			fail
		;
			true
		)
	;
		true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Eager removal from all chains.
%
'chr remove_constraint_internal'( Susp, Agenda) :-
	arg( 2, Susp, Mref), % ARGXXX
	'chr get_mutable'( State, Mref), 
	'chr update_mutable'( removed, Mref),		% mark in any case
	( compound(State) ->			% passive/1
	    Agenda = []
	; State==removed ->
	    Agenda = []
	%; State==triggered ->
	%     Agenda = []
	;
            Susp =.. [_,_,_,_,_,_,_|Args],
	    term_variables( Args, Vars),
	    'chr default_store'( Global),
	    Agenda = [Global|Vars]
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr newvia_1'(X,V) :-
	( var(X) ->
		X = V
	; 
		nonground(X,V)
	).

'chr newvia_2'(X,Y,V) :- 
	( var(X) -> 
		X = V
	; var(Y) ->
		Y = V
	; compound(X), nonground(X,V) ->
		true
	; 
		compound(Y), nonground(Y,V)
	).

%
% The second arg is a witness.
% The formulation with term_variables/2 is
% cycle safe, but it finds a list of all vars.
% We need only one, and no list in particular.
%
'chr newvia'(L,V) :- nonground(L,V).
%~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-

'chr via_1'(X,V) :-
	( var(X) ->
		X = V
	; atomic(X) ->
		'chr default_store'(V)
	; nonground(X,V) ->
		true
	;
		'chr default_store'(V)
	).

'chr via_2'(X,Y,V) :- 
	( var(X) -> 
		X = V
	; var(Y) ->
		Y = V
	; compound(X), nonground(X,V) ->
		true
	; compound(Y), nonground(Y,V) ->
		true
	;
		'chr default_store'(V)
	).

%
% The second arg is a witness.
% The formulation with term_variables/2 is
% cycle safe, but it finds a list of all vars.
% We need only one, and no list in particular.
%
'chr via'(L,V) :-
	( nonground(L,V) ->
		true
	;
		'chr default_store'(V)
	).

nonground( Term, V) :-
	term_variables( Term, Vs),
	Vs = [V|_].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr novel_production'( Self, Tuple) :-
	arg( 5, Self, Ref), % ARGXXX
	'chr get_mutable'( History, Ref),
	( get_ds( Tuple, History, _) ->
	    fail
	;
	    true
	).

%
% Not folded with novel_production/2 because guard checking
% goes in between the two calls.
%
'chr extend_history'( Self, Tuple) :-
	arg( 5, Self, Ref), % ARGXXX
	'chr get_mutable'( History, Ref),
	put_ds( Tuple, History, x, NewHistory),
	'chr update_mutable'( NewHistory, Ref).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint_generation( Susp, State, Generation) :-
	arg( 2, Susp, Mref), % ARGXXX
	'chr get_mutable'( State, Mref),
	arg( 4, Susp, Gref), % ARGXXX
	'chr get_mutable'( Generation, Gref). 	% not incremented meanwhile 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr allocate_constraint'( Closure, Self, F, Args) :-
	Self =.. [suspension,Id,Mref,Closure,Gref,Href,F|Args], % SUSPXXX
	'chr create_mutable'(0, Gref),
	'chr empty_history'(History),
	'chr create_mutable'(History, Href),
	'chr create_mutable'(passive(Args), Mref),
	'chr gen_id'( Id).

%
% 'chr activate_constraint'( -, +, -).
%
% The transition gc->active should be rare
%
'chr activate_constraint'( Vars, Susp, Generation) :-
	arg( 2, Susp, Mref), % ARGXXX
	'chr get_mutable'( State, Mref),
	'chr update_mutable'( active, Mref),
	( nonvar(Generation) ->			% aih
	    true
	;
	    arg( 4, Susp, Gref), % ARGXXX
	    'chr get_mutable'( Gen, Gref),
	    Generation is Gen+1,
	    'chr update_mutable'( Generation, Gref)
	),
	( compound(State) ->			% passive/1
	    term_variables( State, Vs),
	    'chr none_locked'( Vs),
	    Vars = [Global|Vs],
	    'chr default_store'(Global)
	; State == removed ->			% the price for eager removal ...
	    Susp =.. [_,_,_,_,_,_,_|Args],
	    term_variables( Args, Vs),
	    Vars = [Global|Vs],
	    'chr default_store'(Global)
	;
	    Vars = []
	).

'chr insert_constraint_internal'([Global|Vars], Self, Closure, F, Args) :-
	'chr default_store'(Global),
	term_variables(Args,Vars),
	'chr none_locked'(Vars),
	Self =.. [suspension,Id,Mref,Closure,Gref,Href,F|Args], % SUSPXXX
	'chr create_mutable'(active, Mref),
	'chr create_mutable'(0, Gref),
	'chr empty_history'(History),
	'chr create_mutable'(History, Href),
	'chr gen_id'(Id).

insert_constraint_internal([Global|Vars], Self, Term, Closure, F, Args) :-
	'chr default_store'(Global),
	term_variables( Term, Vars),
	'chr none_locked'( Vars),
	'chr empty_history'( History),
	'chr create_mutable'( active, Mref),
	'chr create_mutable'( 0, Gref),
	'chr create_mutable'( History, Href),
	'chr gen_id'( Id),
	Self =.. [suspension,Id,Mref,Closure,Gref,Href,F|Args]. % SUSPXXX

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr empty_history'( E) :- empty_ds( E).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr gen_id'( Id) :-
	nb_getval(chr_id,Id),
	NextId is Id + 1,
	nb_setval(chr_id,NextId).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% SWI begin
'chr create_mutable'(V,mutable(V)).
'chr get_mutable'(V,mutable(V)).  
'chr update_mutable'(V,M) :- setarg(1,M,V).
%% SWI end

%% SICStus begin
%% 'chr create_mutable'(Val, Mut) :- create_mutable(Val, Mut).
%% 'chr get_mutable'(Val, Mut) :- get_mutable(Val, Mut).
%% 'chr update_mutable'(Val, Mut) :- update_mutable(Val, Mut).
%% SICStus end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SWI begin
'chr default_store'(X) :- nb_getval(chr_global,X).
%% SWI end

%% SICStus begin
%% 'chr default_store'(A) :- global_term_ref_1(A).
%% SICStus end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

'chr sbag_member'( Element, [Head|Tail]) :-
      sbag_member( Element, Tail, Head).

% auxiliary to avoid choicepoint for last element
        % does it really avoid the choicepoint? -jon
 sbag_member( E, _,	     E).
 sbag_member( E, [Head|Tail], _) :-
 	sbag_member( E, Tail, Head).
 
'chr sbag_del_element'( [],	  _,	[]).
'chr sbag_del_element'( [X|Xs], Elem, Set2) :-
	( X==Elem ->
	    Set2 = Xs
	;
	    Set2 = [X|Xss],
	    'chr sbag_del_element'( Xs, Elem, Xss)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
'chr merge_attributes'([],Ys,Ys).
'chr merge_attributes'([X | Xs],YL,R) :-
  ( YL = [Y | Ys] ->
      arg(1,X,XId), % ARGXXX
      arg(1,Y,YId),	 % ARGXXX
       ( XId < YId ->
           R = [X | T],
           'chr merge_attributes'(Xs,YL,T)
       ; XId > YId ->
           R = [Y | T],
           'chr merge_attributes'([X|Xs],Ys,T)
       ;
           R = [X | T],
           'chr merge_attributes'(Xs,Ys,T)
       )    
  ;
       R = [X | Xs]
  ).

'chr new_merge_attributes'([],A2,A) :-
	A = A2.
'chr new_merge_attributes'([E1|AT1],A2,A) :-
	( A2 = [E2|AT2] ->
		'chr new_merge_attributes'(E1,E2,AT1,AT2,A)
	;
		A = [E1|AT1]
	).
		
'chr new_merge_attributes'(Pos1-L1,Pos2-L2,AT1,AT2,A) :-
	( Pos1 < Pos2 ->
		A = [Pos1-L1|AT],
		'chr new_merge_attributes'(AT1,[Pos2-L2|AT2],AT)
	; Pos1 > Pos2 ->
		A = [Pos2-L2|AT],
		'chr new_merge_attributes'([Pos1-L1|AT1],AT2,AT)
	;
		'chr merge_attributes'(L1,L2,L),
		A = [Pos1-L|AT],
		'chr new_merge_attributes'(AT1,AT2,AT)
	).

'chr all_suspensions'([],_,_).
'chr all_suspensions'([Susps|SuspsList],Pos,Attr) :-
	all_suspensions(Attr,Susps,SuspsList,Pos).

all_suspensions([],[],SuspsList,Pos) :-
	all_suspensions([],[],SuspsList,Pos). % all empty lists
all_suspensions([APos-ASusps|RAttr],Susps,SuspsList,Pos) :-
	NPos is Pos + 1,
	( Pos == APos ->
		Susps = ASusps,
		'chr all_suspensions'(SuspsList,NPos,RAttr)
	;
		Susps = [],
		'chr all_suspensions'(SuspsList,NPos,[APos-ASusps|RAttr])
	).

'chr normalize_attr'([],[]).
'chr normalize_attr'([Pos-L|R],[Pos-NL|NR]) :-
	sort(L,NL),
	'chr normalize_attr'(R,NR).			

'chr select'([E|T],F,R) :-
	( E = F ->
		R = T
	;
		R = [E|NR],
		'chr select'(T,F,NR)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- multifile
	chr:debug_event/2,		% +State, +Event
	chr:debug_interact/3.		% +Event, +Depth, -Command

'chr debug_event'(Event) :-
	nb_getval(chr_debug,mutable(State)),  % XXX
	( State == off ->
		true
	; chr:debug_event(State, Event) ->
		true
	; 	debug_event(State,Event)
	).

chr_trace :-
	nb_setval(chr_debug,mutable(trace)).
chr_notrace :-
	nb_setval(chr_debug,mutable(off)).

%	chr_leash(+Spec)
%	
%	Define the set of ports at which we prompt for user interaction

chr_leash(Spec) :-
	leashed_ports(Spec, Ports),
	nb_setval(chr_leash,mutable(Ports)).

leashed_ports(none, []).
leashed_ports(off,  []).
leashed_ports(all,  [call, exit, redo, fail, wake, try, apply, insert, remove]).
leashed_ports(default, [call,exit,fail,wake,apply]).
leashed_ports(One, Ports) :-
	atom(One), One \== [], !,
	leashed_ports([One], Ports).
leashed_ports(Set, Ports) :-
	sort(Set, Ports),		% make unique
	leashed_ports(all, All),
	valid_ports(Ports, All).

valid_ports([], _).
valid_ports([H|T], Valid) :-
	(   memberchk(H, Valid)
	->  true
	;   throw(error(domain_error(chr_port, H), _))
	),
	valid_ports(T, Valid).

user:exception(undefined_global_variable, Name, retry) :-
	chr_runtime_debug_global_variable(Name),
	chr_debug_init.

chr_runtime_debug_global_variable(chr_leash).

chr_debug_init :-
   leashed_ports(default, Ports),
   nb_setval(chr_leash, mutable(Ports)).

:- initialization chr_debug_init.

%	debug_event(+State, +Event)


%debug_event(trace, Event) :-
%	functor(Event, Name, Arity),
%	writeln(Name/Arity), fail.
debug_event(trace,Event) :- 
	Event = call(_), !,
	get_debug_history(History,Depth),
	NDepth is Depth + 1,
	chr_debug_interact(Event,NDepth), 
	set_debug_history([Event|History],NDepth).
debug_event(trace,Event) :- 
	Event = wake(_), !,
	get_debug_history(History,Depth),
	NDepth is Depth + 1,
	chr_debug_interact(Event,NDepth), 
	set_debug_history([Event|History],NDepth).
debug_event(trace,Event) :-
	Event = redo(_), !,
	get_debug_history(_History, Depth),
	chr_debug_interact(Event, Depth).
debug_event(trace,Event) :- 
	Event = exit(_),!,
	get_debug_history([_|History],Depth),
	chr_debug_interact(Event,Depth),
	NDepth is Depth - 1,
	set_debug_history(History,NDepth). 
debug_event(trace,Event) :- 
	Event = fail(_),!,
	get_debug_history(_,Depth),
	chr_debug_interact(Event,Depth). 
debug_event(trace, Event) :-
	Event = remove(_), !,
	get_debug_history(_,Depth),
	chr_debug_interact(Event, Depth).
debug_event(trace, Event) :-
	Event = insert(_), !,
	get_debug_history(_,Depth),
	chr_debug_interact(Event, Depth).
debug_event(trace, Event) :-
	Event = try(_,_,_,_), !,
	get_debug_history(_,Depth),
	chr_debug_interact(Event, Depth).
debug_event(trace, Event) :- 
	Event = apply(_,_,_,_), !,
	get_debug_history(_,Depth),
	chr_debug_interact(Event,Depth). 

debug_event(skip(_,_),Event) :- 
	Event = call(_), !,
	get_debug_history(History,Depth),
	NDepth is Depth + 1,
	set_debug_history([Event|History],NDepth).
debug_event(skip(_,_),Event) :- 
	Event = wake(_), !,
	get_debug_history(History,Depth),
	NDepth is Depth + 1,
	set_debug_history([Event|History],NDepth).
debug_event(skip(SkipSusp,SkipDepth),Event) :- 
	Event = exit(Susp),!,
	get_debug_history([_|History],Depth),
	( SkipDepth == Depth,
	  SkipSusp == Susp -> 
		set_chr_debug(trace),
		chr_debug_interact(Event,Depth)
	;
		true
	),
	NDepth is Depth - 1,
	set_debug_history(History,NDepth). 
debug_event(skip(_,_),_) :- !,
	true.

%	chr_debug_interact(+Event, +Depth)
%	
%	Interact with the user on Event that took place at Depth.  First
%	calls chr:debug_interact(+Event, +Depth, -Command) hook. If this
%	fails the event is printed and the system prompts for a command.

chr_debug_interact(Event, Depth) :-
	chr:debug_interact(Event, Depth, Command), !,
	handle_debug_command(Command,Event,Depth).
chr_debug_interact(Event, Depth) :-
	print_event(Event, Depth),
	(   leashed(Event)
	->  ask_continue(Command)
	;   Command = creep
	),
	handle_debug_command(Command,Event,Depth).

leashed(Event) :-
	functor(Event, Port, _),
	nb_getval(chr_leash, mutable(Ports)),
	memberchk(Port, Ports).

ask_continue(Command) :-
	print_message(debug, chr(prompt)),
	get_single_char(CharCode),
	(   CharCode == -1
	->  Char = end_of_file
	;   char_code(Char, CharCode)
	),
	(   debug_command(Char, Command)
	->  print_message(debug, chr(command(Command)))
	;   print_message(help, chr(invalid_command)),
	    ask_continue(Command)
	).


'chr debug command'(Char, Command) :-
	debug_command(Char, Command).

debug_command(c, creep).
debug_command(' ', creep).
debug_command('\r', creep).
debug_command(s, skip).
debug_command(g, ancestors).
debug_command(n, nodebug).
debug_command(a, abort).
debug_command(f, fail).
debug_command(b, break).
debug_command(?, help).
debug_command(h, help).
debug_command(end_of_file, exit).


handle_debug_command(creep,_,_) :- !.
handle_debug_command(skip, Event, Depth) :- !,
	Event =.. [Type|Rest],
	( Type \== call,
	  Type \== wake ->
		handle_debug_command('c',Event,Depth)
	;
		Rest = [Susp],
		set_chr_debug(skip(Susp,Depth))
	).
	
handle_debug_command(ancestors,Event,Depth) :- !,
	print_chr_debug_history,
	chr_debug_interact(Event,Depth).	
handle_debug_command(nodebug,_,_) :- !,
	chr_notrace.
handle_debug_command(abort,_,_) :- !,
	abort.
handle_debug_command(exit,_,_) :- !,
	halt.
handle_debug_command(fail,_,_) :- !,
	fail.
handle_debug_command(break,Event,Depth) :- !,
	break,
	chr_debug_interact(Event,Depth).
handle_debug_command(help,Event,Depth) :- !,
	print_message(help, chr(debug_options)),
	chr_debug_interact(Event,Depth).	
handle_debug_command(Cmd, _, _) :- 
	throw(error(domain_error(chr_debug_command, Cmd), _)).

print_chr_debug_history :-
	get_debug_history(History,Depth),
	print_message(debug, chr(ancestors(History, Depth))).

print_event(Event, Depth) :-
	print_message(debug, chr(event(Event, Depth))).

%	{set,get}_debug_history(Ancestors, Depth)
%	
%	Set/get the list of ancestors and the depth of the current goal.

get_debug_history(History,Depth) :-
	nb_getval(chr_debug_history,mutable(History,Depth)).

set_debug_history(History,Depth) :-
	nb_getval(chr_debug_history,Mutable),
	setarg(1,Mutable,History),
	setarg(2,Mutable,Depth).

set_chr_debug(State) :-
	nb_getval(chr_debug,Mutable),
	setarg(1,Mutable,State).

'chr chr_indexed_variables'(Susp,Vars) :-
        Susp =.. [_,_,_,_,_,_,_|Args],
	term_variables(Args,Vars).
