/*  $Id$

    Part of CHR (Constraint Handling Rules)

    Author:        Tom Schrijvers
    E-mail:        Tom.Schrijvers@cs.kuleuven.be
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
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%   ____ _   _ ____     ____                      _ _
%%  / ___| | | |  _ \   / ___|___  _ __ ___  _ __ (_) | ___ _ __
%% | |   | |_| | |_) | | |   / _ \| '_ ` _ \| '_ \| | |/ _ \ '__|
%% | |___|  _  |  _ <  | |__| (_) | | | | | | |_) | | |  __/ |
%%  \____|_| |_|_| \_\  \____\___/|_| |_| |_| .__/|_|_|\___|_|
%%                                          |_|
%%
%% hProlog CHR compiler:
%%
%%	* by Tom Schrijvers, K.U. Leuven, Tom.Schrijvers@cs.kuleuven.be
%%
%%	* based on the SICStus CHR compilation by Christian Holzbaur
%%
%% First working version: 6 June 2003
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% To Do
%%
%%	* SICStus compatibility
%%		- rules/1 declaration
%%		- options
%%		- pragmas
%%		- tell guard
%%
%%
%%	* do not suspend on variables that don't matter
%%	* make difference between cheap guards		for reordering
%%	                      and non-binding guards	for lock removal
%%
%%	* unqiue -> once/[] transformation for propagation
%%
%%	* cheap guards interleaved with head retrieval + faster
%%	  via-retrieval + non-empty checking for propagation rules
%%	  redo for simpagation_head2 prelude
%%
%%	* intelligent backtracking for simplification/simpagation rule
%%		generator_1(X),'_$savecp'(CP_1),
%%              ... 
%%              if( (
%%			generator_n(Y), 
%%		     	test(X,Y)
%%		    ),
%%		    true,
%%		    ('_$cutto'(CP_1), fail)
%%		),
%%		...
%%
%%	  or recently developped cascading-supported approach 
%%
%%      * intelligent backtracking for propagation rule
%%          use additional boolean argument for each possible smart backtracking
%%          when boolean at end of list true  -> no smart backtracking
%%                                      false -> smart backtracking
%%          only works for rules with at least 3 constraints in the head
%%
%%	* mutually exclusive rules
%%
%%	* constraints that can never be attached / always simplified away
%%		-> need not be considered in diverse operations
%%
%%	* (set semantics + functional dependency) declaration + resolution
%%
%%	* type and instantiation declarations + optimisations
%%		+ better indexes
%%
%%	* disable global store option
%%
%% Done
%%
%%	* clean up generated code
%%	* input verification: pragmas
%%	* SICStus compatibility: handler/1, constraints/1
%% 	* optimise variable passing for propagation rule
%%	* reordering of head constraints for passive head search
%%	* unique inference for simpagation rules
%%	* unique optimisation for simpagation and simplification rules
%%	* cheap guards interleaved with head retrieval + faster
%%	  via-retrieval + non-empty checking for simplification / simpagation rules
%%	* transform 
%%		C \ C <=> true
%%	  into
%%		C # ID \ C <=> true pragma passive.
%%	* valid to disregard body in uniqueness inference?
%%	* unique inference for simplification rules
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(chr_translate,
	  [ chr_translate/2		% +Decls, -TranslatedDecls
	  ]).
%% SWI begin
:- use_module(library(lists),[member/2,append/3,permutation/2,reverse/2]).
:- use_module(library(ordsets)).
%% SWI end
:- use_module(library(dialect/hprolog)).
:- use_module(pairlist).
:- include(chr_op).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Translation

chr_translate(Declarations,NewDeclarations) :-
	init_chr_pp_flags,
	partition_clauses(Declarations,Decls,Rules,OtherClauses,Mod),
	default(Mod,user),
	( Decls == [] ->
		NewDeclarations = OtherClauses
	;
		check_rules(Rules,Decls),
		unique_analyse_optimise(Rules,1,[],NRules),
		generate_attach_a_constraint_all(Decls,Mod,AttachAConstraintClauses),
		generate_detach_a_constraint_all(Decls,Mod,DettachAConstraintClauses),
		generate_attach_increment(Decls,Mod,AttachIncrementClauses),
		generate_attr_unify_hook(Decls,Mod,AttrUnifyHookClauses),
		constraints_code(Decls,NRules,Mod,ConstraintClauses),
		append([ OtherClauses,
			 AttachAConstraintClauses,
			 DettachAConstraintClauses,
			 AttachIncrementClauses,
			 AttrUnifyHookClauses,
			 ConstraintClauses
		       ],
		       NewDeclarations)
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Partitioning of clauses into constraint declarations, chr rules and other 
%% clauses

partition_clauses([],[],[],[],_).
partition_clauses([C|Cs],Ds,Rs,OCs,Mod) :-
  (   rule(C,R) ->
      Ds = RDs,
      Rs = [R | RRs], 
      OCs = ROCs
  ;   is_declaration(C,D) ->
      append(D,RDs,Ds),
      Rs = RRs,
      OCs = ROCs
  ;   is_module_declaration(C,Mod) ->
      Ds = RDs,
      Rs = RRs,
      OCs = [C|ROCs]
  ;   C = (handler _) ->
      format('CHR compiler WARNING: ~w.\n',[C]),
      format('    `-->  SICStus compatibility: ignoring handler/1 declaration.\n',[]),
      Ds = RDs,
      Rs = RRs,
      OCs = ROCs
  ;   C = (rules _) ->
      format('CHR compiler WARNING: ~w.\n',[C]),
      format('    `-->  SICStus compatibility: ignoring rules/1 declaration.\n',[]),
      Ds = RDs,
      Rs = RRs,
      OCs = ROCs
  ;   C = (:- chr_option(OptionName,OptionValue)) ->
      handle_option(OptionName,OptionValue),
      Ds = RDs,
      Rs = RRs,
      OCs = ROCs
  ;   Ds = RDs,
      Rs = RRs,
      OCs = [C|ROCs]
  ),
  partition_clauses(Cs,RDs,RRs,ROCs,Mod).

is_declaration(D, Constraints) :-		%% constraint declaration
  D = (:- Decl),
  ( Decl =.. [chr_constraint,Cs] ; Decl =.. [chr_constraint,Cs]),
  conj2list(Cs,Constraints).

%% Data Declaration
%%
%% pragma_rule 
%%	-> pragma(
%%		rule,
%%		ids,
%%		list(pragma),
%%		yesno(string)
%%		)
%%
%% ids	-> ids(
%%		list(int),
%%		list(int)
%%		)
%%		
%% rule -> rule(
%%		list(constraint),	:: constraints to be removed
%%		list(constraint),	:: surviving constraints
%%		goal,			:: guard
%%		goal			:: body
%%	 	)

rule(RI,R) :-				%% name @ rule
	RI = (Name @ RI2), !,
	rule(RI2,yes(Name),R).
rule(RI,R) :-
	rule(RI,no,R).

rule(RI,Name,R) :-
	RI = (RI2 pragma P), !,			%% pragmas
	is_rule(RI2,R1,IDs),
	conj2list(P,Ps),
	R = pragma(R1,IDs,Ps,Name).
rule(RI,Name,R) :-
	is_rule(RI,R1,IDs),
	R = pragma(R1,IDs,[],Name).

is_rule(RI,R,IDs) :-				%% propagation rule
   RI = (H ==> B), !,
   conj2list(H,Head2i),
   get_ids(Head2i,IDs2,Head2),
   IDs = ids([],IDs2),
   (   B = (G | RB) ->
       R = rule([],Head2,G,RB)
   ;
       R = rule([],Head2,true,B)
   ).
is_rule(RI,R,IDs) :-				%% simplification/simpagation rule
   RI = (H <=> B), !,
   (   B = (G | RB) ->
       Guard = G,
       Body  = RB
   ;   Guard = true,
       Body = B
   ),
   (   H = (H1 \ H2) ->
       conj2list(H1,Head2i),
       conj2list(H2,Head1i),
       get_ids(Head2i,IDs2,Head2,0,N),
       get_ids(Head1i,IDs1,Head1,N,_),
       IDs = ids(IDs1,IDs2)
   ;   conj2list(H,Head1i),
       Head2 = [],
       get_ids(Head1i,IDs1,Head1),
       IDs = ids(IDs1,[])
   ),
   R = rule(Head1,Head2,Guard,Body).

get_ids(Cs,IDs,NCs) :-
	get_ids(Cs,IDs,NCs,0,_).

get_ids([],[],[],N,N).
get_ids([C|Cs],[N|IDs],[NC|NCs],N,NN) :-
	( C = (NC # N) ->
		true
	;
		NC = C
	),
	M is N + 1,
	get_ids(Cs,IDs,NCs, M,NN).

is_module_declaration((:- module(Mod)),Mod).
is_module_declaration((:- module(Mod,_)),Mod).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some input verification:
%%  - all constraints in heads are declared constraints

check_rules(Rules,Decls) :-
	check_rules(Rules,Decls,1).

check_rules([],_,_).
check_rules([PragmaRule|Rest],Decls,N) :-
	check_rule(PragmaRule,Decls,N),
	N1 is N + 1,
	check_rules(Rest,Decls,N1).

check_rule(PragmaRule,Decls,N) :-
	PragmaRule = pragma(Rule,_IDs,Pragmas,_Name),
	Rule = rule(H1,H2,_,_),
	append(H1,H2,HeadConstraints),
	check_head_constraints(HeadConstraints,Decls,PragmaRule,N),
	check_pragmas(Pragmas,PragmaRule,N).

check_head_constraints([],_,_,_).
check_head_constraints([Constr|Rest],Decls,PragmaRule,N) :-
	functor(Constr,F,A),
	( member(F/A,Decls) ->
		check_head_constraints(Rest,Decls,PragmaRule,N)
	;
		format('CHR compiler ERROR: Undeclared constraint ~w in head of ~@.\n',
		       [F/A,format_rule(PragmaRule,N)]),
		format('    `--> Constraint should be on of ~w.\n',[Decls]),
		fail
	).

check_pragmas([],_,_).
check_pragmas([Pragma|Pragmas],PragmaRule,N) :-
	check_pragma(Pragma,PragmaRule,N),
	check_pragmas(Pragmas,PragmaRule,N).

check_pragma(Pragma,PragmaRule,N) :-
	var(Pragma), !,
	format('CHR compiler ERROR: invalid pragma ~w in ~@.\n',
               [Pragma,format_rule(PragmaRule,N)]),
	format('    `--> Pragma should not be a variable!\n',[]),
	fail.

check_pragma(passive(ID), PragmaRule, N) :-
	!,
	PragmaRule = pragma(_,ids(IDs1,IDs2),_,_),
	( memberchk_eq(ID,IDs1) ->
		true
	; memberchk_eq(ID,IDs2) ->
		true
	;
		format('CHR compiler ERROR: invalid identifier ~w in pragma passive in ~@.\n',
                       [ID,format_rule(PragmaRule,N)]),
		fail
	).

check_pragma(Pragma, PragmaRule, N) :-
	Pragma = unique(_,_),
	!,
	format('CHR compiler WARNING: undocumented pragma ~w in ~@.\n',[Pragma,format_rule(PragmaRule,N)]),
	format('    `--> Only use this pragma if you know what you are doing.\n',[]).

check_pragma(Pragma, PragmaRule, N) :-
	Pragma = already_in_heads,
	!,
	format('CHR compiler WARNING: currently unsupported pragma ~w in ~@.\n',[Pragma,format_rule(PragmaRule,N)]),
	format('    `--> Pragma is ignored. Termination and correctness may be affected \n',[]).

check_pragma(Pragma, PragmaRule, N) :-
	Pragma = already_in_head(_),
	!,
	format('CHR compiler WARNING: currently unsupported pragma ~w in ~@.\n',[Pragma,format_rule(PragmaRule,N)]),
	format('    `--> Pragma is ignored. Termination and correctness may be affected \n',[]).
	
check_pragma(Pragma,PragmaRule,N) :-
	format('CHR compiler ERROR: invalid pragma ~w in ~@.\n',[Pragma,format_rule(PragmaRule,N)]),
	format('    `--> Pragma should be one of passive/1!\n',[]),
	fail.

format_rule(PragmaRule,N) :-
	PragmaRule = pragma(_,_,_,MaybeName),
	( MaybeName = yes(Name) ->
		write('rule '), write(Name)
	;
		write('rule number '), write(N)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Global Options
%

handle_option(Var,Value) :- 
	var(Var), !,
	format('CHR compiler ERROR: ~w.\n',[option(Var,Value)]),
	format('    `--> First argument should be an atom, not a variable.\n',[]),
	fail.

handle_option(Name,Value) :- 
	var(Value), !,
	format('CHR compiler ERROR: ~w.\n',[option(Name,Value)]),
	format('    `--> Second argument should be a nonvariable.\n',[]),
	fail.

handle_option(Name,Value) :-
	option_definition(Name,Value,Flags),
	!,
	set_chr_pp_flags(Flags).

handle_option(Name,Value) :- 
	\+ option_definition(Name,_,_), !,
	setof(N,_V ^ _F ^ (option_definition(N,_V,_F)),Ns),
	format('CHR compiler ERROR: ~w.\n',[option(Name,Value)]),
	format('    `--> Invalid option name ~w: should be one of ~w.\n',[Name,Ns]),
	fail.

handle_option(Name,Value) :- 
	findall(V,option_definition(Name,V,_),Vs), 
	format('CHR compiler ERROR: ~w.\n',[option(Name,Value)]),
	format('    `--> Invalid value ~w: should be one of ~w.\n',[Value,Vs]),
	fail.

option_definition(optimize,full,Flags) :-
	Flags = [ unique_analyse_optimise  - on,
                  check_unnecessary_active - full,
		  reorder_heads		   - on,
		  set_semantics_rule	   - on,
		  guard_via_reschedule     - on
		].

option_definition(optimize,sicstus,Flags) :-
	Flags = [ unique_analyse_optimise  - off,
                  check_unnecessary_active - simplification,
		  reorder_heads		   - off,
		  set_semantics_rule	   - off,
		  guard_via_reschedule     - off
		].

option_definition(optimize,off,Flags) :-
	Flags = [ unique_analyse_optimise  - off,
                  check_unnecessary_active - off,
		  reorder_heads		   - off,
		  set_semantics_rule	   - off,
		  guard_via_reschedule     - off
		].

option_definition(check_guard_bindings,on,Flags) :-
	Flags = [ guard_locks - on ].

option_definition(check_guard_bindings,off,Flags) :-
	Flags = [ guard_locks - off ].

init_chr_pp_flags :-
	chr_pp_flag_definition(Name,[DefaultValue|_]),
	set_chr_pp_flag(Name,DefaultValue),
	fail.
init_chr_pp_flags.		

set_chr_pp_flags([]).
set_chr_pp_flags([Name-Value|Flags]) :-
	set_chr_pp_flag(Name,Value),
	set_chr_pp_flags(Flags).

set_chr_pp_flag(Name,Value) :-
	atom_concat('$chr_pp_',Name,GlobalVar),
	nb_setval(GlobalVar,Value).

chr_pp_flag_definition(unique_analyse_optimise,[on,off]).
chr_pp_flag_definition(check_unnecessary_active,[full,simplification,off]).
chr_pp_flag_definition(reorder_heads,[on,off]).
chr_pp_flag_definition(set_semantics_rule,[on,off]).
chr_pp_flag_definition(guard_via_reschedule,[on,off]).
chr_pp_flag_definition(guard_locks,[on,off]).

chr_pp_flag(Name,Value) :-
	atom_concat('$chr_pp_',Name,GlobalVar),
	nb_getval(GlobalVar,V),
	( V == [] ->
		chr_pp_flag_definition(Name,[Value|_])
	;
		V = Value
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Generated predicates
%%	attach_$CONSTRAINT
%%	attach_increment
%%	detach_$CONSTRAINT
%%	attr_unify_hook

%%	attach_$CONSTRAINT
generate_attach_a_constraint_all(Constraints,Mod,Clauses) :-
	length(Constraints,Total),
	generate_attach_a_constraint_all(Constraints,1,Total,Mod,Clauses).
	
generate_attach_a_constraint_all([],_,_,_,[]).
generate_attach_a_constraint_all([Constraint|Constraints],Position,Total,Mod,Clauses) :-
	generate_attach_a_constraint(Total,Position,Constraint,Mod,Clauses1),
	NextPosition is Position + 1,
	generate_attach_a_constraint_all(Constraints,NextPosition,Total,Mod,Clauses2),
	append(Clauses1,Clauses2,Clauses).

generate_attach_a_constraint(Total,Position,Constraint,Mod,[Clause1,Clause2]) :-
	generate_attach_a_constraint_empty_list(Constraint,Clause1),
	( Total == 1 ->
		generate_attach_a_constraint_1_1(Constraint,Mod,Clause2)
	;
		generate_attach_a_constraint_t_p(Total,Position,Constraint,Mod,Clause2)
	).

generate_attach_a_constraint_empty_list(CFct / CAty,Clause) :-
	atom_concat_list(['attach_',CFct, (/) ,CAty],Fct),
	Args = [[],_],
	Head =.. [Fct | Args],
	Clause = ( Head :- true).

generate_attach_a_constraint_1_1(CFct / CAty,Mod,Clause) :-
	atom_concat_list(['attach_',CFct, (/) ,CAty],Fct),
	Args = [[Var|Vars],Susp],
	Head =.. [Fct | Args],
	RecursiveCall =.. [Fct,Vars,Susp],
	Body =
	(
		(   get_attr(Var, Mod, Susps) ->
	            NewSusps=[Susp|Susps],
	            put_attr(Var, Mod, NewSusps)
	        ;   
	            put_attr(Var, Mod, [Susp])
        	),
		RecursiveCall
	),
	Clause = (Head :- Body).

generate_attach_a_constraint_t_p(Total,Position,CFct / CAty ,Mod,Clause) :-
	atom_concat_list(['attach_',CFct, (/) ,CAty],Fct),
	Args = [[Var|Vars],Susp],
	Head =.. [Fct | Args],
	RecursiveCall =.. [Fct,Vars,Susp],
	or_pattern(Position,Pattern),
	make_attr(Total,Mask,SuspsList,Attr),
	nth1(Position,SuspsList,Susps),
	substitute_eq(Susps,SuspsList,[Susp|Susps],SuspsList1),
	make_attr(Total,Mask,SuspsList1,NewAttr1),
	substitute_eq(Susps,SuspsList,[Susp],SuspsList2),
	make_attr(Total,NewMask,SuspsList2,NewAttr2),
	copy_term_nat(SuspsList,SuspsList3),
	nth1(Position,SuspsList3,[Susp]),
	chr_delete(SuspsList3,[Susp],RestSuspsList),
	set_elems(RestSuspsList,[]),
	make_attr(Total,Pattern,SuspsList3,NewAttr3),
	Body =
	(
		( get_attr(Var,Mod,TAttr) ->
			TAttr = Attr,
			( Mask /\ Pattern =:= Pattern ->
				put_attr(Var, Mod, NewAttr1)
			;
				NewMask is Mask \/ Pattern,
				put_attr(Var, Mod, NewAttr2)
			)
		;
			put_attr(Var,Mod,NewAttr3)
		),
		RecursiveCall
	),
	Clause = (Head :- Body).

%%	detach_$CONSTRAINT
generate_detach_a_constraint_all(Constraints,Mod,Clauses) :-
	length(Constraints,Total),
	generate_detach_a_constraint_all(Constraints,1,Total,Mod,Clauses).
	
generate_detach_a_constraint_all([],_,_,_,[]).
generate_detach_a_constraint_all([Constraint|Constraints],Position,Total,Mod,Clauses) :-
	generate_detach_a_constraint(Total,Position,Constraint,Mod,Clauses1),
	NextPosition is Position + 1,
	generate_detach_a_constraint_all(Constraints,NextPosition,Total,Mod,Clauses2),
	append(Clauses1,Clauses2,Clauses).

generate_detach_a_constraint(Total,Position,Constraint,Mod,[Clause1,Clause2]) :-
	generate_detach_a_constraint_empty_list(Constraint,Clause1),
	( Total == 1 ->
		generate_detach_a_constraint_1_1(Constraint,Mod,Clause2)
	;
		generate_detach_a_constraint_t_p(Total,Position,Constraint,Mod,Clause2)
	).

generate_detach_a_constraint_empty_list(CFct / CAty,Clause) :-
	atom_concat_list(['detach_',CFct, (/) ,CAty],Fct),
	Args = [[],_],
	Head =.. [Fct | Args],
	Clause = ( Head :- true).

generate_detach_a_constraint_1_1(CFct / CAty,Mod,Clause) :-
	atom_concat_list(['detach_',CFct, (/) ,CAty],Fct),
	Args = [[Var|Vars],Susp],
	Head =.. [Fct | Args],
	RecursiveCall =.. [Fct,Vars,Susp],
	Body =
	(
		( get_attr(Var,Mod,Susps) ->
			'chr sbag_del_element'(Susps,Susp,NewSusps),
			( NewSusps == [] ->
				del_attr(Var,Mod)
			;
				put_attr(Var,Mod,NewSusps)
			)
		;
			true
		),
		RecursiveCall
	),
	Clause = (Head :- Body).

generate_detach_a_constraint_t_p(Total,Position,CFct / CAty ,Mod,Clause) :-
	atom_concat_list(['detach_',CFct, (/) ,CAty],Fct),
	Args = [[Var|Vars],Susp],
	Head =.. [Fct | Args],
	RecursiveCall =.. [Fct,Vars,Susp],
	or_pattern(Position,Pattern),
	and_pattern(Position,DelPattern),
	make_attr(Total,Mask,SuspsList,Attr),
	nth1(Position,SuspsList,Susps),
	substitute_eq(Susps,SuspsList,[],SuspsList1),
	make_attr(Total,NewMask,SuspsList1,Attr1),
	substitute_eq(Susps,SuspsList,NewSusps,SuspsList2),
	make_attr(Total,Mask,SuspsList2,Attr2),
	Body =
	(
		( get_attr(Var,Mod,TAttr) ->
			TAttr = Attr,
			( Mask /\ Pattern =:= Pattern ->
				'chr sbag_del_element'(Susps,Susp,NewSusps),
				( NewSusps == [] ->
					NewMask is Mask /\ DelPattern,
					( NewMask == 0 ->
						del_attr(Var,Mod)
					;
						put_attr(Var,Mod,Attr1)
					)
				;
					put_attr(Var,Mod,Attr2)
				)
			;
				true
			)
		;
			true
		),
		RecursiveCall
	),
	Clause = (Head :- Body).

%%	detach_$CONSTRAINT
generate_attach_increment(Constraints,Mod,[Clause1,Clause2]) :-
	generate_attach_increment_empty(Clause1),
	length(Constraints,N),
	( N == 1 ->
		generate_attach_increment_one(Mod,Clause2)
	;
		generate_attach_increment_many(N,Mod,Clause2)
	).

generate_attach_increment_empty((attach_increment([],_) :- true)).

generate_attach_increment_one(Mod,Clause) :-
	Head = attach_increment([Var|Vars],Susps),
	Body =
	(
		'chr not_locked'(Var),
		( get_attr(Var,Mod,VarSusps) ->
			sort(VarSusps,SortedVarSusps),
			merge(Susps,SortedVarSusps,MergedSusps),
			put_attr(Var,Mod,MergedSusps)
		;
			put_attr(Var,Mod,Susps)
		),
		attach_increment(Vars,Susps)
	), 
	Clause = (Head :- Body).

generate_attach_increment_many(N,Mod,Clause) :-
	make_attr(N,Mask,SuspsList,Attr),
	make_attr(N,OtherMask,OtherSuspsList,OtherAttr),
	Head = attach_increment([Var|Vars],Attr),
	bagof(G,X ^ Y ^ SY ^ M ^ (member2(SuspsList,OtherSuspsList,X-Y),G = (sort(Y,SY),'chr merge_attributes'(X,SY,M))),Gs),
	list2conj(Gs,SortGoals),
	bagof(MS,A ^ B ^ C ^ member((A,'chr merge_attributes'(B,C,MS)),Gs), MergedSuspsList),
	make_attr(N,MergedMask,MergedSuspsList,NewAttr),
	Body =	
	(
		'chr not_locked'(Var),
		( get_attr(Var,Mod,TOtherAttr) ->
			TOtherAttr = OtherAttr,
			SortGoals,
			MergedMask is Mask \/ OtherMask,
			put_attr(Var,Mod,NewAttr)
		;
			put_attr(Var,Mod,Attr)
		),
		attach_increment(Vars,Attr)
	),
	Clause = (Head :- Body).

%%	attr_unify_hook
generate_attr_unify_hook(Constraints,Mod,[Clause]) :-
	length(Constraints,N),
	( N == 1 ->
		generate_attr_unify_hook_one(Mod,Clause)
	;
		generate_attr_unify_hook_many(N,Mod,Clause)
	).

generate_attr_unify_hook_one(Mod,Clause) :-
	Head = attr_unify_hook(Susps,Other),
	Body = 
	(
		sort(Susps, SortedSusps),
		( var(Other) ->
			( get_attr(Other,Mod,OtherSusps) ->
				true
			;
		        	OtherSusps = []
			),
			sort(OtherSusps,SortedOtherSusps),
			'chr merge_attributes'(SortedSusps,SortedOtherSusps,NewSusps),
			put_attr(Other,Mod,NewSusps),
			'chr run_suspensions'(NewSusps)
		;
			( compound(Other) ->
				term_variables(Other,OtherVars),
				attach_increment(OtherVars, SortedSusps)
			;
				true
			),
			'chr run_suspensions'(Susps)
		)
	),
	Clause = (Head :- Body).

generate_attr_unify_hook_many(N,Mod,Clause) :-
	make_attr(N,Mask,SuspsList,Attr),
	make_attr(N,OtherMask,OtherSuspsList,OtherAttr),
	bagof(Sort,A ^ B ^ ( member(A,SuspsList) , Sort = sort(A,B) ) , SortGoalList),
	list2conj(SortGoalList,SortGoals),
	bagof(B, A ^ member(sort(A,B),SortGoalList), SortedSuspsList),
	bagof(C, D ^ E ^ F ^ G ^ (member2(SortedSuspsList,OtherSuspsList,D-E),
                                  C = (sort(E,F),
                                       'chr merge_attributes'(D,F,G)) ),
              SortMergeGoalList),
	bagof(G, D ^ F ^ H ^ member((H,'chr merge_attributes'(D,F,G)),SortMergeGoalList) , MergedSuspsList),
	list2conj(SortMergeGoalList,SortMergeGoals),
	make_attr(N,MergedMask,MergedSuspsList,MergedAttr),
	make_attr(N,Mask,SortedSuspsList,SortedAttr),
	Head = attr_unify_hook(Attr,Other),
	Body =
	(
		SortGoals,
		( var(Other) ->
			( get_attr(Other,Mod,TOtherAttr) ->
				TOtherAttr = OtherAttr,
				SortMergeGoals,
				MergedMask is Mask \/ OtherMask,
				put_attr(Other,Mod,MergedAttr),
				'chr run_suspensions_loop'(MergedSuspsList)
			;
				put_attr(Other,Mod,SortedAttr),
				'chr run_suspensions_loop'(SortedSuspsList)
			)
		;
			( compound(Other) ->
				term_variables(Other,OtherVars),
				attach_increment(OtherVars,SortedAttr)
			;
				true
			),
			'chr run_suspensions_loop'(SortedSuspsList)
		)	
	),	
	Clause = (Head :- Body).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____        _         ____                      _ _       _   _
%% |  _ \ _   _| | ___   / ___|___  _ __ ___  _ __ (_) | __ _| |_(_) ___  _ __
%% | |_) | | | | |/ _ \ | |   / _ \| '_ ` _ \| '_ \| | |/ _` | __| |/ _ \| '_ \
%% |  _ <| |_| | |  __/ | |__| (_) | | | | | | |_) | | | (_| | |_| | (_) | | | |
%% |_| \_\\__,_|_|\___|  \____\___/|_| |_| |_| .__/|_|_|\__,_|\__|_|\___/|_| |_|
%%                                           |_|

constraints_code(Constraints,Rules,Mod,Clauses) :-
	constraints_code(Constraints,Rules,Mod,L,[]),
	clean_clauses(L,Clauses).

%%	Generate code for all the CHR constraints
constraints_code(Constraints,Rules,Mod,L,T) :-
	length(Constraints,N),
	constraints_code(Constraints,1,N,Constraints,Rules,Mod,L,T).

constraints_code([],_,_,_,_,_,L,L).
constraints_code([Constr|Constrs],I,N,Constraints,Rules,Mod,L,T) :-
	constraint_code(Constr,I,N,Constraints,Rules,Mod,L,T1),
	J is I + 1,
	constraints_code(Constrs,J,N,Constraints,Rules,Mod,T1,T).

%% 	Generate code for a single CHR constraint
constraint_code(Constraint, I, N, Constraints, Rules, Mod, L, T) :-
	constraint_prelude(Constraint,Mod,Clause),
	L = [Clause | L1],
	Id1 = [0],
	rules_code(Rules,1,Constraint,I,N,Constraints,Mod,Id1,Id2,L1,L2),
	gen_cond_attach_clause(Mod,Constraint,I,N,Constraints,Id2,L2,T).

%%	Generate prelude predicate for a constraint.
%%	f(...) :- f/a_0(...,Susp).
constraint_prelude(F/A, _Mod, Clause) :-
	vars_susp(A,Vars,_Susp,VarsSusp),
	Head =.. [ F | Vars],
	build_head(F,A,[0],VarsSusp,Delegate),
	Clause = ( Head  :- Delegate ). 

gen_cond_attach_clause(Mod,F/A,_I,_N,_Constraints,Id,L,T) :-
	( Id == [0] ->
		gen_cond_attach_goal(Mod,F/A,Body,AllArgs)
	; 	vars_susp(A,_Args,Susp,AllArgs),
		gen_uncond_attach_goal(F/A,Susp,Mod,Body,_)
	),
	build_head(F,A,Id,AllArgs,Head),
	Clause = ( Head :- Body ),
	L = [Clause | T].

gen_cond_attach_goal(Mod,F/A,Goal,AllArgs) :-
	vars_susp(A,Args,Susp,AllArgs),
	build_head(F,A,[0],AllArgs,Closure),
	atom_concat_list(['attach_',F, (/) ,A],AttachF),
	Attach =.. [AttachF,Vars,Susp],
	Goal =
	(
		( var(Susp) ->
			'chr insert_constraint_internal'(Vars,Susp,Mod:Closure,F,Args)
		; 
			'chr activate_constraint'(Vars,Susp,_)
		),
		Attach
	).

gen_uncond_attach_goal(F/A,Susp,_Mod,AttachGoal,Generation) :-
	atom_concat_list(['attach_',F, (/) ,A],AttachF),
	Attach =.. [AttachF,Vars,Susp],
	AttachGoal =
	(
		'chr activate_constraint'(Vars, Susp, Generation),
		Attach	
	).

%%	Generate all the code for a constraint based on all CHR rules
rules_code([],_,_,_,_,_,_,Id,Id,L,L).
rules_code([R |Rs],RuleNb,FA,I,N,Constraints,Mod,Id1,Id3,L,T) :-
	rule_code(R,RuleNb,FA,I,N,Constraints,Mod,Id1,Id2,L,T1),
	NextRuleNb is RuleNb + 1,
	rules_code(Rs,NextRuleNb,FA,I,N,Constraints,Mod,Id2,Id3,T1,T).

%%	Generate code for a constraint based on a single CHR rule
rule_code(PragmaRule,RuleNb,FA,I,N,Constraints,Mod,Id1,Id2,L,T) :-
	PragmaRule = pragma(Rule,HeadIDs,_Pragmas,_Name),
	HeadIDs = ids(Head1IDs,Head2IDs),
	Rule = rule(Head1,Head2,_,_),
	heads1_code(Head1,[],Head1IDs,[],PragmaRule,FA,I,N,Constraints,Mod,Id1,L,L1),
	heads2_code(Head2,[],Head2IDs,[],PragmaRule,RuleNb,FA,I,N,Constraints,Mod,Id1,Id2,L1,T).

%%	Generate code based on all the removed heads of a CHR rule
heads1_code([],_,_,_,_,_,_,_,_,_,_,L,L).
heads1_code([Head|Heads],RestHeads,[HeadID|HeadIDs],RestIDs,PragmaRule,F/A,I,N,Constraints,Mod,Id,L,T) :-
	PragmaRule = pragma(Rule,_,Pragmas,_Name),
	( functor(Head,F,A),
	  \+ check_unnecessary_active(Head,RestHeads,Rule),
	  \+ memberchk_eq(passive(HeadID),Pragmas) ->
		append(Heads,RestHeads,OtherHeads),
		append(HeadIDs,RestIDs,OtherIDs),
		head1_code(Head,OtherHeads,OtherIDs,PragmaRule,F/A,I,N,Constraints,Mod,Id,L,L1)
	;	
		L = L1
	),
	heads1_code(Heads,[Head|RestHeads],HeadIDs,[HeadID|RestIDs],PragmaRule,F/A,I,N,Constraints,Mod,Id,L1,T).

%%	Generate code based on one removed head of a CHR rule
head1_code(Head,OtherHeads,OtherIDs,PragmaRule,FA,I,N,Constraints,Mod,Id,L,T) :-
	PragmaRule = pragma(Rule,_,_,_Name),
	Rule = rule(_,Head2,_,_),
	( Head2 == [] ->
		reorder_heads(Head,OtherHeads,OtherIDs,NOtherHeads,NOtherIDs),
		simplification_code(Head,NOtherHeads,NOtherIDs,PragmaRule,FA,I,N,Constraints,Mod,Id,L,T)
	;
		simpagation_head1_code(Head,OtherHeads,OtherIDs,PragmaRule,FA,I,N,Constraints,Mod,Id,L,T)
	).

%% Generate code based on all the persistent heads of a CHR rule
heads2_code([],_,_,_,_,_,_,_,_,_,_,Id,Id,L,L).
heads2_code([Head|Heads],RestHeads,[HeadID|HeadIDs],RestIDs,PragmaRule,RuleNb,F/A,I,N,Constraints,Mod,Id1,Id3,L,T) :-
	PragmaRule = pragma(Rule,_,Pragmas,_Name),
	( functor(Head,F,A),
	  \+ check_unnecessary_active(Head,RestHeads,Rule),
	  \+ memberchk_eq(passive(HeadID),Pragmas),
	  \+ set_semantics_rule(PragmaRule)  ->
		append(Heads,RestHeads,OtherHeads),
		append(HeadIDs,RestIDs,OtherIDs),
		length(Heads,RestHeadNb),
		head2_code(Head,OtherHeads,OtherIDs,PragmaRule,RuleNb,RestHeadNb,F/A,I,N,Constraints,Mod,Id1,L,L0),
		inc_id(Id1,Id2),
		gen_alloc_inc_clause(F/A,Mod,Id1,L0,L1)
	;
		L = L1,
		Id2 = Id1
	),
	heads2_code(Heads,[Head|RestHeads],HeadIDs,[HeadID|RestIDs],PragmaRule,RuleNb,F/A,I,N,Constraints,Mod,Id2,Id3,L1,T).

%% Generate code based on one persistent head of a CHR rule
head2_code(Head,OtherHeads,OtherIDs,PragmaRule,RuleNb,RestHeadNb,FA,I,N,Constraints,Mod,Id,L,T) :-
	PragmaRule = pragma(Rule,_,_,_Name),
	Rule = rule(Head1,_,_,_),
	( Head1 == [] ->
		reorder_heads(Head,OtherHeads,NOtherHeads),
		propagation_code(Head,NOtherHeads,Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,Id,L,T)
	;
		simpagation_head2_code(Head,OtherHeads,OtherIDs,PragmaRule,FA,I,N,Constraints,Mod,Id,L,T) 
	).

gen_alloc_inc_clause(F/A,Mod,Id,L,T) :-
	vars_susp(A,Vars,Susp,VarsSusp),
	build_head(F,A,Id,VarsSusp,Head),
	inc_id(Id,IncId),
	build_head(F,A,IncId,VarsSusp,CallHead),
	( Id == [0] ->
		gen_cond_allocation(Vars,Susp,F/A,VarsSusp,Mod,ConditionalAlloc)
	;
		ConditionalAlloc = true
	), 
	Clause =
	(
		Head :-
			ConditionalAlloc,
			CallHead
	),
	L = [Clause|T].

gen_cond_allocation(Vars,Susp,F/A,VarsSusp,Mod,ConstraintAllocationGoal) :-
	build_head(F,A,[0],VarsSusp,Term),
	ConstraintAllocationGoal =
	( var(Susp) ->
		'chr allocate_constraint'(Mod : Term, Susp, F, Vars)
	;  
		true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

guard_via_reschedule(Retrievals,GuardList,Prelude,Goal) :-
	( chr_pp_flag(guard_via_reschedule,on) ->
		guard_via_reschedule_main(Retrievals,GuardList,Prelude,Goal)
	;
		append(Retrievals,GuardList,GoalList),
		list2conj(GoalList,Goal)
	).

guard_via_reschedule_main(Retrievals,GuardList,Prelude,Goal) :-
	initialize_unit_dictionary(Prelude,Dict),
	build_units(Retrievals,GuardList,Dict,Units),
	dependency_reorder(Units,NUnits),
	units2goal(NUnits,Goal).

units2goal([],true).
units2goal([unit(_,Goal,_,_)|Units],(Goal,Goals)) :-
	units2goal(Units,Goals).

dependency_reorder(Units,NUnits) :-
	dependency_reorder(Units,[],NUnits).

dependency_reorder([],Acc,Result) :-
	reverse(Acc,Result).

dependency_reorder([Unit|Units],Acc,Result) :-
	Unit = unit(_GID,_Goal,Type,GIDs),
	( Type == fixed ->
		NAcc = [Unit|Acc]
	;
		dependency_insert(Acc,Unit,GIDs,NAcc)
	),
	dependency_reorder(Units,NAcc,Result).

dependency_insert([],Unit,_,[Unit]).
dependency_insert([X|Xs],Unit,GIDs,L) :-
	X = unit(GID,_,_,_),
	( memberchk(GID,GIDs) ->
		L = [Unit,X|Xs]
	;
		L = [X | T],
		dependency_insert(Xs,Unit,GIDs,T)
	).

build_units(Retrievals,Guard,InitialDict,Units) :-
	build_retrieval_units(Retrievals,1,N,InitialDict,Dict,Units,Tail),
	build_guard_units(Guard,N,Dict,Tail).

build_retrieval_units([],N,N,Dict,Dict,L,L).
build_retrieval_units([U|Us],N,M,Dict,NDict,L,T) :-
	term_variables(U,Vs),
	update_unit_dictionary(Vs,N,Dict,Dict1,[],GIDs),
	L = [unit(N,U,movable,GIDs)|L1],
	N1 is N + 1,
	build_retrieval_units2(Us,N1,M,Dict1,NDict,L1,T).

build_retrieval_units2([],N,N,Dict,Dict,L,L).
build_retrieval_units2([U|Us],N,M,Dict,NDict,L,T) :-
	term_variables(U,Vs),
	update_unit_dictionary(Vs,N,Dict,Dict1,[],GIDs),
	L = [unit(N,U,fixed,GIDs)|L1],
	N1 is N + 1,
	build_retrieval_units(Us,N1,M,Dict1,NDict,L1,T).

initialize_unit_dictionary(Term,Dict) :-
	term_variables(Term,Vars),
	pair_all_with(Vars,0,Dict).	

update_unit_dictionary([],_,Dict,Dict,GIDs,GIDs).
update_unit_dictionary([V|Vs],This,Dict,NDict,GIDs,NGIDs) :-
	( lookup_eq(Dict,V,GID) ->
		( (GID == This ; memberchk(GID,GIDs) ) ->
			GIDs1 = GIDs
		;
			GIDs1 = [GID|GIDs]
		),
		Dict1 = Dict
	;
		Dict1 = [V - This|Dict],
		GIDs1 = GIDs
	),
	update_unit_dictionary(Vs,This,Dict1,NDict,GIDs1,NGIDs).

build_guard_units(Guard,N,Dict,Units) :-
	( Guard = [Goal] ->
		Units = [unit(N,Goal,fixed,[])]
	; Guard = [Goal|Goals] ->
		term_variables(Goal,Vs),
		update_unit_dictionary2(Vs,N,Dict,NDict,[],GIDs),
		Units = [unit(N,Goal,movable,GIDs)|RUnits],
		N1 is N + 1,
		build_guard_units(Goals,N1,NDict,RUnits)
	).

update_unit_dictionary2([],_,Dict,Dict,GIDs,GIDs).
update_unit_dictionary2([V|Vs],This,Dict,NDict,GIDs,NGIDs) :-
	( lookup_eq(Dict,V,GID) ->
		( (GID == This ; memberchk(GID,GIDs) ) ->
			GIDs1 = GIDs
		;
			GIDs1 = [GID|GIDs]
		),
		Dict1 = [V - This|Dict]
	;
		Dict1 = [V - This|Dict],
		GIDs1 = GIDs
	),
	update_unit_dictionary2(Vs,This,Dict1,NDict,GIDs1,NGIDs).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____       _     ____                             _   _            
%% / ___|  ___| |_  / ___|  ___ _ __ ___   __ _ _ __ | |_(_) ___ ___ _ 
%% \___ \ / _ \ __| \___ \ / _ \ '_ ` _ \ / _` | '_ \| __| |/ __/ __(_)
%%  ___) |  __/ |_   ___) |  __/ | | | | | (_| | | | | |_| | (__\__ \_ 
%% |____/ \___|\__| |____/ \___|_| |_| |_|\__,_|_| |_|\__|_|\___|___(_)
%%                                                                     
%%  _   _       _                    ___        __                              
%% | | | |_ __ (_) __ _ _   _  ___  |_ _|_ __  / _| ___ _ __ ___ _ __   ___ ___ 
%% | | | | '_ \| |/ _` | | | |/ _ \  | || '_ \| |_ / _ \ '__/ _ \ '_ \ / __/ _ \
%% | |_| | | | | | (_| | |_| |  __/  | || | | |  _|  __/ | |  __/ | | | (_|  __/
%%  \___/|_| |_|_|\__, |\__,_|\___| |___|_| |_|_|  \___|_|  \___|_| |_|\___\___|
%%                   |_|                                                        
unique_analyse_optimise(Rules,N,PatternList,NRules) :-
		( chr_pp_flag(unique_analyse_optimise,on) ->
			unique_analyse_optimise_main(Rules,N,PatternList,NRules)
		;
			NRules = Rules
		).

unique_analyse_optimise_main([],_,_,[]).
unique_analyse_optimise_main([PRule|PRules],N,PatternList,[NPRule|NPRules]) :-
	( discover_unique_pattern(PRule,N,Pattern) ->
		NPatternList = [Pattern|PatternList]
	;
		NPatternList = PatternList
	),
	PRule = pragma(Rule,Ids,Pragmas,Name),
	Rule = rule(H1,H2,_,_),
	Ids = ids(Ids1,Ids2),
	apply_unique_patterns_to_constraints(H1,Ids1,NPatternList,MorePragmas1),
	apply_unique_patterns_to_constraints(H2,Ids2,NPatternList,MorePragmas2),
	append([MorePragmas1,MorePragmas2,Pragmas],NPragmas),
	NPRule = pragma(Rule,Ids,NPragmas,Name),
	N1 is N + 1,
	unique_analyse_optimise_main(PRules,N1,NPatternList,NPRules).

apply_unique_patterns_to_constraints([],_,_,[]).
apply_unique_patterns_to_constraints([C|Cs],[Id|Ids],Patterns,Pragmas) :-
	( member(Pattern,Patterns),
	  apply_unique_pattern(C,Id,Pattern,Pragma) ->
		Pragmas = [Pragma | RPragmas]
	;
		Pragmas = RPragmas
	),
	apply_unique_patterns_to_constraints(Cs,Ids,Patterns,RPragmas).

apply_unique_pattern(Constraint,Id,Pattern,Pragma) :-
	Pattern = unique(PatternConstraint,PatternKey),
	subsumes(Constraint,PatternConstraint,Unifier),
	( setof(	V,
			T^Term^Vs^(
				member(T,PatternKey),
				lookup_eq(Unifier,T,Term),
				term_variables(Term,Vs),
				member(V,Vs)
			),
			Vars) ->
		true
	;
		Vars = []
	),
	Pragma = unique(Id,Vars).

%	subsumes(+Term1, +Term2, -Unifier)
%	
%	If Term1 is a more general term   than  Term2 (e.g. has a larger
%	part instantiated), unify  Unifier  with   a  list  Var-Value of
%	variables from Term2 and their corresponding values in Term1.

subsumes(Term1,Term2,Unifier) :-
	empty_ds(S0),
	subsumes_aux(Term1,Term2,S0,S),
	ds_to_list(S,L),
	build_unifier(L,Unifier).

subsumes_aux(Term1, Term2, S0, S) :-
        (   compound(Term2),
            functor(Term2, F, N)
        ->  compound(Term1), functor(Term1, F, N),
            subsumes_aux(N, Term1, Term2, S0, S)
        ;   Term1 == Term2
	->  S = S0
	;   var(Term2),
	    get_ds(Term1,S0,V)
	->  V == Term2, S = S0
	;   var(Term2),
	    put_ds(Term1, S0, Term2, S)
        ).

subsumes_aux(0, _, _, S, S) :- ! .
subsumes_aux(N, T1, T2, S0, S) :-
        arg(N, T1, T1x),
        arg(N, T2, T2x),
        subsumes_aux(T1x, T2x, S0, S1),
        M is N-1,
        subsumes_aux(M, T1, T2, S1, S).

build_unifier([],[]).
build_unifier([X-V|R],[V - X | T]) :-
	build_unifier(R,T).
	
discover_unique_pattern(PragmaRule,RuleNb,Pattern) :-
	PragmaRule = pragma(Rule,_,Pragmas,Name),
	( Rule = rule([C1],[C2],Guard,Body) -> 
		true
	;
		Rule = rule([C1,C2],[],Guard,Body)
	),
	check_unique_constraints(C1,C2,Guard,Body,Pragmas,List),
	term_variables(C1,Vs),
	select_pragma_unique_variables(List,Vs,Key),
	Pattern0 = unique(C1,Key),
	copy_term_nat(Pattern0,Pattern),
	( verbosity_on ->
		format('Found unique pattern ~w in rule ~d~@\n', 
			[Pattern,RuleNb,(Name=yes(N) -> write(": "),write(N) ; true)])
	;
		true
	).
	
select_pragma_unique_variables([],_,[]).
select_pragma_unique_variables([X-Y|R],Vs,L) :-
	( X == Y ->
		L = [X|T]
	;
		once((
			\+ memberchk_eq(X,Vs)
		;
			\+ memberchk_eq(Y,Vs)
		)),
		L = T
	),
	select_pragma_unique_variables(R,Vs,T).

check_unique_constraints(C1,C2,G,_Body,Pragmas,List) :-
	\+ member(passive(_),Pragmas),
	variable_replacement(C1-C2,C2-C1,List),
	copy_with_variable_replacement(G,OtherG,List),
	negate(G,NotG),
	once(entails(NotG,OtherG)).

negate(true,fail).
negate(fail,true).
negate(X =< Y, Y < X).
negate(X > Y, Y >= X).
negate(X >= Y, Y > X).
negate(X < Y, Y =< X).
negate(var(X),nonvar(X)).
negate(nonvar(X),var(X)).

entails(X,X1) :- X1 == X.
entails(fail,_).
entails(X > Y, X1 >= Y1) :- X1 == X, Y1 == Y.
entails(X < Y, X1 =< Y1) :- X1 == X, Y1 == Y.
entails(ground(X),var(X1)) :- X1 == X.

check_unnecessary_active(Constraint,Previous,Rule) :-
	( chr_pp_flag(check_unnecessary_active,full) ->
		check_unnecessary_active_main(Constraint,Previous,Rule)
	; chr_pp_flag(check_unnecessary_active,simplification),
	  Rule = rule(_,[],_,_) ->
		check_unnecessary_active_main(Constraint,Previous,Rule)
	;
		fail
	).

check_unnecessary_active_main(Constraint,Previous,Rule) :-
   member(Other,Previous),
   variable_replacement(Other,Constraint,List),
   copy_with_variable_replacement(Rule,Rule2,List),
   identical_rules(Rule,Rule2), ! .

set_semantics_rule(PragmaRule) :-
	( chr_pp_flag(set_semantics_rule,on) ->
		set_semantics_rule_main(PragmaRule)
	;
		fail
	).

set_semantics_rule_main(PragmaRule) :-
	PragmaRule = pragma(Rule,IDs,Pragmas,_),
	Rule = rule([C1],[C2],true,true),
	C1 == C2,
	IDs = ids([ID1],_),
	\+ memberchk_eq(passive(ID1),Pragmas).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____        _        _____            _            _                     
%% |  _ \ _   _| | ___  | ____|__ _ _   _(_)_   ____ _| | ___ _ __   ___ ___ 
%% | |_) | | | | |/ _ \ |  _| / _` | | | | \ \ / / _` | |/ _ \ '_ \ / __/ _ \
%% |  _ <| |_| | |  __/ | |__| (_| | |_| | |\ V / (_| | |  __/ | | | (_|  __/
%% |_| \_\\__,_|_|\___| |_____\__, |\__,_|_| \_/ \__,_|_|\___|_| |_|\___\___|
%%                               |_|                                         
% have to check for no duplicates in value list

% check wether two rules are identical

identical_rules(rule(H11,H21,G1,B1),rule(H12,H22,G2,B2)) :-
   G1 == G2,
   identical_bodies(B1,B2),
   permutation(H11,P1),
   P1 == H12,
   permutation(H21,P2),
   P2 == H22.

identical_bodies(B1,B2) :-
   ( B1 = (X1 = Y1),
     B2 = (X2 = Y2) ->
     ( X1 == X2,
       Y1 == Y2
     ; X1 == Y2,
       X2 == Y1
     ),
     !
   ; B1 == B2
   ).
 
% replace variables in list
   
copy_with_variable_replacement(X,Y,L) :-
   ( var(X) ->
     ( lookup_eq(L,X,Y) ->
       true
     ; X = Y
     )
   ; functor(X,F,A),
     functor(Y,F,A),
     X =.. [_|XArgs],
     Y =.. [_|YArgs],
     copy_with_variable_replacement_l(XArgs,YArgs,L)
   ).

copy_with_variable_replacement_l([],[],_).
copy_with_variable_replacement_l([X|Xs],[Y|Ys],L) :-
   copy_with_variable_replacement(X,Y,L),
   copy_with_variable_replacement_l(Xs,Ys,L).
   
%% build variable replacement list

variable_replacement(X,Y,L) :-
   variable_replacement(X,Y,[],L).
   
variable_replacement(X,Y,L1,L2) :-
   ( var(X) ->
     var(Y),
     ( lookup_eq(L1,X,Z) ->
       Z == Y,
       L2 = L1
     ; L2 = [X-Y|L1]
     )
   ; X =.. [F|XArgs],
     nonvar(Y),
     Y =.. [F|YArgs],
     variable_replacement_l(XArgs,YArgs,L1,L2)
   ).

variable_replacement_l([],[],L,L).
variable_replacement_l([X|Xs],[Y|Ys],L1,L3) :-
   variable_replacement(X,Y,L1,L2),
   variable_replacement_l(Xs,Ys,L2,L3).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____  _                 _ _  __ _           _   _
%% / ___|(_)_ __ ___  _ __ | (_)/ _(_) ___ __ _| |_(_) ___  _ __
%% \___ \| | '_ ` _ \| '_ \| | | |_| |/ __/ _` | __| |/ _ \| '_ \
%%  ___) | | | | | | | |_) | | |  _| | (_| (_| | |_| | (_) | | | |
%% |____/|_|_| |_| |_| .__/|_|_|_| |_|\___\__,_|\__|_|\___/|_| |_|
%%                   |_| 

simplification_code(Head,RestHeads,RestIDs,PragmaRule,F/A,_I,N,Constraints,Mod,Id,L,T) :-
	PragmaRule = pragma(Rule,_,Pragmas,_),
	head_info(Head,A,_Vars,Susp,HeadVars,HeadPairs),
	build_head(F,A,Id,HeadVars,ClauseHead),
	head_arg_matches(HeadPairs,[],FirstMatching,VarDict1),
	
	(   RestHeads == [] ->
	    Susps = [],
	    VarDict = VarDict1,
	    GetRestHeads = []
	;   
	    rest_heads_retrieval_and_matching(RestHeads,RestIDs,Pragmas,Head,Mod,N,Constraints,GetRestHeads,Susps,VarDict1,VarDict)
	),
	
	guard_body_copies2(Rule,VarDict,GuardCopyList,BodyCopy),
	guard_via_reschedule(GetRestHeads,GuardCopyList,ClauseHead-FirstMatching,RescheduledTest),
	
	gen_uncond_susps_detachments(Susps,RestHeads,SuspsDetachments),
	gen_cond_susp_detachment(Susp,F/A,SuspDetachment),
	
	Clause = ( ClauseHead :-
	     	FirstMatching, 
		     RescheduledTest,
	             !,
	             SuspsDetachments,
	             SuspDetachment,
	             BodyCopy
	         ),
	L = [Clause | T].

head_arg_matches(Pairs,VarDict,Goal,NVarDict) :-
	head_arg_matches_(Pairs,VarDict,GoalList,NVarDict),
	list2conj(GoalList,Goal).
 
head_arg_matches_([],VarDict,[],VarDict).
head_arg_matches_([Arg-Var| Rest],VarDict,GoalList,NVarDict) :-
   (   var(Arg) ->
       (   lookup_eq(VarDict,Arg,OtherVar) ->
           GoalList = [Var == OtherVar | RestGoalList],
           VarDict1 = VarDict
       ;   VarDict1 = [Arg-Var | VarDict],
           GoalList = RestGoalList
       ),
       Pairs = Rest
   ;   atomic(Arg) ->
       GoalList = [ Var == Arg | RestGoalList],
       VarDict = VarDict1,
       Pairs = Rest
   ;   Arg =.. [_|Args],
       functor(Arg,Fct,N),
       functor(Term,Fct,N),
       Term =.. [_|Vars],
       GoalList =[ nonvar(Var), Var = Term | RestGoalList ], 
       pairup(Args,Vars,NewPairs),
       append(NewPairs,Rest,Pairs),
       VarDict1 = VarDict
   ),
   head_arg_matches_(Pairs,VarDict1,RestGoalList,NVarDict).

rest_heads_retrieval_and_matching(Heads,IDs,Pragmas,ActiveHead,Mod,N,Constraints,GoalList,Susps,VarDict,NVarDict):-
	rest_heads_retrieval_and_matching(Heads,IDs,Pragmas,ActiveHead,Mod,N,Constraints,GoalList,Susps,VarDict,NVarDict,[],[],[]).
	
rest_heads_retrieval_and_matching(Heads,IDs,Pragmas,ActiveHead,Mod,N,Constraints,GoalList,Susps,VarDict,NVarDict,PrevHs,PrevSusps,AttrDict) :-
	( Heads = [_|_] ->
		rest_heads_retrieval_and_matching_n(Heads,IDs,Pragmas,PrevHs,PrevSusps,ActiveHead,Mod,N,Constraints,GoalList,Susps,VarDict,NVarDict,AttrDict)	
	;
		GoalList = [],
		Susps = [],
		VarDict = NVarDict
	).

rest_heads_retrieval_and_matching_n([],_,_,_,_,_,_,N,_,[],[],VarDict,VarDict,AttrDict) :-
	instantiate_pattern_goals(AttrDict,N).
rest_heads_retrieval_and_matching_n([H|Hs],[ID|IDs],Pragmas,PrevHs,PrevSusps,ActiveHead,Mod,N,Constraints,[ViaGoal,Goal|Goals],[Susp|Susps],VarDict,NVarDict,AttrDict) :-
	passive_head_via(H,[ActiveHead|PrevHs],AttrDict,Constraints,Mod,VarDict,ViaGoal,Attr,NewAttrDict),
	functor(H,Fct,Aty),
	head_info(H,Aty,Vars,_,_,Pairs),
	head_arg_matches(Pairs,VarDict,MatchingGoal,VarDict1),
	Suspension =.. [suspension,_,State,_,_,_,_|Vars],
	( N == 1 ->
		VarSusps = Attr
	;
		nth1(Pos,Constraints,Fct/Aty), !,
		make_attr(N,_Mask,SuspsList,Attr),
		nth1(Pos,SuspsList,VarSusps)
	),
	different_from_other_susps(H,Susp,PrevHs,PrevSusps,DiffSuspGoals),
	create_get_mutable_ref(active,State,GetMutable),
	Goal1 = 
	(
		'chr sbag_member'(Susp,VarSusps),
		Susp = Suspension,
		GetMutable,
		DiffSuspGoals,
		MatchingGoal
	),
	( member(unique(ID,UniqueKeus),Pragmas),
	  check_unique_keys(UniqueKeus,VarDict) ->
		Goal = (Goal1 -> true) % once(Goal1)
	;
		Goal = Goal1
	),
	rest_heads_retrieval_and_matching_n(Hs,IDs,Pragmas,[H|PrevHs],[Susp|PrevSusps],ActiveHead,Mod,N,Constraints,Goals,Susps,VarDict1,NVarDict,NewAttrDict).

instantiate_pattern_goals([],_).
instantiate_pattern_goals([_-attr(Attr,Bits,Goal)|Rest],N) :-
	( N == 1 ->
		Goal = true
	;
		make_attr(N,Mask,_,Attr),
		or_list(Bits,Pattern), !,
		Goal = (Mask /\ Pattern =:= Pattern)
	),
	instantiate_pattern_goals(Rest,N).


check_unique_keys([],_).
check_unique_keys([V|Vs],Dict) :-
	lookup_eq(Dict,V,_),
	check_unique_keys(Vs,Dict).

% Generates tests to ensure the found constraint differs from previously found constraints
different_from_other_susps(Head,Susp,Heads,Susps,DiffSuspGoals) :-
	( bagof(DiffSuspGoal, Pos ^ ( nth1(Pos,Heads,PreHead), \+ Head \= PreHead, nth1(Pos,Susps,PreSusp), DiffSuspGoal = (Susp \== PreSusp) ),DiffSuspGoalList) ->
	     list2conj(DiffSuspGoalList,DiffSuspGoals)
	;
	     DiffSuspGoals = true
	).

passive_head_via(Head,PrevHeads,AttrDict,Constraints,Mod,VarDict,Goal,Attr,NewAttrDict) :-
	functor(Head,F,A),
	nth1(Pos,Constraints,F/A),!,
	common_variables(Head,PrevHeads,CommonVars),
	translate(CommonVars,VarDict,Vars),
	or_pattern(Pos,Bit),
	( permutation(Vars,PermutedVars),
	  lookup_eq(AttrDict,PermutedVars,attr(Attr,Positions,_)) ->
		member(Bit,Positions), !,
		NewAttrDict = AttrDict,
		Goal = true
	; 
		Goal = (Goal1, PatternGoal),
		gen_get_mod_constraints(Mod,Vars,Goal1,Attr),
		NewAttrDict = [Vars - attr(Attr,[Bit|_],PatternGoal) | AttrDict]
	).
 
common_variables(T,Ts,Vs) :-
	term_variables(T,V1),
	term_variables(Ts,V2),
	intersect_eq(V1,V2,Vs).

gen_get_mod_constraints(Mod,L,Goal,Susps) :-
   (   L == [] ->
       Goal = 
       (   'chr default_store'(Global),
           get_attr(Global,Mod,TSusps),
	   TSusps = Susps
       )
   ; 
       (    L = [A] ->
            VIA =  'chr via_1'(A,V)
       ;    (   L = [A,B] ->
                VIA = 'chr via_2'(A,B,V)
            ;   VIA = 'chr via'(L,V)
            )
       ),
       Goal =
       (   VIA,
           get_attr(V,Mod,TSusps),
	   TSusps = Susps
       )
   ).

guard_body_copies(Rule,VarDict,GuardCopy,BodyCopy) :-
	guard_body_copies2(Rule,VarDict,GuardCopyList,BodyCopy),
	list2conj(GuardCopyList,GuardCopy).

guard_body_copies2(Rule,VarDict,GuardCopyList,BodyCopy) :-
	Rule = rule(_,_,Guard,Body),
	conj2list(Guard,GuardList),
	split_off_simple_guard(GuardList,VarDict,GuardPrefix,RestGuardList),
	my_term_copy(GuardPrefix-RestGuardList,VarDict,VarDict2,GuardPrefixCopy-RestGuardListCopyCore),

	append(GuardPrefixCopy,[RestGuardCopy],GuardCopyList),
	term_variables(RestGuardList,GuardVars),
	term_variables(RestGuardListCopyCore,GuardCopyVars),
	( chr_pp_flag(guard_locks,on),
          bagof(('chr lock'(Y)) - ('chr unlock'(Y)),
                X ^ (member(X,GuardVars),		% X is a variable appearing in the original guard
                     lookup_eq(VarDict,X,Y),            % translate X into new variable
                     memberchk_eq(Y,GuardCopyVars)      % redundant check? or multiple entries for X possible?
                    ),
                LocksUnlocks) ->
		once(pairup(Locks,Unlocks,LocksUnlocks))
	;
		Locks = [],
		Unlocks = []
	),
	list2conj(Locks,LockPhase),
	list2conj(Unlocks,UnlockPhase),
	list2conj(RestGuardListCopyCore,RestGuardCopyCore),
	RestGuardCopy = (LockPhase,(RestGuardCopyCore,UnlockPhase)),
	my_term_copy(Body,VarDict2,BodyCopy).


split_off_simple_guard([],_,[],[]).
split_off_simple_guard([G|Gs],VarDict,S,C) :-
	( simple_guard(G,VarDict) ->
		S = [G|Ss],
		split_off_simple_guard(Gs,VarDict,Ss,C)
	;
		S = [],
		C = [G|Gs]
	).

% simple guard: cheap and benign (does not bind variables)

simple_guard(var(_),    _).
simple_guard(nonvar(_), _).
simple_guard(ground(_), _).
simple_guard(number(_), _).
simple_guard(atom(_), _).
simple_guard(integer(_), _).
simple_guard(float(_), _).

simple_guard(_ > _ , _).
simple_guard(_ < _ , _).
simple_guard(_ =< _, _).
simple_guard(_ >= _, _).
simple_guard(_ =:= _, _).
simple_guard(_ == _, _).

simple_guard(X is _, VarDict) :-
	\+ lookup_eq(VarDict,X,_).

simple_guard((G1,G2),VarDict) :-
	simple_guard(G1,VarDict),
	simple_guard(G2,VarDict).

simple_guard(\+ G, VarDict) :-
	simple_guard(G, VarDict).

my_term_copy(X,Dict,Y) :-
   my_term_copy(X,Dict,_,Y).

my_term_copy(X,Dict1,Dict2,Y) :-
   (   var(X) ->
       (   lookup_eq(Dict1,X,Y) ->
           Dict2 = Dict1
       ;   Dict2 = [X-Y|Dict1]
       )
   ;   functor(X,XF,XA),
       functor(Y,XF,XA),
       X =.. [_|XArgs],
       Y =.. [_|YArgs],
       my_term_copy_list(XArgs,Dict1,Dict2,YArgs)
   ).

my_term_copy_list([],Dict,Dict,[]).
my_term_copy_list([X|Xs],Dict1,Dict3,[Y|Ys]) :-
   my_term_copy(X,Dict1,Dict2,Y),
   my_term_copy_list(Xs,Dict2,Dict3,Ys).

gen_cond_susp_detachment(Susp,FA,SuspDetachment) :-
   gen_uncond_susp_detachment(Susp,FA,UnCondSuspDetachment),
   SuspDetachment = 
      (   var(Susp) ->
          true
      ;   UnCondSuspDetachment
      ).

gen_uncond_susp_detachment(Susp,CFct/CAty,SuspDetachment) :-
	atom_concat_list(['detach_',CFct, (/) ,CAty],Fct),
	Detach =.. [Fct,Vars,Susp],
	SuspDetachment = 
	(
		'chr remove_constraint_internal'(Susp, Vars),
		Detach
	).

gen_uncond_susps_detachments([],[],true).
gen_uncond_susps_detachments([Susp|Susps],[Term|Terms],(SuspDetachment,SuspsDetachments)) :-
   functor(Term,F,A),
   gen_uncond_susp_detachment(Susp,F/A,SuspDetachment),
   gen_uncond_susps_detachments(Susps,Terms,SuspsDetachments).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____  _                                   _   _               _
%% / ___|(_)_ __ ___  _ __   __ _  __ _  __ _| |_(_) ___  _ __   / |
%% \___ \| | '_ ` _ \| '_ \ / _` |/ _` |/ _` | __| |/ _ \| '_ \  | |
%%  ___) | | | | | | | |_) | (_| | (_| | (_| | |_| | (_) | | | | | |
%% |____/|_|_| |_| |_| .__/ \__,_|\__, |\__,_|\__|_|\___/|_| |_| |_|
%%                   |_|          |___/

simpagation_head1_code(Head,RestHeads,OtherIDs,PragmaRule,F/A,_I,N,Constraints,Mod,Id,L,T) :-
   PragmaRule = pragma(Rule,ids(_,Heads2IDs),Pragmas,_Name),
   Rule = rule(_Heads,Heads2,_Guard,_Body),

   head_info(Head,A,_Vars,Susp,HeadVars,HeadPairs),
   head_arg_matches(HeadPairs,[],FirstMatching,VarDict1),

   build_head(F,A,Id,HeadVars,ClauseHead),

   append(RestHeads,Heads2,Heads),
   append(OtherIDs,Heads2IDs,IDs),
   reorder_heads(Head,Heads,IDs,NHeads,NIDs),
   rest_heads_retrieval_and_matching(NHeads,NIDs,Pragmas,Head,Mod,N,Constraints,GetRestHeads,Susps,VarDict1,VarDict),
   length(RestHeads,RN),
   take(RN,Susps,Susps1),

   guard_body_copies2(Rule,VarDict,GuardCopyList,BodyCopy),
   guard_via_reschedule(GetRestHeads,GuardCopyList,ClauseHead-FirstMatching,RescheduledTest),

   gen_uncond_susps_detachments(Susps1,RestHeads,SuspsDetachments),
   gen_cond_susp_detachment(Susp,F/A,SuspDetachment),
   
   Clause = ( ClauseHead :-
		FirstMatching, 
		RescheduledTest,
                !,
                SuspsDetachments,
                SuspDetachment,
                BodyCopy
            ),
   L = [Clause | T].
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____  _                                   _   _               ____
%% / ___|(_)_ __ ___  _ __   __ _  __ _  __ _| |_(_) ___  _ __   |___ \
%% \___ \| | '_ ` _ \| '_ \ / _` |/ _` |/ _` | __| |/ _ \| '_ \    __) |
%%  ___) | | | | | | | |_) | (_| | (_| | (_| | |_| | (_) | | | |  / __/
%% |____/|_|_| |_| |_| .__/ \__,_|\__, |\__,_|\__|_|\___/|_| |_| |_____|
%%                   |_|          |___/

%% Genereate prelude + worker predicate
%% prelude calls worker
%% worker iterates over one type of removed constraints
simpagation_head2_code(Head2,RestHeads2,RestIDs,PragmaRule,FA,I,N,Constraints,Mod,Id,L,T) :-
   PragmaRule = pragma(Rule,ids(IDs1,_),Pragmas,_Name),
   Rule = rule(Heads1,_,Guard,Body),
   reorder_heads(Head2,Heads1,IDs1,[Head1|RestHeads1],[ID1|RestIDs1]),   	% Heads1 = [Head1|RestHeads1],
										% IDs1 = [ID1|RestIDs1],
   simpagation_head2_prelude(Head2,Head1,[RestHeads2,Heads1,Guard,Body],FA,I,N,Constraints,Mod,Id,L,L1),
   extend_id(Id,Id2), 
   simpagation_head2_worker(Head2,Head1,ID1,RestHeads1,RestIDs1,RestHeads2,RestIDs,Rule,Pragmas,FA,I,N,Constraints,Mod,Id2,L1,T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
simpagation_head2_prelude(Head,Head1,Rest,F/A,_I,N,Constraints,Mod,Id1,L,T) :-
	head_info(Head,A,Vars,Susp,VarsSusp,HeadPairs),
	build_head(F,A,Id1,VarsSusp,ClauseHead),
	head_arg_matches(HeadPairs,[],FirstMatching,VarDict),

	passive_head_via(Head1,[Head],[],Constraints,Mod,VarDict,ModConstraintsGoal,Attr,AttrDict),   
	instantiate_pattern_goals(AttrDict,N),
	( N == 1 ->
		AllSusps = Attr
	;
		functor(Head1,F1,A1),
		nth1(Pos,Constraints,F1/A1), !,
		make_attr(N,_,SuspsList,Attr),
		nth1(Pos,SuspsList,AllSusps)
	),

	(   Id1 == [0] ->	% create suspension
		gen_cond_allocation(Vars,Susp,F/A,VarsSusp,Mod,ConstraintAllocationGoal)
	;	ConstraintAllocationGoal = true
	),

	extend_id(Id1,DelegateId),
	extra_active_delegate_variables(Head,Rest,VarDict,ExtraVars),
	append([AllSusps|VarsSusp],ExtraVars,DelegateCallVars),
	build_head(F,A,DelegateId,DelegateCallVars,Delegate),

	PreludeClause = 
	   ( ClauseHead :-
	          FirstMatching,
	          ModConstraintsGoal,
	          !,
	          ConstraintAllocationGoal,
	          Delegate
	   ),
	L = [PreludeClause|T].

extra_active_delegate_variables(Term,Terms,VarDict,Vars) :-
	Term =.. [_|Args],
	delegate_variables(Term,Terms,VarDict,Args,Vars).

passive_delegate_variables(Term,PrevTerms,NextTerms,VarDict,Vars) :-
	term_variables(PrevTerms,PrevVars),
	delegate_variables(Term,NextTerms,VarDict,PrevVars,Vars).

delegate_variables(Term,Terms,VarDict,PrevVars,Vars) :-
	term_variables(Term,V1),
	term_variables(Terms,V2),
	intersect_eq(V1,V2,V3),
	list_difference_eq(V3,PrevVars,V4),
	translate(V4,VarDict,Vars).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
simpagation_head2_worker(Head2,Head1,ID1,RestHeads1,IDs1,RestHeads2,IDs2,Rule,Pragmas,FA,I,N,Constraints,Mod,Id,L,T) :-
   Rule = rule(_,_,Guard,Body),
   simpagation_head2_worker_end(Head2,[Head1,RestHeads1,RestHeads2,Guard,Body],FA,Id,L,L1),
   simpagation_head2_worker_body(Head2,Head1,ID1,RestHeads1,IDs1,RestHeads2,IDs2,Rule,Pragmas,FA,I,N,Constraints,Mod,Id,L1,T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
simpagation_head2_worker_body(Head2,Head1,ID1,RestHeads1,IDs1,RestHeads2,IDs2,Rule,Pragmas,F/A,_I,N,Constraints,Mod,Id,L,T) :-
   gen_var(OtherSusp),
   gen_var(OtherSusps),

   head_info(Head2,A,_Vars,Susp,VarsSusp,Head2Pairs),
   head_arg_matches(Head2Pairs,[],_,VarDict1),

   Rule = rule(_,_,Guard,Body),
   extra_active_delegate_variables(Head2,[Head1,RestHeads1,RestHeads2,Guard,Body],VarDict1,ExtraVars),
   append([[OtherSusp|OtherSusps]|VarsSusp],ExtraVars,HeadVars),
   build_head(F,A,Id,HeadVars,ClauseHead),

   functor(Head1,_OtherF,OtherA),
   head_info(Head1,OtherA,OtherVars,_,_,Head1Pairs),
   head_arg_matches(Head1Pairs,VarDict1,FirstMatching,VarDict2),

   OtherSuspension =.. [suspension,_,OtherState,_,_,_,_|OtherVars],
   create_get_mutable_ref(active,OtherState,GetMutable),
   IteratorSuspTest =
      (   OtherSusp = OtherSuspension,
          GetMutable
      ),

   (   (RestHeads1 \== [] ; RestHeads2 \== []) ->
		append(RestHeads1,RestHeads2,RestHeads),
		append(IDs1,IDs2,IDs),
		reorder_heads(Head1-Head2,RestHeads,IDs,NRestHeads,NIDs),
		rest_heads_retrieval_and_matching(NRestHeads,NIDs,Pragmas,[Head1,Head2],Mod,N,Constraints,RestSuspsRetrieval,Susps,VarDict2,VarDict,[Head1],[OtherSusp],[]),
		length(RestHeads1,RH1N),
		take(RH1N,Susps,Susps1)
   ;   RestSuspsRetrieval = [],
       Susps1 = [],
       VarDict = VarDict2
   ),

   gen_uncond_susps_detachments([OtherSusp | Susps1],[Head1|RestHeads1],Susps1Detachments),

   append([OtherSusps|VarsSusp],ExtraVars,RecursiveVars),
   build_head(F,A,Id,RecursiveVars,RecursiveCall),
   append([[]|VarsSusp],ExtraVars,RecursiveVars2),
   build_head(F,A,Id,RecursiveVars2,RecursiveCall2),

   guard_body_copies2(Rule,VarDict,GuardCopyList,BodyCopy),
   guard_via_reschedule(RestSuspsRetrieval,GuardCopyList,v(ClauseHead,IteratorSuspTest,FirstMatching),RescheduledTest),
   (   BodyCopy \== true ->
       gen_uncond_attach_goal(F/A,Susp,Mod,Attachment,Generation),
       gen_state_cond_call(Susp,A,RecursiveCall,Generation,ConditionalRecursiveCall),
       gen_state_cond_call(Susp,A,RecursiveCall2,Generation,ConditionalRecursiveCall2)
   ;   Attachment = true,
       ConditionalRecursiveCall = RecursiveCall,
       ConditionalRecursiveCall2 = RecursiveCall2
   ),

   ( member(unique(ID1,UniqueKeys), Pragmas),
     check_unique_keys(UniqueKeys,VarDict1) ->
	Clause =
		( ClauseHead :-
			( IteratorSuspTest,
			  FirstMatching ->
				( RescheduledTest ->
					Susps1Detachments,
					Attachment,
					BodyCopy,
					ConditionalRecursiveCall2
				;
					RecursiveCall2
				)
			;
				RecursiveCall
			)
		)
    ;
	Clause =
      		( ClauseHead :-
             		( IteratorSuspTest,
			  FirstMatching,
			  RescheduledTest ->
				Susps1Detachments,
				Attachment,
				BodyCopy,
				ConditionalRecursiveCall
			;
				RecursiveCall
			)
		)
   ),
   L = [Clause | T].

gen_state_cond_call(Susp,N,Call,Generation,ConditionalCall) :-
   length(Args,N),
   Suspension =.. [suspension,_,State,_,NewGeneration,_,_|Args],
   create_get_mutable_ref(active,State,GetState),
   create_get_mutable_ref(Generation,NewGeneration,GetGeneration),
   ConditionalCall =
      (   Susp = Suspension,
	  GetState,
          GetGeneration ->
		  'chr update_mutable'(inactive,State),
	          Call
	      ;   true
      ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
simpagation_head2_worker_end(Head,Rest,F/A,Id,L,T) :-
   head_info(Head,A,_Vars,_Susp,VarsSusp,Pairs),
   head_arg_matches(Pairs,[],_,VarDict),
   extra_active_delegate_variables(Head,Rest,VarDict,ExtraVars),
   append([[]|VarsSusp],ExtraVars,HeadVars),
   build_head(F,A,Id,HeadVars,ClauseHead),
   next_id(Id,ContinuationId),
   build_head(F,A,ContinuationId,VarsSusp,ContinuationHead),
   Clause = ( ClauseHead :- ContinuationHead ),
   L = [Clause | T].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____                                    _   _             
%% |  _ \ _ __ ___  _ __   __ _  __ _  __ _| |_(_) ___  _ __  
%% | |_) | '__/ _ \| '_ \ / _` |/ _` |/ _` | __| |/ _ \| '_ \ 
%% |  __/| | | (_) | |_) | (_| | (_| | (_| | |_| | (_) | | | |
%% |_|   |_|  \___/| .__/ \__,_|\__, |\__,_|\__|_|\___/|_| |_|
%%                 |_|          |___/                         

propagation_code(Head,RestHeads,Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,Id,L,T) :-
	( RestHeads == [] ->
		propagation_single_headed(Head,Rule,RuleNb,FA,Mod,Id,L,T)
	;   
		propagation_multi_headed(Head,RestHeads,Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,Id,L,T)
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Single headed propagation
%% everything in a single clause
propagation_single_headed(Head,Rule,RuleNb,F/A,Mod,Id,L,T) :-
   head_info(Head,A,Vars,Susp,VarsSusp,HeadPairs),
   build_head(F,A,Id,VarsSusp,ClauseHead),

   inc_id(Id,NextId),
   build_head(F,A,NextId,VarsSusp,NextHead),

   NextCall = NextHead,

   head_arg_matches(HeadPairs,[],HeadMatching,VarDict),
   guard_body_copies(Rule,VarDict,GuardCopy,BodyCopy),
   ( Id == [0] ->
	gen_cond_allocation(Vars,Susp,F/A,VarsSusp,Mod,Allocation),
	Allocation1 = Allocation
   ;
	Allocation1 = true
   ),
   gen_uncond_attach_goal(F/A,Susp,Mod,Attachment,Generation), 

   gen_state_cond_call(Susp,A,NextCall,Generation,ConditionalNextCall),

   Clause = (
        ClauseHead :-
		HeadMatching,
		Allocation1,
		'chr novel_production'(Susp,RuleNb),	% optimisation of t(RuleNb,Susp)
		GuardCopy,
		!,
		'chr extend_history'(Susp,RuleNb),
		Attachment,
		BodyCopy,
		ConditionalNextCall
   ),  
   L = [Clause | T].
   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% multi headed propagation
%% prelude + predicates to accumulate the necessary combinations of suspended
%% constraints + predicate to execute the body
propagation_multi_headed(Head,RestHeads,Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,Id,L,T) :-
   RestHeads = [First|Rest],
   propagation_prelude(Head,RestHeads,Rule,FA,N,Constraints,Mod,Id,L,L1),
   extend_id(Id,ExtendedId),
   propagation_nested_code(Rest,[First,Head],Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,ExtendedId,L1,T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
propagation_prelude(Head,[First|Rest],Rule,F/A,N,Constraints,Mod,Id,L,T) :-
   head_info(Head,A,Vars,Susp,VarsSusp,HeadPairs),
   build_head(F,A,Id,VarsSusp,PreludeHead),
   head_arg_matches(HeadPairs,[],FirstMatching,VarDict),
   Rule = rule(_,_,Guard,Body),
   extra_active_delegate_variables(Head,[First,Rest,Guard,Body],VarDict,ExtraVars),

   passive_head_via(First,[Head],[],Constraints,Mod,VarDict,FirstSuspGoal,Attr,AttrDict),   
   instantiate_pattern_goals(AttrDict,N),
   ( N == 1 ->
       	Susps = Attr
   ;
	functor(First,FirstFct,FirstAty),
	make_attr(N,_Mask,SuspsList,Attr),
        nth1(Pos,Constraints,FirstFct/FirstAty), !,
	nth1(Pos,SuspsList,Susps)
   ),

   (   Id == [0] ->
       gen_cond_allocation(Vars,Susp,F/A,VarsSusp,Mod,CondAllocation)
   ;   CondAllocation = true
   ),

   extend_id(Id,NestedId),
   append([Susps|VarsSusp],ExtraVars,NestedVars), 
   build_head(F,A,NestedId,NestedVars,NestedHead),
   NestedCall = NestedHead,

   Prelude = (
      PreludeHead :-
	  FirstMatching,
	  FirstSuspGoal,
          !,
          CondAllocation,
          NestedCall
   ),
   L = [Prelude|T].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
propagation_nested_code([],[CurrentHead|PreHeads],Rule,RuleNb,RestHeadNb,FA,_,_Constraints,Mod,Id,L,T) :-
   propagation_end([CurrentHead|PreHeads],[],Rule,FA,Id,L,L1),
   propagation_body(CurrentHead,PreHeads,Rule,RuleNb,RestHeadNb,FA,Mod,Id,L1,T).

propagation_nested_code([Head|RestHeads],PreHeads,Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,Id,L,T) :-
   propagation_end(PreHeads,[Head|RestHeads],Rule,FA,Id,L,L1),
   propagation_accumulator([Head|RestHeads],PreHeads,Rule,FA,N,Constraints,Mod,Id,L1,L2),
   inc_id(Id,IncId),
   propagation_nested_code(RestHeads,[Head|PreHeads],Rule,RuleNb,RestHeadNb,FA,N,Constraints,Mod,IncId,L2,T).

propagation_body(CurrentHead,PreHeads,Rule,RuleNb,RestHeadNb,F/A,Mod,Id,L,T) :-
   Rule = rule(_,_,Guard,Body),
   get_prop_inner_loop_vars(PreHeads,[CurrentHead,Guard,Body],PreVarsAndSusps,VarDict1,Susp,RestSusps),
   gen_var(OtherSusp),
   gen_var(OtherSusps),
   functor(CurrentHead,_OtherF,OtherA),
   gen_vars(OtherA,OtherVars),
   Suspension =.. [suspension,_,State,_,_,_,_|OtherVars],
   create_get_mutable_ref(active,State,GetMutable),
   CurrentSuspTest = (
      OtherSusp = Suspension,
      GetMutable
   ),
   ClauseVars = [[OtherSusp|OtherSusps]|PreVarsAndSusps],
   build_head(F,A,Id,ClauseVars,ClauseHead),
   RecursiveVars = [OtherSusps|PreVarsAndSusps],
   build_head(F,A,Id,RecursiveVars,RecursiveHead),
   RecursiveCall = RecursiveHead,
   CurrentHead =.. [_|OtherArgs],
   pairup(OtherArgs,OtherVars,OtherPairs),
   head_arg_matches(OtherPairs,VarDict1,Matching,VarDict),
 
   different_from_other_susps(CurrentHead,OtherSusp,PreHeads,RestSusps,DiffSuspGoals), 

   guard_body_copies(Rule,VarDict,GuardCopy,BodyCopy),
   gen_uncond_attach_goal(F/A,Susp,Mod,Attach,Generation),
   gen_state_cond_call(Susp,A,RecursiveCall,Generation,ConditionalRecursiveCall),

   history_susps(RestHeadNb,[OtherSusp|RestSusps],Susp,[],HistorySusps),
   bagof('chr novel_production'(X,Y),( member(X,HistorySusps), Y = TupleVar) ,NovelProductionsList),
   list2conj(NovelProductionsList,NovelProductions),
   Tuple =.. [t,RuleNb|HistorySusps],

   Clause = (
      ClauseHead :-
         (   CurrentSuspTest,
	     DiffSuspGoals,
             Matching,
	     TupleVar = Tuple,
	     NovelProductions,
             GuardCopy ->
	     'chr extend_history'(Susp,TupleVar),
             Attach,
             BodyCopy,
             ConditionalRecursiveCall
         ;   RecursiveCall
         )
   ),
   L = [Clause|T].


history_susps(Count,OtherSusps,Susp,Acc,HistorySusps) :-
	( Count == 0 ->
		reverse(OtherSusps,ReversedSusps),
		append(ReversedSusps,[Susp|Acc],HistorySusps)
	;
		OtherSusps = [OtherSusp|RestOtherSusps],
		NCount is Count - 1,
		history_susps(NCount,RestOtherSusps,Susp,[OtherSusp|Acc],HistorySusps)
	).


get_prop_inner_loop_vars([Head],Terms,HeadVars,VarDict,Susp,[]) :-
	!,
	functor(Head,_F,A),
	head_info(Head,A,_Vars,Susp,VarsSusp,Pairs),
	head_arg_matches(Pairs,[],_,VarDict),
	extra_active_delegate_variables(Head,Terms,VarDict,ExtraVars),
	append(VarsSusp,ExtraVars,HeadVars).
get_prop_inner_loop_vars([Head|Heads],Terms,VarsSusps,NVarDict,MainSusp,[Susp|RestSusps]) :-
	get_prop_inner_loop_vars(Heads,[Head|Terms],RestVarsSusp,VarDict,MainSusp,RestSusps),
	functor(Head,_F,A),
	gen_var(Susps),
	head_info(Head,A,_Vars,Susp,_VarsSusp,Pairs),
	head_arg_matches(Pairs,VarDict,_,NVarDict),
	passive_delegate_variables(Head,Heads,Terms,NVarDict,HeadVars),
	append(HeadVars,[Susp,Susps|RestVarsSusp],VarsSusps).

propagation_end([CurrentHead|PrevHeads],NextHeads,Rule,F/A,Id,L,T) :-
   Rule = rule(_,_,Guard,Body),
   gen_var_susp_list_for(PrevHeads,[CurrentHead,NextHeads,Guard,Body],_,VarsAndSusps,AllButFirst,FirstSusp),

   Vars = [ [] | VarsAndSusps],

   build_head(F,A,Id,Vars,Head),

   (   Id = [0|_] ->
       next_id(Id,PrevId),
       PrevVarsAndSusps = AllButFirst
   ;
       dec_id(Id,PrevId),
       PrevVarsAndSusps = [FirstSusp|AllButFirst]
   ),
  
   build_head(F,A,PrevId,PrevVarsAndSusps,PrevHead),
   PredecessorCall = PrevHead,
 
   Clause = (
      Head :-
         PredecessorCall
   ),
   L = [Clause | T].

gen_var_susp_list_for([Head],Terms,VarDict,HeadVars,VarsSusp,Susp) :-
   !,
   functor(Head,_F,A),
   head_info(Head,A,_Vars,Susp,VarsSusp,HeadPairs),
   head_arg_matches(HeadPairs,[],_,VarDict),
   extra_active_delegate_variables(Head,Terms,VarDict,ExtraVars),
   append(VarsSusp,ExtraVars,HeadVars).
gen_var_susp_list_for([Head|Heads],Terms,NVarDict,VarsSusps,Rest,Susps) :-
	gen_var_susp_list_for(Heads,[Head|Terms],VarDict,Rest,_,_),
	functor(Head,_F,A),
	gen_var(Susps),
	head_info(Head,A,_Vars,Susp,_VarsSusp,HeadPairs),
	head_arg_matches(HeadPairs,VarDict,_,NVarDict),
	passive_delegate_variables(Head,Heads,Terms,NVarDict,HeadVars),
	append(HeadVars,[Susp,Susps|Rest],VarsSusps).

propagation_accumulator([NextHead|RestHeads],[CurrentHead|PreHeads],Rule,F/A,N,Constraints,Mod,Id,L,T) :-
	Rule = rule(_,_,Guard,Body),
	pre_vars_and_susps(PreHeads,[CurrentHead,NextHead,RestHeads,Guard,Body],PreVarsAndSusps,VarDict,PreSusps),
	gen_var(OtherSusps),
	functor(CurrentHead,_OtherF,OtherA),
	gen_vars(OtherA,OtherVars),
	head_info(CurrentHead,OtherA,OtherVars,OtherSusp,_VarsSusp,HeadPairs),
	head_arg_matches(HeadPairs,VarDict,FirstMatching,VarDict1),
	
	OtherSuspension =.. [suspension,_,State,_,_,_,_|OtherVars],

	different_from_other_susps(CurrentHead,OtherSusp,PreHeads,PreSusps,DiffSuspGoals),
	create_get_mutable_ref(active,State,GetMutable),
	CurrentSuspTest = (
	   OtherSusp = OtherSuspension,
	   GetMutable,
	   DiffSuspGoals,
	   FirstMatching
	),
	functor(NextHead,NextF,NextA),
	passive_head_via(NextHead,[CurrentHead|PreHeads],[],Constraints,Mod,VarDict1,NextSuspGoal,Attr,AttrDict),   
	instantiate_pattern_goals(AttrDict,N),
	( N == 1 ->
	     NextSusps = Attr
	;
	     nth1(Position,Constraints,NextF/NextA), !,
	     make_attr(N,_Mask,SuspsList,Attr),
	     nth1(Position,SuspsList,NextSusps)
	),
	inc_id(Id,NestedId),
	ClauseVars = [[OtherSusp|OtherSusps]|PreVarsAndSusps],
	build_head(F,A,Id,ClauseVars,ClauseHead),
	passive_delegate_variables(CurrentHead,PreHeads,[NextHead,RestHeads,Guard,Body],VarDict1,CurrentHeadVars),
	append([NextSusps|CurrentHeadVars],[OtherSusp,OtherSusps|PreVarsAndSusps],NestedVars),
	build_head(F,A,NestedId,NestedVars,NestedHead),
	
	RecursiveVars = [OtherSusps|PreVarsAndSusps],
	build_head(F,A,Id,RecursiveVars,RecursiveHead),
	Clause = (
	   ClauseHead :-
	   (   CurrentSuspTest,
	       NextSuspGoal
	       ->
	       NestedHead
	   ;   RecursiveHead
	   )
	),   
	L = [Clause|T].

pre_vars_and_susps([Head],Terms,HeadVars,VarDict,[]) :-
	!,
	functor(Head,_F,A),
	head_info(Head,A,_Vars,_Susp,VarsSusp,HeadPairs),
	head_arg_matches(HeadPairs,[],_,VarDict),
	extra_active_delegate_variables(Head,Terms,VarDict,ExtraVars),
	append(VarsSusp,ExtraVars,HeadVars).
pre_vars_and_susps([Head|Heads],Terms,NVSs,NVarDict,[Susp|Susps]) :-
	pre_vars_and_susps(Heads,[Head|Terms],VSs,VarDict,Susps),
	functor(Head,_F,A),
	gen_var(NextSusps),
	head_info(Head,A,_Vars,Susp,_VarsSusp,HeadPairs),
	head_arg_matches(HeadPairs,VarDict,_,NVarDict),
	passive_delegate_variables(Head,Heads,Terms,NVarDict,HeadVars),
	append(HeadVars,[Susp,NextSusps|VSs],NVSs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ____               _             _   _                _ 
%% |  _ \ __ _ ___ ___(_)_   _____  | | | | ___  __ _  __| |
%% | |_) / _` / __/ __| \ \ / / _ \ | |_| |/ _ \/ _` |/ _` |
%% |  __/ (_| \__ \__ \ |\ V /  __/ |  _  |  __/ (_| | (_| |
%% |_|   \__,_|___/___/_| \_/ \___| |_| |_|\___|\__,_|\__,_|
%%                                                          
%%  ____      _        _                 _ 
%% |  _ \ ___| |_ _ __(_) _____   ____ _| |
%% | |_) / _ \ __| '__| |/ _ \ \ / / _` | |
%% |  _ <  __/ |_| |  | |  __/\ V / (_| | |
%% |_| \_\___|\__|_|  |_|\___| \_/ \__,_|_|
%%                                         
%%  ____                    _           _             
%% |  _ \ ___  ___  _ __ __| | ___ _ __(_)_ __   __ _ 
%% | |_) / _ \/ _ \| '__/ _` |/ _ \ '__| | '_ \ / _` |
%% |  _ <  __/ (_) | | | (_| |  __/ |  | | | | | (_| |
%% |_| \_\___|\___/|_|  \__,_|\___|_|  |_|_| |_|\__, |
%%                                              |___/ 

reorder_heads(Head,RestHeads,RestIDs,NRestHeads,NRestIDs) :-
	( chr_pp_flag(reorder_heads,on) ->
		reorder_heads_main(Head,RestHeads,RestIDs,NRestHeads,NRestIDs)
	;
		NRestHeads = RestHeads,
		NRestIDs = RestIDs
	).

reorder_heads_main(Head,RestHeads,RestIDs,NRestHeads,NRestIDs) :-
	term_variables(Head,KnownVars),
	reorder_heads1(RestHeads,RestIDs,KnownVars,NRestHeads,NRestIDs).

reorder_heads1(Heads,IDs,KnownVars,NHeads,NIDs) :-
	( Heads == [] ->
		NHeads = [],
		NIDs = []
	;
		NHeads = [BestHead|BestTail],
		NIDs = [BestID | BestIDs],
		select_best_head(Heads,IDs,KnownVars,BestHead,BestID,RestHeads,RestIDs,NKnownVars),
		reorder_heads1(RestHeads,RestIDs,NKnownVars,BestTail,BestIDs)
	).

select_best_head(Heads,IDs,KnownVars,BestHead,BestID,RestHeads,RestIDs,NKnownVars) :-
		( bagof(tuple(Score,Head,ID,Rest,RIDs), (
					select2(Head,ID, Heads,IDs,Rest,RIDs) , 
					order_score(Head,KnownVars,Rest,Score) 
				    ), 
				    Scores) -> true ; Scores = []),
		max_go_list(Scores,tuple(_,BestHead,BestID,RestHeads,RestIDs)),
		term_variables(BestHead,BestHeadVars),
		( setof(V, (
				member(V,BestHeadVars),
				\+ memberchk_eq(V,KnownVars) 
			 ),
			 NewVars) -> true ; NewVars = []),
		append(NewVars,KnownVars,NKnownVars).

reorder_heads(Head,RestHeads,NRestHeads) :-
	term_variables(Head,KnownVars),
	reorder_heads1(RestHeads,KnownVars,NRestHeads).

reorder_heads1(Heads,KnownVars,NHeads) :-
	( Heads == [] ->
		NHeads = []
	;
		NHeads = [BestHead|BestTail],
		select_best_head(Heads,KnownVars,BestHead,RestHeads,NKnownVars),
		reorder_heads1(RestHeads,NKnownVars,BestTail)
	).

select_best_head(Heads,KnownVars,BestHead,RestHeads,NKnownVars) :-
		( bagof(tuple(Score,Head,Rest), (
					select(Head,Heads,Rest) , 
					order_score(Head,KnownVars,Rest,Score) 
				    ), 
				    Scores) -> true ; Scores = []),
		max_go_list(Scores,tuple(_,BestHead,RestHeads)),
		term_variables(BestHead,BestHeadVars),
		( setof(V, (
				member(V,BestHeadVars),
				\+ memberchk_eq(V,KnownVars) 
			 ),
			 NewVars) -> true ; NewVars = []),
		append(NewVars,KnownVars,NKnownVars).

order_score(Head,KnownVars,Rest,Score) :-
	term_variables(Head,HeadVars),
	term_variables(Rest,RestVars),
	order_score_vars(HeadVars,KnownVars,RestVars,0,Score).

order_score_vars([],_,_,Score,NScore) :-
	( Score == 0 ->
		NScore = 99999
	;
		NScore = Score
	).
order_score_vars([V|Vs],KnownVars,RestVars,Score,NScore) :-
	( memberchk_eq(V,KnownVars) ->
		TScore is Score + 1
	; memberchk_eq(V,RestVars) ->
		TScore is Score + 1
	;
		TScore = Score
	),
	order_score_vars(Vs,KnownVars,RestVars,TScore,NScore).
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  ___       _ _       _             
%% |_ _|_ __ | (_)_ __ (_)_ __   __ _ 
%%  | || '_ \| | | '_ \| | '_ \ / _` |
%%  | || | | | | | | | | | | | | (_| |
%% |___|_| |_|_|_|_| |_|_|_| |_|\__, |
%%                              |___/ 

%% SWI begin
create_get_mutable_ref(V,M,GM) :- GM = (M = mutable(V)).
%% SWI end

%% SICStus begin
%% create_get_mutable_ref(V,M,GM) :- GM = (get_mutable(V,M)).
%% SICStus end



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%   ____          _         ____ _                  _             
%%  / ___|___   __| | ___   / ___| | ___  __ _ _ __ (_)_ __   __ _ 
%% | |   / _ \ / _` |/ _ \ | |   | |/ _ \/ _` | '_ \| | '_ \ / _` |
%% | |__| (_) | (_| |  __/ | |___| |  __/ (_| | | | | | | | | (_| |
%%  \____\___/ \__,_|\___|  \____|_|\___|\__,_|_| |_|_|_| |_|\__, |
%%                                                           |___/ 
%%
%% removes redundant 'true's and other trivial but potentially non-free constructs

clean_clauses([],[]).
clean_clauses([C|Cs],[NC|NCs]) :-
	clean_clause(C,NC),
	clean_clauses(Cs,NCs).

clean_clause(Clause,NClause) :-
	( Clause = (Head :- Body) ->
		clean_goal(Body,NBody),
		( NBody == true ->
			NClause = Head
		;
			NClause = (Head :- NBody)
		)
	;
		NClause = Clause
	).

clean_goal(Goal,NGoal) :-
	var(Goal), !,
	NGoal = Goal.
clean_goal((G1,G2),NGoal) :-
	!,
	clean_goal(G1,NG1),
	clean_goal(G2,NG2),
	( NG1 == true ->
		NGoal = NG2
	; NG2 == true ->
		NGoal = NG1
	;
		NGoal = (NG1,NG2)
	).
clean_goal((If -> Then ; Else),NGoal) :-
	!,
	clean_goal(If,NIf),
	( NIf == true ->
		clean_goal(Then,NThen),
		NGoal = NThen
	; NIf == fail ->
		clean_goal(Else,NElse),
		NGoal = NElse
	;
		clean_goal(Then,NThen),
		clean_goal(Else,NElse),
		NGoal = (NIf -> NThen; NElse)
	).
clean_goal((G1 ; G2),NGoal) :-
	!,
	clean_goal(G1,NG1),
	clean_goal(G2,NG2),
	( NG1 == fail ->
		NGoal = NG2
	; NG2 == fail ->
		NGoal = NG1
	;
		NGoal = (NG1 ; NG2)
	).
clean_goal(once(G),NGoal) :-
	!,
	clean_goal(G,NG),
	( NG == true ->
		NGoal = true
	; NG == fail ->
		NGoal = fail
	;
		NGoal = once(NG)
	).
clean_goal((G1 -> G2),NGoal) :-
	!,
	clean_goal(G1,NG1),
	( NG1 == true ->
		clean_goal(G2,NGoal)
	; NG1 == fail ->
		NGoal = fail
	;
		clean_goal(G2,NG2),
		NGoal = (NG1 -> NG2)
	).
clean_goal(Goal,Goal).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  _   _ _   _ _ _ _
%% | | | | |_(_) (_) |_ _   _
%% | | | | __| | | | __| | | |
%% | |_| | |_| | | | |_| |_| |
%%  \___/ \__|_|_|_|\__|\__, |
%%                      |___/

gen_var(_).
gen_vars(N,Xs) :-
   length(Xs,N). 

head_info(Head,A,Vars,Susp,VarsSusp,HeadPairs) :-
   vars_susp(A,Vars,Susp,VarsSusp),
   Head =.. [_|Args],
   pairup(Args,Vars,HeadPairs).
 
inc_id([N|Ns],[O|Ns]) :-
   O is N + 1.
dec_id([N|Ns],[M|Ns]) :-
   M is N - 1.

extend_id(Id,[0|Id]).

next_id([_,N|Ns],[O|Ns]) :-
   O is N + 1.

build_head(F,A,Id,Args,Head) :-
   buildName(F,A,Id,Name),
   Head =.. [Name|Args].

buildName(Fct,Aty,List,Result) :-
   atom_concat(Fct, (/) ,FctSlash),
   atomic_concat(FctSlash,Aty,FctSlashAty),
   buildName_(List,FctSlashAty,Result).

buildName_([],Name,Name).
buildName_([N|Ns],Name,Result) :-
  buildName_(Ns,Name,Name1),
  atom_concat(Name1,'__',NameDash),    % '_' is a char :-(
  atomic_concat(NameDash,N,Result).

vars_susp(A,Vars,Susp,VarsSusp) :-
   length(Vars,A),
   append(Vars,[Susp],VarsSusp).

make_attr(N,Mask,SuspsList,Attr) :-
	length(SuspsList,N),
	Attr =.. [v,Mask|SuspsList].

or_pattern(Pos,Pat) :-
	Pow is Pos - 1,
	Pat is 1 << Pow.      % was 2 ** X

and_pattern(Pos,Pat) :-
	X is Pos - 1,
	Y is 1 << X,          % was 2 ** X
	Pat is -(Y + 1).

conj2list(Conj,L) :-				%% transform conjunctions to list
  conj2list(Conj,L,[]).

conj2list(Conj,L,T) :-
  Conj = (G1,G2), !,
  conj2list(G1,L,T1),
  conj2list(G2,T1,T).
conj2list(G,[G | T],T).

list2conj([],true).
list2conj([G],X) :- !, X = G.
list2conj([G|Gs],C) :-
	( G == true ->				%% remove some redundant trues
		list2conj(Gs,C)
	;
		C = (G,R),
		list2conj(Gs,R)
	).

atom_concat_list([X],X) :- ! .
atom_concat_list([X|Xs],A) :-
	atom_concat_list(Xs,B),
	atomic_concat(X,B,A).

set_elems([],_).
set_elems([X|Xs],X) :-
	set_elems(Xs,X).

member2([X|_],[Y|_],X-Y).
member2([_|Xs],[_|Ys],P) :-
	member2(Xs,Ys,P).

select2(X, Y, [X|Xs], [Y|Ys], Xs, Ys).
select2(X, Y, [X1|Xs], [Y1|Ys], [X1|NXs], [Y1|NYs]) :-
	select2(X, Y, Xs, Ys, NXs, NYs).

pair_all_with([],_,[]).
pair_all_with([X|Xs],Y,[X-Y|Rest]) :-
	pair_all_with(Xs,Y,Rest).

default(X,Def) :-
	( var(X) -> X = Def ; true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% SWI begin
verbosity_on :- prolog_flag(verbose,V), V == yes.
%% SWI end

%% SICStus begin
%% verbosity_on.  % at the moment
%% SICStus end
