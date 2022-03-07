:- module(rrecurse,
       [rrcall/1, rrcall/2, rrcall/3,
        rwrite_off/0, rwrite_on/0,
        rwriteln/1, %rwriteln/2,
        rwrite/1, rwriteq/1, rwriteqln/1,
        rformat/2,rformat/3
       ]).

/** <module> Recursive call tracing utility
This module provides developers with a simple yet robust way to add
trace output to any recursive predicate. The output is clearly
indented and color-coded to reflect the depth of each layer of
recursion. This, combined with several other specialized term-writing
features, enables the developer to see at-a-glance the progressive
unification of predicate arguments and the course taken when
backtracking.

@author Stan Soo
@license BSD2
*/


:- use_module(library(lists)).
:- use_module(library(occurs)).
:- use_module(library(terms)).
:- use_module(library(assoc), [empty_assoc/1, put_assoc/4, get_assoc/3]).
:- use_module(library(ansi_term), [ansi_format/3]).
:- use_module(library(intercept), [intercept/3, intercept/4, intercept_all/4,
                                   nb_intercept_all/4, send_signal/1,
                                   send_silent_signal/1]).
% See also catch/4, reset/3, shift/1, shift_for_copy/1


:- autoload(library(rbtrees),
	    [ %rb_empty/1,
	      rb_lookup/3,
	      rb_insert/4,
	      rb_new/1,
	      rb_visit/2,
	      ord_list_to_rbtree/2,
	      rb_update/5
	    ]).

:- module_transparent
        rrcall/1, rrcall/2, rrcall/3,
        rrcall_setup/9, rrcall_cleanup/3,
        create_rrcall_body/13,
        create_rrcall_body_/12,
        rr_intercept/6.%,
        %print_call1/6.



                      /**********************
                      * EXPORTED PREDICATES *
                      **********************/


%!  rrcall(+Goal) is det.
%!  rrcall(+Goal, +Template) is det.
%!  rrcall(+Goal, +Template, +Binds) is det.
%
%   When Template is not specified, Goal is expected to be a single, standalone
%   invocation of a recursive predicate.
%
%   When Template is provided, Goal can be any syntactically valid callable
%   term. Occurrences of Template within Goal will be wrapped with
%   ``rrcall(...)``. The instantiation of the argument(s) of Template is
%   taken into consideration when making these replacements, but it is
%   disregarded when temporarily wrapping the definition of the predicate
%   that Template refers to.
%
%   In other words, given a Template with name _Name_ and of arity _Arity_:
%
%   * Within Goal, a term of ``Name/Arity`` will only be _rrcall_-ed if
%     its arguments can be unified with those of Template.
%   * Within the clauses of the predicate ``Name/Arity``, _all_ calls to
%     ``Name/Arity`` (that is, _all_ recursive calls) will call the wrapper
%     wrapper (within which the original predicate will then be called).
%
%   The arity-3 version is used by the module to pass along toplevel (and,
%   in the future, original-source) variable names via definitions of the
%   hook predicates user:term_expansion/4 and user:expand_query/4.

rrcall(Goal) :-
        notrace(most_general_goal(Goal, Template)),
        rrcall(Goal, Template, []).
rrcall(Goal, Template) :-
        rrcall(Goal, Template, []).
rrcall(Goal, Template0, Binds) :-
        must_be(callable, Goal),
        (   is_predicate_indicator(Template0)
        ->  PI0=Template0
        ;   must_be(callable, Template0),
            Template=Template0
        ),
        pi_head(PI0,Template),
        most_general_goal(Template,GTemplate),
        (
          predicate_property(GTemplate,visible)
        -> ( strip_module(Template,TModule0,THead),
           strip_module(PI0,TModule0,TName/TArity),
           strip_module(GTemplate,_,GHead),
           ( current_predicate(TModule:TName/Arity),
             Arity=TArity,
             once((predicate_property(GHead,imported_from(TModule))
                  ;   predicate_property(GHead,implementation_module(TModule))
                  )
           )),
           !%,writeq(TModule:TName/TArity),nl
           )

        ;  throw(error(existence_error(procedure,PI0), _))
        ),
        context_module(CM),%rwrite('rrcall context module: '),rwriteln(M),
        !,
        setup_call_cleanup(
            rrecurse:rrcall_setup(CM,TModule:TName/TArity,PI0,Template,GTemplate,THead,GHead,Binds,GlobalNames),
            @(rrecurse:intercept(Goal,rr_intercept(N,Mode),
                                 rrecurse:rr_intercept(
                                              CM, TModule:TName/TArity,
                                              PI0, Binds, GlobalNames),
                                 [N,Mode]), CM),
            rrecurse:rrcall_cleanup(CM,TModule:TName/TArity,GlobalNames)).



rr_intercept(CM,Module:_Name/_Arity, _PITemplate,
             _Binds, [_CountName,ClauseHeadName,_GHName,TrackerName],
             [N,Mode]) :-
        @((b_getval(TrackerName,TrackerAssoc0),
        get_assoc(N,TrackerAssoc0,TrackerList-_StatusMarkers),
        b_getval(ClauseHeadName,HeadAssoc),
        get_assoc(N,HeadAssoc,CH-GH)), CM),
        %unifiable(CH,GH,Substs),
        (   CH=Module:CHNoModule,
            nonvar(CHNoModule)
        -> !
        ;   CH=CHNoModule
        ),
        %term_variables(CHNoModule,Vars),
        %copy_term_nat(Vars,CHNoModule,[],CH1),
        @(rrecurse:print_call1(N,Mode,[], % TODO: BindCodes?
                             CHNoModule,
                             CH, GH),
          CM),
        (   InterceptType=before_fail
        ->  maplist(=(y),TrackerList)
        ->  nth0(I,[pre_call,after_enter,before_exit,post_call],InterceptType),
            nth0(I,TrackerList,y)
        ).


                 /*******************
                 * WRAPPER CREATION *
                 *******************/

rrcall_global_names(PI, [CountName,ClauseHeadName,GHName,TrackerName]) :-
        term_to_atom(PI,PIAtom),
        atom_concat(PIAtom,'__rr_count',CountName),
        atom_concat(PIAtom,'__rr_clause_head',ClauseHeadName),
        atom_concat(PIAtom,'__rr_gen_head',GHName),
        atom_concat(PIAtom,'__rr_track_print',TrackerName).

rrcall_setup(CM,Mod:Name/Arity,PIT,THT,GHT,THead,GHead,Binds,[CountName,ClauseHeadName,GHName,TrackerName]) :-
        %writeln(inside_setup),
        rrecurse:rrcall_global_names(Mod:Name/Arity,[CountName,ClauseHeadName,GHName,TrackerName]),
        %writeln(calling_wrap),
        %context_module(M),rwrite('rrcall_setup context module: '),rwriteln(M),
        rrecurse:rrcall_wrap_predicate(CM,Mod:Name/Arity,PIT,THT,GHT,THead,GHead,[CountName,ClauseHeadName,GHName,TrackerName],Binds),
        @((rrecurse:b_setval(CountName, -1),
           rrecurse:b_setval(GHName,GHead),
           empty_assoc(A),
           rrecurse:b_setval(ClauseHeadName,A),
           length(Tracker,Arity),
           maplist(=(true),Tracker),
           TrackerVar = [y,y,y,y]-Tracker,
           list_to_assoc([-1-TrackerVar],TrackerAssoc),
           rrecurse:b_setval(TrackerName,TrackerAssoc)
          ),
          CM).


rrcall_cleanup(CM,PI,[CountName,ClauseHeadName,GHName,TrackerName]) :-
        PI = M:_,
        @(rrecurse:unwrap_predicate(PI,rrcall_wrapper),M),
        @((
            rrecurse:nb_delete(CountName),
            rrecurse:nb_delete(ClauseHeadName),
            rrecurse:nb_delete(GHName),
            rrecurse:nb_delete(TrackerName)),
          CM).

rrcall_wrap_predicate(CM,PI,PIT,THT,GHT,THead,GHead,GlobalNames,Binds) :-
        %writeln(inside_wrap_pred),
        PI=TModule:TName/TArity,
        %writeln(inside_wrap_pred_u),
        @((rrecurse:create_rrcall_body(CM,TModule:TName/TArity,PIT,
                                       THT,GHT,THead,GHead,
                                       _AllHeads,Binds,
                                       GlobalNames,
                                       Closure,Wrapped, Body),
           '$wrap_predicate'(GHT, rrcall_wrapper, Closure, Wrapped, Body)
          ),
          TModule).

create_rrcall_body(CM,TModule:TName/TArity,PIT,_THT,GHT,_THead,TGen, _AllHeads, Binds, GlobalNames, Closure, Wrapped, Body) :-
        callable_name_arguments(TGen,TName,GArguments),
        %GlobalNames=[_,_,_,TrackerName|_],
        %length(Tracker,TArity),
        %TrackerVar = _N/_P//Tracker,
        %@(rrecurse:b_setval(TrackerName,TrackerVar),CM),
        create_rrcall_body_(CM,TModule:TName/TArity,PIT,GHT,TGen,GArguments,_ZippedHeadsAndArgs,Binds,GlobalNames,Closure,Wrapped,Body).

rr_undo(_,_) :- !.
create_rrcall_body_(
    CM,
    M:TName/TArity,
    PIT,
    GHT,
    GenHead,
    _GenArguments,
    _ZippedHeadsAndArgs,
    Binds,
    [CountName,ClauseHeadName,GHName,TrackerName],
    Closure,
    Wrapped,
    (

        @((
           b_getval(CountName,N0),
           b_getval(TrackerName,TrackerAssoc00),
           get_assoc(N0,TrackerAssoc00,[EC,AE,BX,OC]-Tracker00),
           b_getval(ClauseHeadName,ClauseHeadAssoc0),


                     %format('TrackerAssoc00: ~w, ClauseHeadAssoc0: ~w~n',
             %      [TrackerAssoc00,ClauseHeadAssoc0]),
           (   AE==y
           ->  %writeln(ae_is_y),
                  TrackerAssoc0=TrackerAssoc00
             ;   %writeln(ae_not_y),
                  get_assoc(N0,ClauseHeadAssoc0,ClauseHead00-GHead00),
                  %format('ClauseHead00-GHead00: ~q~n',[ClauseHead00-GHead00]),
                  term_variables(ClauseHead00,AllVars),
               copy_term_nat(AllVars,ClauseHead00,_,ClauseHead01),
                 %!, % TODO: This cut???
                 (   var(ClauseHead01)
                     -> copy_term_nat(AllVars,GHead00,_,ClauseHead01),
                        ClauseHeadNoModule=ClauseHead01
                     ; once(( subsumes(M:ClauseHeadNoModule,ClauseHead01)
                            ; subsumes(ClauseHeadNoModule,ClauseHead01))
                     )
                 ),
                 rrecurse:rformat('Missed a print (~w)!~n', [N0] ),
                 undo((
                     rrecurse:rformat('Undoing, just before catch-up after_enter (checking ~w)~n', [N0]))),
               @(rrecurse:print_call1(N0,after_enter,[],
                                      ClauseHeadNoModule,
                                      ClauseHead01, GHead00),
                   CM),
                 undo(rrecurse:rformat('Undoing, just after catch-up after_enter (~w)~n', [N0])),
                 rrecurse:put_assoc(N0,TrackerAssoc00,[EC,y,BX,OC]-Tracker00,TrackerAssoc0)
                 %,writeln(updated_trackerassoc)
             ),
           undo(rrecurse:rformat('Undoing, just after AE==y cond block (checking ~w)~n',[N0])),
             N1 is N0 + 1,
             rrecurse:b_setval(CountName,N1),
             rrecurse:put_assoc(N1,ClauseHeadAssoc0,_ClauseHeadVar0-GenHead,ClauseHeadAssoc1),
             b_setval(ClauseHeadName,ClauseHeadAssoc1),
             rrecurse:print_call(N0,pre_call,GHT,Binds),
             rrecurse:put_assoc(N1,TrackerAssoc0,[_,_,_,_]-StatusMarkers,TrackerAssoc1),
             b_setval( TrackerName, TrackerAssoc1 )

             %writeln(putting_head_var_attrs),

            %assoc_to_list(ClauseHeadAssoc1,List0),
            %length(List0,Num),
            %term_attvars(GenHead,AttVars),
            %ansi_format([bg(red),hfg(white)],'ATTVARS (~w/~w): ~q~n',[N1,Num,AttVars])
             %,writeln(put_head_var_attrs)
          ),
            CM),
        %writeln('Put head variable attributes.'),
        %undo(rrecurse:rwriteln(N1,'~t<00')),rrecurse:rwriteln(N1,'>00'),
        %rrecurse:rformat('== Clause ~w == ~n', [N1]),
        undo(rrecurse:rformat('Undoing, just before wrapped cond. block (~w)~n', [N1])),
        (   undo(rrecurse:rformat('Undoing, just before Wrapped (~w)~n',[N1])),
            @(rrecurse:put_head_variables_attributes(Binds,M:TName/TArity,PIT,GHT,Closure,N1,[CountName,ClauseHeadName,GHName,TrackerName],StatusMarkers),CM),
            @(Wrapped,CM),
            undo((rrecurse:rformat('Undoing, just after Wrapped (~w)~n',[N1]),
                  rrecurse:rr_undo(N1,back_up_back_into)))
        -> @((
                b_getval(ClauseHeadName,ClauseHeadAssoc2),
                get_assoc(N1,ClauseHeadAssoc2,ClauseHeadVar-GenHead),
                term_variables(GenHead,GenHeadVars),
                %maplist([V]>>del_attr(V,rrecurse),GenHeadVars),
               (   var(ClauseHeadVar)
               -> copy_term_nat(GenHeadVars,GenHead,_,ClauseHead1)
                  %,ClauseHeadVar=ClauseHead1
               ; once(( subsumes(M:ClauseHead1,ClauseHeadVar)
                      ; subsumes(ClauseHead1,ClauseHeadVar)
                     )
                 )
               ),
               %(   var(ClauseHeadVar)
               % ->  subsumes(M:ClauseHead1,...)
               %     once((subsumes(M:ClauseHead1,ClauseHeadVar)
               %      ;  ClauseHeadVar = ClauseHead1
                %     )),
                rrecurse:rformat('ClauseHead1: ~q, GenHead: ~q~n', [ClauseHead1,GenHead]),
                unifiable(ClauseHead1,GenHead,Binds0), % was ClauseHeadVar

                rrecurse:rformat('Wrapper substitutions: ~q~n', [Binds0]),
                rrecurse:rformat('ClauseHeadVar: ~q, ClauseHead1: ~q, GenHead: ~q~n', [ClauseHeadVar,ClauseHead1,GenHead]),
                maplist([X=Y,XCodes=YCodes]>>(
                            write_term_to_codes(X,XCodes,[quoted(true)]),
                            write_term_to_codes(Y,YCodes,[quoted(true)])
                        ),Binds0,Binds1),
                    %writeln(printing_aftercalls),
                    rrecurse:rformat('Binds1: ~W~n',[Binds1,[portray(true)]]),
                    rrecurse:print_call(N1,before_exit,ClauseHead1,Binds,Binds1),% was ClauseHeadVar
                    b_getval(TrackerName,TrackerAssoc2),
                    get_assoc(N1,TrackerAssoc2,N1_Tracker-_N1_SMs),
                    get_assoc(N0,TrackerAssoc2,N0_Tracker-_N0_SMs),

                    N1_Tracker=[_,_,y,_],
                rrecurse:print_call(N0,post_call,GenHead,Binds),
                N0_Tracker=[_,_,_,y]
              ),
              CM)
        ;   %writeln(goal_failed),
            @((rrecurse:print_call(N0,before_fail,GenHead,Binds)),CM),
            fail
        )
    )
).


prolog_parent_frames(F,Frames) :-
        (   prolog_frame_attribute(F,parent,PF)
        -> Frames=[PF|Rest],
           prolog_parent_frames(PF,Rest)
        ;   Frames=[]
        ).


print_parent_frames(F) :-
        (   get_flag(rwrite,1)
        ->  prolog_parent_frames(F,Frames),
            %writeq(Frames),nl,
            length(Frames,Length),
            length(Indexes,Length),
            foreach((between(1,Length,I), K is I+0),
                    (
                        nth1(I,Indexes,K)
                    )),
            %writeln(Indexes),
            maplist([F,I,(I,PI,Head)
                    ]>>(prolog_frame_attribute(
                            F,predicate_indicator,PI),
                        ignore((prolog_frame_attribute(F,clause,Clause),
                                clause(Head,_,Clause)))
                       ),
                    [F|Frames], [0|Indexes], Infos),
            forall(member((I,PI,Head),Infos),
                   (   ansi_format([bg(red),hfg(white)],'~a ',[I]),
                       ansi_format([bg(red),hfg(white),bold],'~q ',[PI]),
                       ( var(Head)
                       ->  nl
                       ; ansi_format([bg(yellow),fg(black)],'~q~n',[Head])))
                  )
        ;   true
        ).

find_pf(F,Module,Name,Arity,PF) :-
        prolog_frame_attribute(F,predicate_indicator,PI),
        (   once((PI=Module:Name/Arity ; PI=Name/Arity))
        -> PF = F
        ;   prolog_frame_attribute(F,parent,P),
            find_pf(P,Module,Name,Arity,PF)
        ), !.

prolog_parent_frame(PF) :-
        prolog_parent_frame(2,PF).

prolog_parent_frame(N,PF) :-
        must_be(positive_integer,N),
        prolog_current_frame(F),
        prolog_frame_attribute(F,parent,PF0),
        N1 is N + 0,%N1 is N + 8,
        prolog_parent_frame(N1,PF0,PF).

prolog_parent_frame(0,F,F) :- !.
prolog_parent_frame(N,F,PF) :-
        prolog_frame_attribute(F,parent,PF0),
        N1 is N-1,
        prolog_parent_frame(N1,PF0,PF).





                /*****************************
                *    ATTRIBUTED VARIABLES    *
                *****************************/

put_head_variables_attributes(Binds,TModule:TName/TArity,_PIT,GHT,Closure,N1,GlobalNames,StatusMarkers) :-
        term_variables(GHT,Vars),
        length(Vars,NumVars),
        length(Indexes,NumVars),
        length(StatusMarkers,NumVars),
        foreach(between(1,NumVars,I),nth1(I,Indexes,I)),
        maplist([X=Y,YCodes=XCodes]>>(
                    atom_codes(X,XCodes),
                    write_term_to_codes(Y,YCodes,[quoted(true)])
                ),Binds,BindCodes),
        maplist(rrecurse:put_head_variable_attribute(
                             Binds,BindCodes,
                             TModule:TName/TArity,
                             Closure,
                             StatusMarkers,N1,
                             GlobalNames),
                Indexes, Vars).

put_head_variable_attribute(Binds,BindCodes,PI,Closure,StatusMarkers,N1,GlobalNames,N,HeadVar) :-
        (   ( member(Name=HV,Binds), HV==HeadVar )
        -> put_attr(AttributedVar, rrecurse, rrcall_attr(GlobalNames,PI,Closure,N1,StatusMarkers,N,Name,BindCodes))
        ;   put_attr(AttributedVar, rrecurse, rrcall_attr(GlobalNames,PI,Closure,N1,StatusMarkers,N, _,BindCodes))
        ),
        HeadVar = AttributedVar.

head_variable(Var,AttrValue) :-
        var(AttrValue), !,
        get_attr(Var,rrecurse,AttrValue),
        AttrValue==rrcall_attr(_GNs,_PI,_C,_N1,_SMs,_N,_Name,_BCs).

head_variable(Var,rrcall_attr(GlobalNames,PI,C,N1,SMs,N,Name,BindCodes)) :-
        put_attr(AttributedVar, rrecurse, rrcall_attr(GlobalNames,PI,C,N1,SMs,N,Name,BindCodes)),
        Var = AttributedVar.

attribute_goals(Var) -->
        { get_attr(
              Var, rrecurse,
              rrcall_attr(GlobalNames,PI,C,N1,SMs,N,Name,BindCodes))
        },
        [ head_variable(
              Var,
              rrcall_attr(GlobalNames,PI,C,N1,SMs,N,Name,BindCodes))
        ].

attr_unify_hook(AttrVal, _Val2) :-
        AttrVal=rrcall_attr(
                    [_CountName,ClauseHeadName,_GHName,TrackerName],
                    M:Name/Arity,_Closure,
                    N1,StatusMarkers,
                    N,_VarName,
                    BindCodes),
        %writeln(attr_unify_hook),
        b_getval(TrackerName,TrackerAssoc0),
        %format('Got TrackerAssoc0: ~q~n', [TrackerAssoc0]),
        get_assoc(N1,TrackerAssoc0,TrackerVar0),
        %format('Got TrackerVar0 (~w): ~q. (SMs: ~q)~n', [N1,TrackerVar0,StatusMarkers]),
        TrackerVar0=[_,AE,_,_]-StatusMarkers,
        prolog_current_frame(F),
        %print_parent_frames(F),
        ( AE==y
        ->  %undo(nth1(N1,StatusMarkers,_)),
            nth1(N1,StatusMarkers,true)
        ;   find_pf(F,M,Name,Arity,PF), !
        -> (   prolog_frame_attribute(PF,clause,ClauseRef),
              (  clause(M:ClauseHead,_Body,ClauseRef)
              ;  clause(ClauseHead,_Body,ClauseRef)
              ),
            head_name_arity(ClauseHead,Name,Arity)
            -> %format('PF ClauseHead: ~q~n', [ClauseHead]),
               %b_getval(GHName,GHVar),%TODO!!
                b_getval(ClauseHeadName,ClauseHeadAssoc0),
                %writeln(got_ghvvar_and_clauseheadassoc),
                (   get_assoc(N1,ClauseHeadAssoc0,Entry),
                    Entry=ClauseHeadVar-GHVar
                ->  true%writeln(unified_existing_entry),true%ClauseHeadAssoc1=ClauseHeadAssoc0
                ;   %format('Cant unify ~q with entry ~q~n',[ClauseHeadVar-GHVar,Entry]),
                    put_assoc(N1,ClauseHeadAssoc0,ClauseHeadVar-GHVar,ClauseHeadAssoc1),
                    %format('Put new entry ~q @ ~q in ClauseHeadAssoc1~n',[ClauseHeadVar-GHVar,N1]),
                    b_setval(ClauseHeadName,ClauseHeadAssoc1)
                    %,writeln(updated_clauseheead_assoc)
                ),
                      %(   get_assoc(N1,ClauseHeadAssoc0,ClauseHeadVar-GHVar0),
                           %    GHVar0==GHVar
                           %->  ClauseHeadAssoc0=ClauseHeadAssoc1
                           %;   put_assoc(N1,ClauseHeadAssoc0,ClauseHeadVar-GHVar0,ClauseHeadAssoc1),
                           %    b_setval(ClauseHeadName,ClauseHeadAssoc1)
                %),
                %!write(found_clause),%write('. ClauseHead1: '), writeq(ClauseHead),nl,
                           %once(
                          %    ( get_assoc(N1,ClauseHeadAssoc0,ClauseHeadVar)
                              %    ; ( put_assoc(N1,ClauseHeadAssoc0,ClauseHeadVar,ClauseHeadAssoc1),
                                 %        b_setval(ClauseHeadName,ClauseHeadAssoc1))
                                %    )
                %),
                %writeln(got_chv),
                term_variables(ClauseHead,AllVars),
                %write('. ClauseHeadVar: '), writeq(ClauseHeadVar),nl,
                copy_term_nat(AllVars,ClauseHead,_,ClauseHead1),
                %write(copied_term),
                %write('. ClauseHead1: '), writeq(ClauseHead1),nl,
                ClauseHead1=ClauseHeadVar,
                %writeln(unified_ch1_and_chv),
                once(( (nonvar(ClauseHead1),ClauseHead1=M:ClauseHeadNoModule)
                     ; ClauseHeadNoModule=ClauseHead1)
                    ),
                %writeln(got_ch_nomod),
                nth1(N,StatusMarkers,true),
                %writeln(updated_status_markers),
            (   maplist(==(true),StatusMarkers)
            ->  %writeln(all_true),%! all true
                undo((rrecurse:rformat('Undoing print_call1(~w,after_enter,~q,~q,~q)~n',
                            [N1,ClauseHeadNoModule,ClauseHead,GHVar]))),
                rrecurse:print_call1(N1,after_enter,BindCodes,
                                     ClauseHeadNoModule,
                                     ClauseHead, GHVar),
                TrackerVar0=[EC,_,BX,OC]-_,
                TrackerVar1=[EC,y,BX,OC]-StatusMarkers,
                put_assoc(N1,TrackerAssoc0,TrackerVar1,TrackerAssoc1),
                b_setval(TrackerName,TrackerAssoc1)
                %,writeln(updated_tracker_assoc)
            ;   true %!writeln(not_all_ready),
            )
        )
        %%%%%%%)% used to match the open paren before
        %%%%%%%%% b_getval(ClauseHeadName,ClauseHeadAssoc)
        %; true
        %( \+attvar(Val2)%!writeln(cant_find_parent)
        %  -> put_attr(AttrVar,rrecurse,AttrVal), %!writeln(val2_not_attvar),
        %     AttrVar=Val2 %!writeln(val2_is_attvar),
        %  ;  true
        %  )
        )
        ; true.

print_call1(N1,Mode,BindCodes,ClauseHeadNoModule,ClauseHead1,GHVar) :-
        (   unifiable(ClauseHeadNoModule,GHVar,Substs)
        ->  maplist([Codes1=Codes2,Atom1=Atom2]>>(atom_codes(Atom1,Codes1),atom_codes(Atom2,Codes2)),BindCodes,BindAtoms),%!writeln(can_unify),
            rrecurse:rformat('Hook substitutions: ~q, ~q~n',
                             [BindAtoms,Substs]),
            %rrecurse:rformat(
            %             'CHV: ~q, CH: ~q, CH1: ~q, GHVar: ~q~n',
            %             [ClauseHeadVar,ClauseHead,
            %              ClauseHead1,GHVar]),
            maplist([X=Y,XCodes=YCodes]>>(
                        write_term_to_codes(X,XCodes,[quoted(true)]),
                        write_term_to_codes(Y,YCodes,[quoted(true)])
                    ),Substs,SubstCodes0)
        ;   rrecurse:rformat(
                         'Cannot unify ~q with ~q.~n',
                         [ClauseHeadNoModule,GHVar]),
            SubstCodes0=[]%,writeln(cannot_unify)
        ), % End of unifiable(...) condition block
        append(BindCodes,SubstCodes0,SubstCodes),
        print_call(N1,Mode,ClauseHead1,[],SubstCodes).


                /*****************************
                *  PRINTING THE TRACE LINES  *
                *****************************/

rrcall_colors([
    [(black,   0, 0), (white, white)],
    [(black,   1, 1), (white, white)],
    [(cyan,    0, 0), (black, white)],
    [(blue,    1, 1), (white, white)],
    [(blue,    0, 0), (white, white)],
    [(magenta, 0, 0), (white, white)],
    [(red,     0, 0), (white, white)],
    [(red,     1, 1), (white, white)],
    [(yellow,  0, 1), (black, white)],
    [(green,   0, 0), (white, white)],
    [(green,   0, 1), (black, white)],
    [(cyan,    0, 1), (black, white)]
]).


%!  print_call(++CountName:atom,++Mode:atom,+Functor:callable,++Binds:list) is det.
%!  print_call(++CountName:atom,++Mode:atom,+Functor:callable,++Binds:list,++Binds1:list) is det.
%
%   Print call.

print_call(CountName,Mode,Functor,Binds) :-
        context_module(M),
        @(rrecurse:print_call(CountName,Mode,Functor,Binds,[]), M).
print_call(CountName,Mode,Functor,Binds,Binds1) :-
        (   Mode==before_exit
        ->  rrecurse:rformat('print_call: ~q, ~q, ~q, ~W~n',
                            [Mode,Functor,Binds,Binds1,[portray(true)]]),
            rrecurse:rformat('Functor: ~q, ', [Functor]),
            print_call_functor_fmt_args(Functor, PrintFmt, Args, Binds),
            rrecurse:rformat('Functor: ~q, ', [Functor]),
            format_to_codes(PrintFmt,Args,Codes),
            rrecurse:rformat('Codes: ~W~n', [Codes, [portray(true)]]),
            phrase(rrecurse:rr_replace(Binds1),Codes,Codes1)
        ;   true
        ),
        (   number(CountName)
        ->  N=CountName
        ;   b_getval(CountName,N)
        ),
        print_get_fmt(Mode,N,ColorFmt),
        (   once((Mode=after_enter ; Mode=before_exit ; Mode=before_fail))
        ->  TabDist1 is N
        ;   TabDist1 is N+1
        ),
        mytabc(4,TabDist1),
        print_call_mode_prefix(Mode,Prefix),
        (   Mode\==before_exit
        ->  rrecurse:rformat('print_call: ~q, ~q, ~q, ~W~n',
                            [Mode,Functor,Binds,Binds1,[portray(true)]]),
            rrecurse:rformat('Functor: ~q, ', [Functor]),
            print_call_functor_fmt_args(Functor, PrintFmt, Args, Binds),
            rrecurse:rformat('Functor: ~q, ', [Functor]),
            format_to_codes(PrintFmt,Args,Codes),
            rrecurse:rformat('Codes: ~W~n', [Codes, [portray(true)]]),
            phrase(rrecurse:rr_replace(Binds1),Codes,Codes1)
        ;   true
        ),
        !,
        atom_codes(Atom,Codes1),
        ansi_format(ColorFmt, Prefix, []),
	ansi_format(ColorFmt, Atom,[]),
        nl.
        %put(' '),
        %get_time(TimeStamp),
        %format_time(atom(TimeAtom),
        %            '[%H:%M:%S:%3f]',
        %           TimeStamp),
        %writeln(TimeAtom).



%! print_call_functor_fmt_args(+Functor, -Format, -Args, ++Binds) is det.
%! print_call_functor_fmt_args_(++Binds, +FunctorArgs, -FormatArgs) is det.
%! print_call_mode_prefix(+Mode:atom, -Prefix:atom) is nondet.
%
%  Unifies Args with the list of arguments (including write_term/2 - style
%  argument lists following each term, anticipating ~W) and unifies Format with
%  the format-atom that can be used to write the term used in invoking
%  the predicate.

print_call_functor_fmt_args(F, Form, [], Binds) :-
        (   \+callable(F) ; \+compound(F) ), !,
        %writeq(F),nl,%writeq(Binds),nl,
        format(atom(Form), '~|~W.',
               [F, [
                    ignore_ops,quoted,quote_non_ascii,
                    brace_terms(false),attributes(ignore),
                    variable_names(Binds)]]),
        !.
print_call_functor_fmt_args(Func,Form,Args,Binds) :-
        callable_name_arity_arguments(Func,Name,Arity,Args0),
        print_call_functor_fmt_args_(Binds,Args0,Args),
        %compound_name_arity(Func,Name,Arity),
        length(AList,Arity),
        maplist(=('~t~4+~|~W'), AList),
        atomic_list_concat(AList,',',ArgsFormatAtom),
        format(atom(Form), '~|~w( ~a ).', [Name,ArgsFormatAtom]), !.

print_call_functor_fmt_args_(_,[],[]) :- !.
print_call_functor_fmt_args_(Binds, [A|Args0],
                             [A|[[variable_names(Binds),ignore_ops(true),
                                  quoted(true), quote_non_ascii(true),
                                  brace_terms(false),attributes(ignore)
                                 ]|Args]
                             ]) :-
        print_call_functor_fmt_args_(Binds, Args0, Args), !.

print_call_mode_prefix(pre_call, '~|>>>~tCALLING~1+ ').
print_call_mode_prefix(post_call, '~|<<<~tCALLED~1+ ').
print_call_mode_prefix(after_enter, '> ').
print_call_mode_prefix(before_exit, '< ').
print_call_mode_prefix(before_fail, '##').


%! print_get_fmt(++Mode:atom, ++Depth:int, -ColorFmt:list) is det.
%! print_get_mode_fmt(++Mode:atom, +Spec, -ColorFmt:list) is det.
%
%  Based on the Mode and the indentation Depth, unifies ColorFmt with a
%  suitable list of options understood by ansi_term:ansi_format/3.
%
%  print_get_fmt/3 selects spec number N (with modulus) from the list
%  of depth color-schemes obtained via rrcall_colors/1. These specifications
%  in the future will be highly customizable, as work has already been
%  done to implement support for several rather flexible types of
%  color-scheme specification (still, as of yet, limited to the
%  handful of ANSI colors supported by the ansi_term module).

print_get_fmt(Mode, N, ColorFmt) :-
        rrcall_colors(Colors),
        length(Colors,L),
        NN is mod(N,L),
        nth0(NN, Colors, [Spec1, Spec2]),
        print_get_fmt_(Mode,Spec1,Spec2,ColorFmt), !.

print_get_mode_fmt(Mode,[Spec1,Spec2], ColorFmt) :-
        print_get_fmt_(Mode, Spec1, Spec2, ColorFmt), !.
print_get_mode_fmt(Mode, Spec, ColorFmt) :-
        print_get_fmt_(Mode, Spec, Spec, ColorFmt), !.

print_get_fmt_(Mode,(C1,HF1,HB1),(C2F,C2B), ColorFmt):-
        (   C2F = white
        ->  C2FH = 1
        ;   C2FH = 0
        ),
        (   C2B = white
        ->  C2BH = 1
        ;   C2BH = 0
        ),
        (   once((Mode=after_enter ; Mode=before_exit ; Mode=before_fail))
        ->  print_get_fmt__(C2F,C2FH,C1,HB1,ColorFmt)
        ;   print_get_fmt__(C1,HF1,C2B,C2BH,ColorFmt)
        ), !.
print_get_fmt_(Mode,(C1,HF1,HB1),(C2,HF2,HB2), ColorFmt):-
        (   once((Mode=after_enter ; Mode=before_exit ; Mode=before_fail))
        ->  print_get_fmt__(C2,HF2,C1,HB1,ColorFmt)
        ;   print_get_fmt__(C1,HF1,C2,HB2,ColorFmt)
        ), !.

print_get_fmt_(Mode,(C1,HF1,HB1),(C2F,HF2,C2B,HB2), ColorFmt):-
        (   once((Mode=after_enter ; Mode=before_exit ; Mode=before_fail))
        ->  print_get_fmt__(C2F,HF2,C1,HB1,ColorFmt)
        ;   print_get_fmt__(C1,HF1,C2B,HB2,ColorFmt)
        ), !.

print_get_fmt__(FColor, 1, BColor, 1, [hfg(FColor), hbg(BColor)]).
print_get_fmt__(FColor, 1, BColor, 0, [hfg(FColor), bg(BColor)]).
print_get_fmt__(FColor, 0, BColor, 1, [fg(FColor), hbg(BColor)]).
print_get_fmt__(FColor, 0, BColor, 0, [fg(FColor), bg(BColor)]).

mytabc(N) :- mytabc(1,N).
mytabc(Size,N) :-
        mytabc('|','-',rr,Size,N).
mytabc(ColorFmt,Size,N) :-
        mytabc('|','-',ColorFmt,Size,N).
mytabc(LeadChar,ColorFmt,Size,N) :-
	mytabc('|',LeadChar,ColorFmt,Size,N).
%mytabc(AlignChar,LeadChar,ColorFmt,1,N) :-
%	N > 1, !,
%	mytabc(AlignChar,LeadChar,ColorFmt,N,1).
mytabc(AlignChar,LeadChar,ColorFmt,Size,N) :-
	TabAmt is Size - 1,
	mytabc_(TabAmt,Size,AlignChar,LeadChar,ColorFmt,N).

mytabc_(TabAmt,Size,AlignChar,LeadChar,rr,N) :-
        !,
        rrcall_colors(ColorFmts),
        mytabc_(ColorFmts, ColorFmts, TabAmt, Size, AlignChar, LeadChar, rr, 1, N).
mytabc_(TabAmt,Size,AlignChar,LeadChar,ColorFmt,N) :-
	mytabc_([],[],TabAmt,Size,AlignChar,LeadChar,ColorFmt,1,N).

mytabc_(_,_,_,_,_,_,_,N0,N) :-
	N0 > N, !.
mytabc_(FmtList,List0,0,Size,AlignChar,LeadChar,ColorFmt0,N0,N) :-
	!,
        mytabc_get_fmt(ColorFmt0,FmtList,List0,ColorFmt,List1),
        ansi_format(ColorFmt,'~w',AlignChar),%write(AlignChar),
	N1 is N0 + 1,
	mytabc_(FmtList,List1,0,Size,AlignChar,LeadChar,ColorFmt0,N1,N).
mytabc_(FmtList,List0,1,Size,AlignChar,LeadChar,ColorFmt0,N0,N) :-
	!,
        mytabc_get_fmt(ColorFmt0,FmtList,List0,ColorFmt,List1),
	ansi_format(ColorFmt,'~w~w',[AlignChar,LeadChar]),
	N1 is N0 + 1,
	mytabc_(FmtList,List1,1,Size,AlignChar,LeadChar,ColorFmt0,N1,N).
mytabc_(FmtList,List0,TabAmt,Size,AlignChar,LeadChar,ColorFmt0,N0,N) :-
	TabAmt > 1, !,
	atomic_list_concat(['~|',AlignChar,
                            LeadChar,'~`',LeadChar,'t~',
                            TabAmt,'+',LeadChar],Fmt),
        mytabc_get_fmt(ColorFmt0,FmtList,List0,ColorFmt,List1),
        ansi_format(ColorFmt,Fmt,[]),
	N1 is N0 + 1,
	mytabc_(FmtList,List1,TabAmt,Size,AlignChar,LeadChar,ColorFmt0,N1,N).
mytabc_(_,_,_,_,_,_,_,_,_) :- !. %% TODO: warning?

mytabc_get_fmt(rr, _,[NthSpec|T], Fmt,T) :-
        !, print_get_mode_fmt(after_enter,NthSpec,Fmt).
mytabc_get_fmt(rr, FmtList,[NthSpec], Fmt, FmtList) :-
        !, print_get_mode_fmt(after_enter,NthSpec,Fmt).
%%mytabc_get_fmt(FmtSpec//Mode, [], [], Fmt, [], []). %% TODO
mytabc_get_fmt(Fmt, [],[], Fmt, []) :- !.



                /*****************************
                *  SUBTERM FIND-AND-REPLACE  *
                *****************************/

% ?- subst_subterm((mypred(arg1,Arg2),wrapper(mypred(Arg1,arg2))), mypred(A1,A2), mypred(A1,A2,arg3), Skeleton, Substitutions).
subst_subterm(Term, Templates, Skeleton) :-
    rb_new(Map0),
    add_map(Term, Map0, Map),
    rb_visit(Map, Counts),
    matching_terms(Templates, Counts, Matches),
    !,
    ord_list_to_rbtree(Matches,MatchAssoc),
    insert_vars(Term,Skeleton,MatchAssoc).

subst_subterm(Term, FindTemplate, ReplaceTemplate, Skeleton) :-
    rb_new(Map0),
    add_map(Term, Map0, Map),
    rb_visit(Map, Counts),
    matching_terms(FindTemplate,ReplaceTemplate, Counts, Matches),
    !,
    ord_list_to_rbtree(Matches,MatchAssoc),
    insert_vars(Term,Skeleton,MatchAssoc).


add_map(Term, Map0, Map) :-
    (   primitive(Term)
    ->  Map = Map0
    ;   rb_update(Map0, Term, Old, New, Map)
    ->  New is Old+1
    ;   rb_insert(Map0, Term, 1, Map1),
        assoc_arg_map(1, Term, Map1, Map)
    ).

assoc_arg_map(I, Term, Map0, Map) :-
    arg(I, Term, Arg),
    !,
    add_map(Arg, Map0, Map1),
    I2 is I + 1,
    assoc_arg_map(I2, Term, Map1, Map).
assoc_arg_map(_, _, Map, Map).

primitive(Term) :-
    var(Term),
    !.
primitive(Term) :-
    atomic(Term),
    !.
primitive('$VAR'(_)).

common_terms([], []).
common_terms([H-Count|T], List) :-
    !,
    (   Count == 1
    ->  common_terms(T, List)
    ;   List = [H-_NewVar|Tail],
        common_terms(T, Tail)
    ).


matching_terms(_, [], []).
matching_terms(Templates, [H-_|T], List) :-
        !,
        %freeze(H, once((FTemplate=@=H ; subsumes_term(FTemplate,H)))),
        (   once((member([FTemplate,RTemplate],Templates),
                  (   (FTemplate=@=H ; subsumes_term(FTemplate,H)))))
        ->  List = [H-R|LTail],
            %Binds = [Bs|BTail],
            sub_term_shared_variables(FTemplate,RTemplate,SharedVars),
            copy_term(SharedVars,[FTemplate,RTemplate],_NewVars,[H,R]),

            (   subsumes(RTemplate,R)
            %;   subsumes(RTemplate,R)
            ),
            matching_terms(FTemplate,RTemplate, T, LTail)
        ;   matching_terms(Templates, T, List)
        ).


matching_terms(_, _, [], []).
matching_terms(FTemplate, RTemplate, [H-_|T], List) :-
        !,
        (   \+once((FTemplate=@=H ; subsumes_term(FTemplate,H)))
        ->  matching_terms(FTemplate,RTemplate, T, List)
        ;   List = [H-R|LTail],
            %Binds = [Bs|BTail],
            sub_term_shared_variables(FTemplate,RTemplate,SharedVars),
            copy_term(SharedVars,RTemplate,_NewVars,R),

            subsumes(R,RTemplate),
            matching_terms(FTemplate,RTemplate, T, LTail)
        ).

insert_vars(T0, T, _) :-
    primitive(T0),
    !,
    T = T0.
insert_vars(T0, T, Subst) :-
    rb_lookup(T0, S, Subst),
    !,
    T = S.
insert_vars(T0, T, Subst) :-
    functor(T0, Name, Arity),
    functor(T,  Name, Arity),
    insert_arg_vars(1, T0, T, Subst).

insert_arg_vars(I, T0, T, Subst) :-
    arg(I, T0, A0),
    !,
    arg(I, T,  A),
    insert_vars(A0, A, Subst),
    I2 is I + 1,
    insert_arg_vars(I2, T0, T, Subst).
insert_arg_vars(_, _, _, _).
mk_subst([], [], _).
mk_subst([Val0-Var|T0], [Var=Val|T], Subst) :-
    functor(Val0, Name, Arity),
    functor(Val,  Name, Arity),
    insert_arg_vars(1, Val0, Val, Subst),
    mk_subst(T0, T, Subst).



                 /**********************
                 *        RWRITE       *
                 **********************/

%! rwrite_on is det.
%! rwrite_off is det.
%
%  Enable or disable rwrite (via set_flag/2, so affects all threads).

rwrite_on :- set_flag(rwrite,1).
rwrite_off :- set_flag(rwrite,0).


%! rwrite(+Term) is det.
%! rwriteln(+Term) is det.
%
%  Flag-dependent (see `rwrite_on/0`, `rwrite_off/0`) versions of `write/1`
%  and `writeln/1`.

%rwriteln(_,_) :- get_flag(rwrite,0), !.
%rwriteln(N,X) :- M is N*2, format(atom(A),'~~|~~`.t~~~w|~w@~w~n',[M,N,X]),format(A, []).
rwriteln(_) :- get_flag(rwrite,0), !.
rwriteln(X) :- writeln(X).
rwrite(_) :- get_flag(rwrite,0), !.
rwrite(X) :- write(X).



%! rwriteq(+Term) is det.
%! rwriteqln(+Term) is det.
%
%  Flag-dependent (see `rwrite_on/0`, `rwrite_off/0`) _and quoted_ versions
%  of `write/1` and `writeln/1`.
%
%  ``rwriteq/1`` can also be understood as a flag-dependent version of
%  `writeq/1`.

rwriteq(_) :- get_flag(rwrite,0), !.
rwriteq(X) :- writeq(X).
rwriteqln(_) :- get_flag(rwrite,0), !.
rwriteqln(X) :- writeq(X),nl.


%! rformat(+Format, +Args) is det.
%! rformat(++Stream, +Format, +Args) is det.
%
%  Flag-dependent (see `rwrite_on/0`, `rwrite_off/0`) versions of
%  `format/2` and `format/3`.

rformat(_,_) :- get_flag(rwrite,0), !.
rformat(Format,Args) :- format(Format,Args).
rformat(_,_,_) :- get_flag(rwrite,0), !.
rformat(Stream,Format,Args) :- format(Stream,Format,Args).


                /*****************
                * MISC UTILITIES *
                *****************/

%! term_shared_variables(?Term1,?Term2,-Variables) is det.
%
%  Like occurs:sub_term_shared_variables/3, but Term1 is not
%  necessarily a sub-term of Term1.

term_shared_variables(Term1,Term2,Vars) :-
        term_variables(Term1,Vars1),
        term_variables(Term2,Vars2),
        occurs:intersection_eq(Vars1,Vars2,Vars).


%! rr_replace(+Binds)// is det.

rr_replace(_) --> \+[_], !.
rr_replace(Binds), PrintValue -->
        [H],
        {member([H|Rest]=PrintValue,Binds)},
        Rest,
        !,
        rr_replace(Binds).
rr_replace(Binds), [C] -->
        [C],
        !,
        rr_replace(Binds).

%rr_replace_test(Old,New) :-
%        write_term_to_codes(Old,OldCodes,[]),
%        Binds = [`123`=`456`,`abc`=`def`,`ghi`=`jkl`],
%        phrase(rrecurse:rr_replace(Binds),OldCodes,NewCodes),
%        read_term_from_codes(NewCodes,New,[]).


%! callable_name_arity_arguments(?Callable, ?Name, ?Arity, ?Args) is nondet.
%
%  A combination of compound_name_arguments and compound_name_arity that can
%  also handle non-compound callables (i.e., atomics). Unlike functor/3,
%  however, it also accepts zero-arity compound terms without error.
%
%  Note that when generating a zero-arity callable from name and arity (or
%  when Args is bound to the empty list), this predicate will aim to unify
%  Callable with an atom (rather than a zero-arity compound term).

callable_name_arity_arguments(Callable,Name,Arity,Args) :-
        nonvar(Callable),
        Callable = _:Head, !,
        callable_name_arity_arguments(Head,Name,Arity,Args).
callable_name_arity_arguments(Callable, Name, Arity, Args) :-
        once((var(Callable) ; must_be(callable,Callable))),
        (    ( nonvar(Callable)
             ->  \+atom(Callable)
             ;   \+((Arity==0 ; Args==[]))
               )
        ->
             length(Args,Arity),
             (   Arity=0
             ->  Callable=..[Name|Args]
             ;   compound_name_arity(Callable,Name,Arity),
                 compound_name_arguments(Callable,Name,Args)
             )
        ;   Name=Callable, Arity=0, Args=[]
        ).


%! callable_name_arguments(?Callable, ?Name, ?Arguments) is semidet.
%
%  Should be reworked or replaced by `callable_name_arity_arguments/4`.

callable_name_arguments(Callable0, Name, Arguments) :-
        nonvar(Callable0), Callable0=_:Callable,
        !,
        callable_name_arguments(Callable,Name,Arguments).
callable_name_arguments(Callable,Name,Arguments) :-
        atomic(Callable), !,
        Name=Callable,
        Arguments=[], !.
callable_name_arguments(Callable,Name,Arguments) :-
        (   nonvar(Callable)
        ->  must_be(callable,Callable)
        ;   must_be(atomic,Name),
            must_be(nonvar,Name)
        ),
        compound_name_arguments(Callable,Name,Arguments).







                 /**********************
                 *   EXPANSION HOOKS   *
                 **********************/
%user:expand_query(Goal,Goal,Binds,Binds) :-
%        Binds\==[], write('BINDS: '), writeq(Binds),nl,fail.


user:expand_query(rrcall(Goal), (notrace(most_general_goal(Goal, Template)), rrcall(Goal, Template, Binds)), Binds, Binds) :-
        !, rwrite('Expanding rrcall/1. '), rwriteqln(Binds).
user:expand_query(rrcall(Goal,Template),
                  rrcall(Goal,Template,Binds), Binds, Binds) :- !,
        rwrite('Expanding rrcall/2. '), rwriteqln(Binds).
user:expand_query(Query0, Query1, Binds, Binds) :-
        once((contains_term(Query0,rrcall(_)) ;
        contains_term(Query0,rrcall(_,_)))),
        (   Binds = []
        ->  Query1=Query0
        ;   rwriteqln(Binds)
        ),
        subst_subterm(
            Query0,
            [[rrecurse:rrcall(A1),
              (notrace(context_module(M)),
               rrecurse:rrcall_(M,A1,Binds))],
             [rrcall(A1),
              (notrace(most_general_goal(A1,A2)),
               rrcall(A1,A2,Binds))],
             [rrecurse:rrcall(A1,A2),
              (notrace(context_module(M)),
               rrecurse:rrcall_(M,A1,A2,Binds))],
             [rrcall(A1,A2),
              rrcall(A1,A2,Binds)]],
            Query1),
        !.
