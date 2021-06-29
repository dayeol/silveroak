Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.TailRecursion.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Z.Lia.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.LibBase.Bitfield.

Require Import coqutil.Map.SortedListString.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Module parameters.
  Class parameters :=
    { word :> Interface.word.word 32;
      mem :> Interface.map.map word Byte.byte;
      ext_spec : list
    (mem * string * list word *
     (mem * list word)) ->
  mem ->
  string ->
  list word ->
  (mem -> list word -> Prop) -> Prop
    }.
  Class ok (p : parameters) :=
    {  word_ok :> word.ok word;
      mem_ok :> Interface.map.ok mem;
    }.
End parameters.
Notation parameters := parameters.parameters.

Section Proof.
  Context {p : parameters} {p_ok : parameters.ok p}.


  Global Instance semantics_parameters : Semantics.parameters :=
  {|
    Semantics.width := 32;
    Semantics.word := parameters.word;
    Semantics.mem := parameters.mem;
    Semantics.locals := SortedListString.map _;
    Semantics.env := SortedListString.map _;
    Semantics.ext_spec := parameters.ext_spec;
  |}.

  Existing Instance semantics_parameters.
  Check (_ : Semantics.parameters).


  Global Instance spec_of_bitfield_bit32_read : spec_of "b2_bitfield_bit32_read"
  := fun function_env =>
    forall (field : parameters.word) (index: parameters.word) (R : _ -> Prop) (m : mem) (t : trace),
      R m /\
      call function_env bitfield_bit32_read t m [field; index]
        (fun t' m' rets =>
          t = t' /\ m = m' /\ exists v, rets = [v] /\
          (word.unsigned v = word.unsigned field)
        ).

  Check (_ : spec_of "b2_bitfield_bit32_read").

  Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
  Local Notation functions_t := (list function_t).

  Ltac program_logic_goal_for_function proc ::=
  fail 1000 "debugg";
  let __ := constr:(proc : function_t) in
  let fname := eval cbv in (fst proc) in
  let callees := eval cbv in (callees (snd (snd proc))) in
  idtac fname;
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t, ltac:(
    let s := assuming_correctness_of_in callees functions (spec (cons proc functions)) in
    exact s)).
  Set Ltac Backtrace.
  Check spec_of.
  Check spec_of "b2_bitfield_bit32_read".
  Set Printing Implicit.
  Check program_logic_goal_for_function! bitfield_bit32_read.
  Lemma bitfield_bit32_read_correct :
    program_logic_goal_for_function! bitfield_bit32_read.

End Proof.
