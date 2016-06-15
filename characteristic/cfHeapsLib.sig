signature cfHeapsLib =
sig
  include Abbrev

  (* Prove an "easy" goal about sets, involving UNION, DISJOINT,... Useful
    after unfolding the definitions of heap predicates. *)
  val SPLIT_TAC : tactic


  (** Normalization of STAR *)

  (* Normalize modulo AC of STAR *)
  val rew_heap_AC : tactic

  (* Normalize using AC, but also pull exists, remove emp, etc. *)
  val rew_heap : tactic


  (** Making progress on goals of the form [H1 ==>> H2].

      The main tactic one wants to use faced with such a goal is [hsimpl].

      It will normalize both heaps, extract pure formulæ ([cond]), extract and
      instantiate existential quantifications from H1 and H2, and remove
      subheaps present both in H1 and H2.

      [hsimpl_conseq_conv] fails if the input term is not of the form
      ``_ ==>> _ `` or ``_ ==+> _``. Otherwise, it returns UNCHANGED if there
      is nothing to do.

      [hsimpl] applies [hsimpl_conseq_conv] on every subterm of the goal on
      which it doesn't fail, that is on every [SEP_IMP] and [SEP_IMPPOST].
   *)
  val hsimpl : tactic
  val hsimpl_conseq_conv : ConseqConv.directed_conseq_conv


  (** Auxiliary directed_conseq_convs, that are used to implement
      [hsimpl_conseq_conv] and [hsimpl]. *)

  (* [hpull_conseq_conv]: extract pure facts and existential quantifications
     from the left heap (H1).

     For example: On term ``(A * cond P) ==>> B``, [hpull_conseq_conv] returns a
     conseq conv to convert it to ``P ==> (A ==>> B)``.

     On term ``(SEP_EXISTS x. A x * B) ==>> C``, the returned conseq_conv
     allows to convert it to ``!x. (A x * B) ==>> C``.
     
     [hpull_conseq_conv] fails if the goal is not of the form ``_ ==>> _``. If
     the goal is of this form but there is nothing to pull, UNCHANGED is raised.
   *)
  val hpull_conseq_conv : ConseqConv.directed_conseq_conv
                 
  (* [hsimpl_cancel_conseq_conv]: on a goal of the form [H1 ==>> H2],
     [hsimpl_cancel_conseq_conv] tries to remove subheaps present both in H1 and
     H2. Moreover, if [one (loc, v)] is in H1 and [one (loc, v')] is in H2,
     [hsimpl_cancel] will remove both, and produce an assumption [v = v'].

     For example, [hsimpl_cancel_conseq_conv] generates a conversion from 
     ``(A * B * one (l, v)) ==>> (B * one (l, v'))`` to
     ``v = v' ==> (A ==>> emp)``.

     [hsimpl_cancel_conseq_conv] fails if the goal is not of the form
     ``_ ==>> _``. If the goal is of this form does but there is nothing to do,
     UNCHANGED is raised.
   *)
  val hsimpl_cancel_conseq_conv : ConseqConv.directed_conseq_conv

  (* [hsimpl_steps]: extract pure facts and existential quantifications from the
     right heap (H2).

     For example, `` A ==>> (B * cond P)`` gets converted to
     ``P /\ A ==>> B``.

     [hsimpl_steps_conseq_conv] fails if the goal is not of the form
     ``_ ==>> _``. If the goal is of this form but there is nothing to do,
     UNCHANGED is raised.
   *)
  val hsimpl_steps_conseq_conv : ConseqConv.directed_conseq_conv
end