open HolKernel bossLib boolLib EmitTeX
open bytecode_emitTheory extended_emitTheory basis_emitTheory
open CompilerLibTheory CompilerPrimitivesTheory IntLangTheory ToIntLangTheory ToBytecodeTheory CompilerTheory PrinterTheory compilerTerminationTheory
val _ = new_theory "compile_emit"

val _ = Parse.temp_type_abbrev("set",``:'a -> bool``)
val _ = Parse.temp_type_abbrev("string",``:char list``)
val _ = Parse.temp_type_abbrev("op_",``:op``) (* EmitML should do this *)
val _ = Parse.disable_tyabbrev_printing "tvarN"
val _ = Parse.disable_tyabbrev_printing "envE"
val _ = Parse.disable_tyabbrev_printing "store"
val _ = Parse.disable_tyabbrev_printing "type_def"
val _ = Parse.disable_tyabbrev_printing "ccenv"
val _ = Parse.disable_tyabbrev_printing "ctenv"
val _ = Parse.disable_tyabbrev_printing "ceenv"
val _ = Parse.disable_tyabbrev_printing "alist"
val _ = Parse.disable_tyabbrev_printing "def"
val _ = Parse.disable_tyabbrev_printing "contab"
val _ = Parse.hide "toList"
val _ = Feedback.set_trace "Greek tyvars" 0 (* EmitML should do this *)

val underscore_rule = Conv.CONV_RULE let
fun foldthis (tm,(ls,n)) = let
  val (nm,_) = Term.dest_var tm
in if String.sub(nm,0) = #"_" then (("us"^(Int.toString n))::ls,n+1) else (nm::ls,n) end in
Conv.TOP_SWEEP_CONV
  (fn tm => let
     val (vs, _) = Term.strip_binder NONE tm
     val (vs,n) = List.foldr foldthis ([],0) vs
   in if n = 0 then raise Conv.UNCHANGED else Conv.RENAME_VARS_CONV vs tm end)
end

fun fix_compile_bindings_suc th = let
  val ([lz,ls],cs) = List.partition (equal``compile_bindings``o fst o strip_comb o lhs o snd o strip_forall o concl) (CONJUNCTS th)
  val (l,rz) = dest_eq (snd (strip_forall (concl lz)))
  val rs = rator (rhs (snd (strip_forall (concl ls))))
  val n = mk_var("m",``:num``)
  val th = GEN_ALL (mk_thm([],mk_eq(mk_comb(rator l,n),mk_cond(mk_eq(n,numSyntax.zero_tm),rz,mk_comb(rs,numSyntax.mk_pre n)))))
  in LIST_CONJ(th::cs) end

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
  [ AstTheory.datatype_lit
  , AstTheory.datatype_error
  , AstTheory.datatype_opb
  , AstTheory.datatype_opn
  , AstTheory.datatype_op
  , AstTheory.datatype_uop
  , AstTheory.datatype_lop
  , AstTheory.datatype_id
  , AstTheory.datatype_pat
  , AstTheory.datatype_exp
  , SemanticPrimitivesTheory.datatype_v
  , AstTheory.datatype_tc0
  , AstTheory.datatype_t
  , AstTheory.datatype_dec
  , datatype_Cprim1
  , datatype_Cprim2
  , datatype_Cpat
  , datatype_ccbind
  , datatype_ctbind
  , datatype_Cexp
  , datatype_exp_to_Cexp_state
  , datatype_call_context
  , datatype_compiler_result
  , datatype_compiler_state
  , datatype_ov
  ]

val defs = map EmitML.DEFN
[ mk_thm([],``SET_TO_LIST s = toList s``)
, alistTheory.alist_to_fmap_def
, Cpat_vars_def
, lunion_def
, lshift_def
, the_def
, free_vars_def
, emit_def
, i0_def
, i1_def
, i2_def
, mkshift_def
, shift_def
, cbv_def
, cmap_def
, etC_def
, error_to_int_def
, get_label_def
, compile_envref_def
, compile_varref_def
, pushret_def
, prim1_to_bc_def
, prim2_to_bc_def
, find_index_def
, emit_ceref_def
, emit_ceenv_def
, bind_fv_def
, num_fold_def
, label_closures_def
, push_lab_def
, underscore_rule cons_closure_def
, update_refptr_def
, underscore_rule compile_closures_def
, fix_compile_bindings_suc (underscore_rule compile_def)
, free_labs_def
, cce_aux_def
, compile_code_env_def
, calculate_labels_def
, replace_labels_def
, compile_labels_def
, init_compiler_state_def
, pat_to_Cpat_def
, remove_mat_vp_def
, underscore_rule remove_mat_var_def
, underscore_rule exp_to_Cexp_def
, compile_Cexp_def
, number_constructors_def
, AstTheory.pat_bindings_def
, compile_shadows_def
, compile_news_def
, compile_fake_exp_def
, compile_dec_def
, id_to_string_def
, LibTheory.lookup_def
, v_to_ov_def
, bv_to_ov_def
, cpam_def
]

val num_to_bool = prove(
``num_to_bool n <=> n <> 0``,
Cases_on `n` THEN SRW_TAC[][num_to_bool_def])

val _ = EmitML.eSML "compile" (
  (EmitML.OPEN ["num","fmap","set","sum","bytecode","sorting"])
::(EmitML.MLSIG "type num = numML.num")
::(EmitML.MLSIG "type int = intML.int")
::(EmitML.MLSTRUCT "type int = intML.int")
::(EmitML.MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::(EmitML.MLSIG "type 'a set = 'a setML.set")
::(EmitML.MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum")
::(EmitML.MLSIG "type bc_stack_op = bytecodeML.bc_stack_op")
::(EmitML.MLSIG "type bc_inst = bytecodeML.bc_inst")
::(EmitML.MLSIG "type bc_value = bytecodeML.bc_value")
::(EmitML.MLSIG "val num_to_bool : num -> bool")
::(EmitML.DEFN_NOSIG num_to_bool)
::data@defs)

val _ = export_theory ();
