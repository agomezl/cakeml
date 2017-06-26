structure ioProgLib =
struct

open preamble
open ml_progLib ioProgTheory semanticsLib helperLib

val hprop_heap_thms =
  ref [
    emp_precond,
    mlcharioProgTheory.STDOUT_precond,
    mlcharioProgTheory.STDERR_precond,
    mlcharioProgTheory.STDIN_T_precond,
    mlcharioProgTheory.STDIN_F_precond,
    mlcommandLineProgTheory.COMMANDLINE_precond,
    mlfileioProgTheory.ROFS_precond];

fun mk_main_call s =
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;

val basis_ffi_const = prim_mk_const{Thy="ioProg",Name="basis_ffi"};
val basis_ffi_tm =
  list_mk_comb(basis_ffi_const,
    map mk_var
      (zip ["inp","cls","files"]
        (#1(strip_fun(type_of basis_ffi_const)))))

(* TODO: move *)
val STDOUT_tm = prim_mk_const{Thy="mlcharioProg",Name="STDOUT"}
fun mk_STDOUT x = mk_comb (STDOUT_tm,x)
fun dest_STDOUT x = snd (assert (same_const STDOUT_tm o fst) (dest_comb x))
val is_STDOUT = can dest_STDOUT
val STDERR_tm = prim_mk_const{Thy="mlcharioProg",Name="STDERR"}
fun mk_STDERR x = mk_comb (STDERR_tm,x)
fun dest_STDERR x = snd (assert (same_const STDERR_tm o fst) (dest_comb x))
val is_STDERR = can dest_STDERR
val (UNIT_TYPE_tm,mk_UNIT_TYPE,dest_UNIT_TYPE,is_UNIT_TYPE) = syntax_fns2 "ml_translator" "UNIT_TYPE"
val cond_tm = set_sepTheory.cond_def |> SPEC_ALL |> concl |> lhs |> rator
fun dest_cond x = snd (assert (same_const cond_tm o fst) (dest_comb x))
(* -- *)

fun ERR f s = mk_HOL_ERR"ioProgLib" f s

(*  Given a spec, normalise it if possible into the form required for
    call_main_thm_basis, namely:
    app (basis_proj1,basis_proj2) fv [Conv NONE []] P
      (POSTv uv. &UNIT_TYPE () uv * (SEP_EXISTS x y. &R x y * STDOUT x * STDERR y) * Q)
    TODO: could be more robust
examples:
  val spec = mk_thm([],
    ``app p fv [uv] (STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs)
       (POSTv v.  &UNIT_TYPE () v * STDOUT (out ++ foo cl fs)
                   * STDERR (out ++ bar cl fs)
                   * (COMMANDLINE cl * ROFS fs))``)
    |> add_basis_proj
  val spec = mk_thm([],
    ``app p fv [Conv NONE []] (ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err)
      (POSTv uv. &UNIT_TYPE () uv *
          (SEP_EXISTS out' error.
            &(∃output err_msg. out' = out ++ output ∧ error = err ++ err_msg ∧
              foo output fs cl err_msg) * STDOUT out' * STDERR error) *
          (ROFS fs * COMMANDLINE cl))``)
    |> add_basis_proj
  val spec =
    mk_thm([],``app p fv [Conv NONE []] (STDOUT output) (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ bar))``)
    |> add_basis_proj
  val spec =
    mk_thm([],``app p fv [Conv NONE []] (STDOUT s * STDERR []) (POSTv uv. &UNIT_TYPE () uv * STDOUT s * STDERR bar)``)
    |> add_basis_proj
*)
fun add_basis_proj spec =
  let
    val (proj,fv,args,precond,postcond) = spec |> concl |> cfAppSyntax.dest_app
    val (v,hprop) = cfHeapsBaseSyntax.dest_postv postcond
    val hprops = list_dest dest_star hprop
    val (stdouts,hprops) = partition is_STDOUT hprops
    val (stderrs,hprops) = partition is_STDERR hprops
    fun is_cond_UNIT_TYPE x = aconv v (snd (dest_UNIT_TYPE (dest_cond x))) handle HOL_ERR _ => false
    val (unitvs,hprops) = partition is_cond_UNIT_TYPE hprops
    val (sepexists, hprops) = partition (can dest_sep_exists) hprops
    val star_type = type_of precond
    val rest_hprop = list_mk_star hprops star_type
    val post = list_mk_star (unitvs@stdouts@stderrs@sepexists@[rest_hprop]) star_type
    val (argv,argty) = listSyntax.dest_list args
    val (arg_vars,args_goal) =
      if List.null argv orelse
         not (List.null (List.tl argv))
      then raise ERR "add_basis_proj" "must have exactly one argument"
      else if List.all is_var argv then (argv, ``[Conv NONE []]``)
      else ([],args)
    val goal =
      cfAppSyntax.mk_app(proj,fv,args_goal,precond,cfHeapsBaseSyntax.mk_postv(v,post))
    val lemma = prove(goal,
      mp_tac (GENL arg_vars spec)
      \\ simp_tac(bool_ss)[set_sepTheory.SEP_CLAUSES]
      \\ simp_tac (std_ss++star_ss) [])
    val spec1 = if List.null stderrs andalso not (List.null stdouts) then
                HO_MATCH_MP append_STDERR lemma else lemma
    val spec2 = HO_MATCH_MP append_SEP_EXISTS spec1 handle HOL_ERR _ => spec1
  in
      spec2 |> Q.GEN`p` |> Q.ISPEC`(basis_proj1, basis_proj2)`
  end

(*This function proves that for a given state, parts_ok holds for the ffi and the basis_proj2*)
fun parts_ok_basis_st st =
  let val goal = ``parts_ok ^st.ffi (basis_proj1, basis_proj2)``
  val th = prove(goal,
    qmatch_goalsub_abbrev_tac`st.ffi`
    \\ `st.ffi.oracle = basis_ffi_oracle`
    by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
    \\ rw[cfStoreTheory.parts_ok_def]
    \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
    \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
    \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
    \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
    \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
    \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
    \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
    \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
    \\ TRY pairarg_tac \\ fs[]
    \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
    \\ srw_tac[DNF_ss][])
  in th end

(* This function proves the SPLIT pre-condition of call_main_thm_basis *)
fun subset_basis_st st precond =
  let
  val hprops = precond |>  helperLib.list_dest helperLib.dest_star
  fun match_and_instantiate tm th =
    INST_TY_TERM (match_term (rator(concl th)) tm) th
  fun find_heap_thm hprop =
    Lib.tryfind (match_and_instantiate hprop) (!hprop_heap_thms)
    handle HOL_ERR _ => raise(ERR"subset_basis_st"
                                 ("no hprop_heap_thm for "^Parse.term_to_string(hprop)))
  val heap_thms = List.map find_heap_thm hprops
  fun build_set [] = raise(ERR"subset_basis_st""no STDOUT in precondition")
    | build_set [th] = th
    | build_set (th1::th2::ths) =
        let
          val th = MATCH_MP append_hprop (CONJ th1 th2)
          val th = CONV_RULE(LAND_CONV EVAL)th
          val th = MATCH_MP th TRUTH
          val th = CONV_RULE(RAND_CONV (pred_setLib.UNION_CONV EVAL)) th
        in build_set (th::ths) end
  val sets_thm = build_set heap_thms
  val (precond',sets) = dest_comb(concl sets_thm)
  val precond_rw = prove(mk_eq(precond',precond),SIMP_TAC (pure_ss ++ helperLib.star_ss) [] \\ REFL_TAC)
  val sets_thm = CONV_RULE(RATOR_CONV(REWR_CONV precond_rw)) sets_thm
  val to_inst = free_vars sets
  val goal = pred_setSyntax.mk_subset(sets,st)
  val pok_thm = parts_ok_basis_st (rand st)
  val tac = (strip_assume_tac pok_thm
     \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           cfStoreTheory.Mem_NOT_IN_ffi2heap, cfStoreTheory.ffi2heap_def]
     \\ EVAL_TAC \\ rw[INJ_MAP_EQ_IFF,INJ_DEF,FLOOKUP_UPDATE])
  val (subgoals,_) = tac ([],goal)
  fun mk_mapping (x,y) =
    if mem x to_inst then SOME (x |-> y) else
    if mem y to_inst then SOME (y |-> x) else NONE
  fun safe_dest_eq tm =
    if boolSyntax.is_eq tm then boolSyntax.dest_eq tm else
    Lib.tryfind boolSyntax.dest_eq (boolSyntax.strip_disj tm)
    handle HOL_ERR _ =>
      raise(ERR"subset_basis_st"("Could not prove heap subgoal: "^(Parse.term_to_string tm)))
  val s =
     List.mapPartial (mk_mapping o safe_dest_eq o #2) subgoals
  val goal' = Term.subst s goal
  val th = prove(goal',tac)
  val th = MATCH_MP SPLIT_exists (CONJ (INST s sets_thm) th)
  in th end


(*
  - st is the ML prog state of the final desired program
  - name (string) is the name of the program's main function (unit->unit)
  - spec is a theorem of the form
     |- app (basis_proj1, basis_proj2) main_v [Conv NONE []] P
          (POSTv uv. &UNIT_TYPE () uv * STDOUT x * Q)
    where main_v is the value corresponding to the main function
          P is the precondition
          x is the desired output
          Q is any remaining postconditions

    (add_basis_proj can turn an |- app p ... spec into the form above)
*)

fun call_thm st name spec =
  let
    val call_ERR = ERR "call_thm"
    val th =
      call_main_thm_basis
        |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
        |> SPEC(stringSyntax.fromMLstring name)
        |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
        |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
        |> C HO_MATCH_MP spec
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc (* TODO: this is too slow for large progs *)
    val th = PURE_REWRITE_RULE[prog_rewrite] th
    val (mods_tm,types_tm) = th |> concl |> dest_imp |> #1 |> dest_conj
    val mods_thm =
      mods_tm |> (RAND_CONV EVAL THENC no_dup_mods_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(call_ERR "duplicate modules")
    val types_thm =
      types_tm |> (RAND_CONV EVAL THENC no_dup_top_types_conv)
      |> EQT_ELIM handle HOL_ERR _ => raise(call_ERR "duplicate top types")
    val th = MATCH_MP th (CONJ mods_thm types_thm)
    val (split,precondh1) = th |> concl |> dest_imp |> #1 |> strip_exists |> #2 |> dest_conj
    val precond = rator precondh1
    val st = split |> rator |> rand
    val SPLIT_thm = subset_basis_st st precond
    val th = PART_MATCH_A (#1 o dest_imp) th (concl SPLIT_thm)
    val th = MATCH_MP th SPLIT_thm
  in (th,rhs(concl prog_rewrite)) end

end
