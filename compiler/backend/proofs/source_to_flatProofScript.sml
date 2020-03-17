(*
  Correctness proof for source_to_flat
*)

open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     source_to_flatTheory flatLangTheory flatSemTheory flatPropsTheory
     backendPropsTheory
local open flat_elimProofTheory flat_patternProofTheory in end

val _ = new_theory "source_to_flatProof";

val grammar_ancestry =
  ["source_to_flat","flatProps","namespaceProps",
   "semantics","semanticPrimitivesProps","ffi","lprefix_lub",
   "backend_common","misc","backendProps"];
val _ = set_grammar_ancestry grammar_ancestry;

(* TODO: move *)

val compile_exps_length = Q.prove (
  `LENGTH (compile_exps t m es) = LENGTH es`,
  induct_on `es` >>
  rw [compile_exp_def]);

Theorem mapi_map:
   !f g l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l
Proof
  Induct_on `l` >>
  rw [combinTheory.o_DEF]
QED

val fst_lem = Q.prove (
  `(λ(p1,p1',p2). p1) = FST`,
  rw [FUN_EQ_THM] >>
  pairarg_tac >>
  rw []);

val funion_submap = Q.prove (
  `FUNION x y SUBMAP z ∧ DISJOINT (FDOM x) (FDOM y) ⇒ y SUBMAP z`,
  rw [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, FUNION_DEF] >>
  metis_tac []);

val flookup_funion_submap = Q.prove (
  `(x ⊌ y) SUBMAP z ∧
   FLOOKUP (x ⊌ y) k = SOME v
   ⇒
   FLOOKUP z k = SOME v`,
  rw [SUBMAP_DEF, FLOOKUP_DEF] >>
  metis_tac []);

Theorem FILTER_MAPi_ID:
   ∀ls f. FILTER P (MAPi f ls) = MAPi f ls ⇔
   (∀n. n < LENGTH ls ⇒ P (f n (EL n ls)))
Proof
  Induct \\ reverse(rw[])
  >- (
    qmatch_goalsub_abbrev_tac`a ⇔ b`
    \\ `¬a`
    by (
      simp[Abbr`a`]
      \\ disch_then(mp_tac o Q.AP_TERM`LENGTH`)
      \\ rw[]
      \\ specl_args_of_then``FILTER``LENGTH_FILTER_LEQ mp_tac
      \\ simp[] )
    \\ simp[Abbr`b`]
    \\ qexists_tac`0`
    \\ simp[] )
  \\ simp[Once FORALL_NUM, SimpRHS]
QED

(* -- *)

(* value relation *)


(* bind locals with an arbitrary trace *)
val bind_locals_def = Define `
  bind_locals ts locals comp_map =
    nsBindList (MAP2 (\t x. (x, Local t x)) ts locals) comp_map`;

val nsAppend_bind_locals = Q.prove(`
  ∀funs.
  nsAppend (alist_to_ns (MAP (λx. (x,Local t x)) (MAP FST funs))) (bind_locals ts locals comp_map) =
  bind_locals (REPLICATE (LENGTH funs) t ++ ts) (MAP FST funs ++ locals) comp_map`,
  Induct_on`funs`>>fs[FORALL_PROD,bind_locals_def,namespaceTheory.nsBindList_def]);

val nsBindList_pat_tups_bind_locals = Q.prove(`
  ∀ls.
  ∃tss.
  nsBindList (pat_tups t ls) (bind_locals ts locals comp_map) =
  bind_locals (tss ++ ts) (ls ++ locals) comp_map ∧
  LENGTH tss = LENGTH ls`,
  Induct>>rw[pat_tups_def,namespaceTheory.nsBindList_def,bind_locals_def]>>
  qexists_tac`(t § (LENGTH ls + 1))::tss`>>simp[]);

val _ = Datatype `
  global_env =
    <| v : flatSem$v option list; c : (ctor_id # type_id) # num |-> stamp |>`;

val has_bools_def = Define `
  has_bools genv ⇔
    FLOOKUP genv ((true_tag, SOME bool_id), 0n) = SOME (TypeStamp "True" bool_type_num) ∧
    FLOOKUP genv ((false_tag, SOME bool_id), 0n) = SOME (TypeStamp "False" bool_type_num)`;

val has_lists_def = Define `
  has_lists genv ⇔
    FLOOKUP genv ((cons_tag, SOME list_id), 2n) = SOME (TypeStamp "::" list_type_num) ∧
    FLOOKUP genv ((nil_tag, SOME list_id), 0n) = SOME (TypeStamp "[]" list_type_num)`;

val has_exns_def = Define `
  has_exns genv ⇔
    FLOOKUP genv ((div_tag, NONE), 0n) = SOME div_stamp ∧
    FLOOKUP genv ((chr_tag, NONE), 0n) = SOME chr_stamp ∧
    FLOOKUP genv ((subscript_tag, NONE), 0n) = SOME subscript_stamp ∧
    FLOOKUP genv ((bind_tag, NONE), 0n) = SOME bind_stamp`;

val genv_c_ok_def = Define `
  genv_c_ok genv_c ⇔
    has_bools genv_c ∧
    has_exns genv_c ∧
    has_lists genv_c ∧
    (!cn1 cn2 l1 l2 stamp1 stamp2.
      FLOOKUP genv_c (cn1,l1) = SOME stamp1 ∧
      FLOOKUP genv_c (cn2,l2) = SOME stamp2
      ⇒
      (ctor_same_type (SOME stamp1) (SOME stamp2) ⇔ ctor_same_type (SOME cn1) (SOME cn2))) ∧
    (!cn1 cn2 l1 l2 stamp.
      FLOOKUP genv_c (cn1,l1) = SOME stamp ∧
      FLOOKUP genv_c (cn2,l2) = SOME stamp
      ⇒
      cn1 = cn2 ∧ l1 = l2)`;

Inductive v_rel:
  (!genv lit.
    v_rel genv ((Litv lit):semanticPrimitives$v) ((Litv lit):flatSem$v)) ∧
  (!genv cn cn' vs vs'.
    LIST_REL (v_rel genv) vs vs' ∧
    FLOOKUP genv.c (cn', LENGTH vs) = SOME cn
    ⇒
    v_rel genv (Conv (SOME cn) vs) (Conv (SOME cn') vs')) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Conv NONE vs) (Conv NONE vs')) ∧
  (!genv comp_map env env_v_local x e env_v_local' t ts.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env ∧
    LENGTH ts = LENGTH env_v_local'.v + 1
    ⇒
    v_rel genv
      (Closure (env with v := nsAppend env_v_local env.v) x e)
      (Closure env_v_local' x
        (compile_exp t
          (comp_map with v := bind_locals ts (x::MAP FST env_v_local'.v) comp_map.v)
          e))) ∧
  (* For expression level let recs *)
  (!genv comp_map env env_v_local funs x env_v_local' t ts.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env ∧
    LENGTH ts = LENGTH funs + LENGTH env_v_local'.v
    ⇒
    v_rel genv
      (Recclosure (env with v := nsAppend env_v_local env.v) funs x)
      (Recclosure env_v_local'
        (compile_funs t
          (comp_map with v := bind_locals ts (MAP FST funs++MAP FST env_v_local'.v) comp_map.v) funs)
          x)) ∧
  (* For top-level let recs *)
  (!genv comp_map env funs flat_env x y e new_vars t1 t2.
    MAP FST new_vars = MAP FST (REVERSE funs) ∧
    global_env_inv genv comp_map {} env ∧
    flat_env.v = [] ∧
    find_recfun x funs = SOME (y, e) ∧
    (* A syntactic way of relating the recursive function environment, rather
     * than saying that they build v_rel related environments, which looks to
     * require step-indexing *)
    (!x. x ∈ set (MAP FST funs) ⇒
       ?n y e t1 t2 t3.
         ALOOKUP new_vars x = SOME (Glob t1 n) ∧
         n < LENGTH genv.v ∧
         find_recfun x funs = SOME (y,e) ∧
         EL n genv.v =
           SOME (Closure flat_env y
                  (compile_exp t2 (comp_map with v := nsBindList ((y, Local t3 y)::new_vars) comp_map.v) e)))
    ⇒
    v_rel genv
      (Recclosure env funs x)
      (Closure flat_env y
        (compile_exp t1
          (comp_map with v := nsBindList ((y, Local t2 y)::new_vars) comp_map.v)
          e))) ∧
  (!genv loc.
    v_rel genv (Loc loc) (Loc loc)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Vectorv vs) (Vectorv vs')) ∧
  (!genv.
    env_rel genv nsEmpty []) ∧
  (!genv x v env env' v'.
    env_rel genv env env' ∧
    v_rel genv v v'
    ⇒
    env_rel genv (nsBind x v env) ((x,v')::env')) ∧
  (!genv comp_map shadowers env.
    (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env.v x = SOME v
       ⇒
       ?n v' t.
         nsLookup comp_map.v x = SOME (Glob t n) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
    (!x arity stamp.
      nsLookup env.c x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c ((I ## OPTION_MAP FST) cn,arity) = SOME stamp)
    ⇒
    global_env_inv genv comp_map shadowers env)
End

Theorem v_rel_eqns:
   (!genv l v.
    v_rel genv (Litv l) v ⇔
      (v = Litv l)) ∧
   (!genv vs v.
    v_rel genv (Conv cn vs) v ⇔
      ?vs' cn'.
        LIST_REL (v_rel genv) vs vs' ∧
        v = Conv cn' vs' ∧
        case cn of
        | NONE => cn' = NONE
        | SOME cn =>
          ?cn2. cn' = SOME cn2 ∧ FLOOKUP genv.c (cn2, LENGTH vs) = SOME cn) ∧
   (!genv l v.
    v_rel genv (Loc l) v ⇔
      (v = Loc l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Vectorv vs')) ∧
   (!genv env'.
    env_rel genv nsEmpty env' ⇔
      env' = []) ∧
   (!genv x v env env'.
    env_rel genv (nsBind x v env) env' ⇔
      ?v' env''. v_rel genv v v' ∧ env_rel genv env env'' ∧ env' = ((x,v')::env'')) ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env ⇔
      (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env.v x = SOME v
       ⇒
       ?n v' t.
         nsLookup comp_map.v x = SOME (Glob t n) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
      (!x arity stamp.
        nsLookup env.c x = SOME (arity, stamp) ⇒
        ∃cn. nsLookup comp_map.c x = SOME cn ∧
          FLOOKUP genv.c ((I ## OPTION_MAP FST) cn,arity) = SOME stamp))
Proof
  srw_tac[][semanticPrimitivesTheory.Boolv_def,flatSemTheory.Boolv_def] >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`nsEmpty`](CONJUNCT1(CONJUNCT2 v_rel_cases))] >>
  every_case_tac >>
  fs [genv_c_ok_def, has_bools_def] >>
  TRY eq_tac >>
  rw [] >>
  metis_tac []
QED

Theorem env_rel_LIST_REL:
  !xs ys. env_rel genv (alist_to_ns xs) ys <=>
  LIST_REL (\x y. FST x = FST y /\ v_rel genv (SND x) (SND y)) xs ys
Proof
  Induct \\ simp [Once v_rel_cases]
  \\ simp [FORALL_PROD, PULL_EXISTS]
  \\ rw []
  \\ EQ_TAC
  \\ simp [PULL_EXISTS, FORALL_PROD]
QED

val env_rel_dom = Q.prove (
  `!genv env env'.
    env_rel genv env env'
    ⇒
    ?l. env = alist_to_ns l ∧ MAP FST l = MAP FST env'`,
  induct_on `env'` >>
  simp [Once v_rel_cases] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw_tac list_ss [GSYM alist_to_ns_cons] >>
  prove_tac [MAP, FST]);

val env_rel_lookup = Q.prove (
  `!genv env x v env'.
    ALOOKUP env x = SOME v ∧
    env_rel genv (alist_to_ns env) env'
    ⇒
    ?v'.
      v_rel genv v v' ∧
      ALOOKUP env' x = SOME v'`,
  induct_on `env'` >>
  simp [] >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  fs [] >>
  rw [] >>
  Cases_on `env` >>
  TRY (PairCases_on `h`) >>
  fs [alist_to_ns_cons] >>
  rw [] >>
  metis_tac []);

val env_rel_append = Q.prove (
  `!genv env1 env2 env1' env2'.
    env_rel genv env1 env1' ∧
    env_rel genv env2 env2'
    ⇒
    env_rel genv (nsAppend env1 env2) (env1'++env2')`,
  induct_on `env1'` >>
  rw []
  >- (
    `env1 = nsEmpty` by fs [Once v_rel_cases] >>
    rw []) >>
  qpat_x_assum `env_rel _ _ (_::_)` mp_tac >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  simp [Once v_rel_cases]);

Triviality env_rel_one:
  env_rel genv (nsBind a b nsEmpty) xs <=>
  ?v. xs = [(a, v)] /\ v_rel genv b v
Proof
  simp [Once v_rel_cases]
  \\ Cases_on `xs` \\ simp []
  \\ simp [Once v_rel_cases]
  \\ metis_tac []
QED

Theorem env_rel_bind_one = env_rel_append
  |> Q.SPECL [`genv`, `nsBind a b nsEmpty`, `env2`, `[(c, d)]`]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss ()) [env_rel_one]

val env_rel_el = Q.prove (
  `!genv env env_i1.
    env_rel genv (alist_to_ns env) env_i1 ⇔
    LENGTH env = LENGTH env_i1 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i1)) ∧ v_rel genv (SND (EL n env)) (SND (EL n env_i1))`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  srw_tac[][v_rel_eqns] >>
  eq_tac >>
  srw_tac[][] >>
  srw_tac[][]
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `env_i1` >>
      full_simp_tac(srw_ss())[] >>
      FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      srw_tac[][] >>
      qexists_tac `SND h` >>
      srw_tac[][] >>
      FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
      srw_tac[][]));

val subglobals_def = Define `
  subglobals g1 g2 ⇔
    LENGTH g1 ≤ LENGTH g2 ∧
    !n. n < LENGTH g1 ∧ IS_SOME (EL n g1) ⇒ EL n g1 = EL n g2`;

val subglobals_refl = Q.prove (
  `!g. subglobals g g`,
  rw [subglobals_def]);

val subglobals_trans = Q.prove (
  `!g1 g2 g3. subglobals g1 g2 ∧ subglobals g2 g3 ⇒ subglobals g1 g3`,
  rw [subglobals_def] >>
  res_tac >>
  fs []);

val subglobals_refl_append = Q.prove (
  `!g1 g2 g3.
    subglobals (g1 ++ g2) (g1 ++ g3) = subglobals g2 g3 ∧
    (LENGTH g2 = LENGTH g3 ⇒ subglobals (g2 ++ g1) (g3 ++ g1) = subglobals g2 g3)`,
  rw [subglobals_def] >>
  eq_tac >>
  rw []
  >- (
    first_x_assum (qspec_then `n + LENGTH (g1:'a option list)` mp_tac) >>
    rw [EL_APPEND_EQN])
  >- (
    first_x_assum (qspec_then `n - LENGTH (g1:'a option list)` mp_tac) >>
    rw [EL_APPEND_EQN] >>
    fs [EL_APPEND_EQN])
  >- (
    first_x_assum (qspec_then `n` mp_tac) >>
    rw [EL_APPEND_EQN])
  >- (
    Cases_on `n < LENGTH g3` >>
    fs [EL_APPEND_EQN] >>
    rfs [] >>
    fs []));

val v_rel_weakening = Q.prove (
  `(!genv v v'.
    v_rel genv v v'
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ v_rel genv' v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ env_rel genv' env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ global_env_inv genv' comp_map shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns, subglobals_def]
  >- fs [LIST_REL_EL_EQN]
  >- fs [LIST_REL_EL_EQN]
  >- fs [LIST_REL_EL_EQN]
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`, `ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`,`ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t1`, `t2`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns, EL_APPEND1] >>
      srw_tac[][] >>
      res_tac >>
      qexists_tac `n` >>
      srw_tac[][EL_APPEND1] >>
      map_every qexists_tac [`t2`,`t3`] >>
      rw [] >>
      metis_tac [IS_SOME_DEF])
  >- fs [LIST_REL_EL_EQN]
  >- (
    res_tac >>
    rw [] >>
    metis_tac [IS_SOME_DEF])
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]);

val v_rel_weakening2 = Q.prove (
  `(!genv v v'.
    v_rel genv v v'
    ⇒
    ∀gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ v_rel (genv with c := FUNION gc genv.c) v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ env_rel (genv with c := FUNION gc genv.c) env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    !gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ global_env_inv (genv with c := FUNION gc genv.c) comp_map shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns]
  >- fs [LIST_REL_EL_EQN]
  >- (
    simp [FLOOKUP_FUNION] >>
    fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
    rw [] >>
    metis_tac [])
  >- fs [LIST_REL_EL_EQN]
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`, `ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`,`ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t1`, `t2`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns, EL_APPEND1] >>
      srw_tac[][] >>
      res_tac >>
      qexists_tac `n` >>
      srw_tac[][EL_APPEND1] >>
      map_every qexists_tac [`t2`,`t3`] >>
      decide_tac)
  >- fs [LIST_REL_EL_EQN]
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]
  >- (
    res_tac >>
    fs [] >>
    simp [FLOOKUP_FUNION] >>
    fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
    rw [] >>
    metis_tac []));

val drestrict_lem = Q.prove (
  `f1 SUBMAP f2 ⇒ DRESTRICT f2 (COMPL (FDOM f1)) ⊌ f1 = f2`,
  rw [FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_FUNION] >>
  every_case_tac >>
  fs [FLOOKUP_DRESTRICT, SUBMAP_DEF] >>
  fs [FLOOKUP_DEF] >>
  rw [] >>
  metis_tac []);

val v_rel_weak = Q.prove (
  `!genv v v' genv'.
   v_rel genv v v' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   v_rel genv' v v'`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

val env_rel_weak = Q.prove (
  `!genv env env' genv'.
   env_rel genv env env' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   env_rel genv' env env'`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

val global_env_inv_weak = Q.prove (
  `!genv comp_map shadowers env genv'.
   global_env_inv genv comp_map shadowers env ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   global_env_inv genv' comp_map shadowers env`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

Inductive result_rel:
  (∀genv v v'.
    f genv v v'
    ⇒
    result_rel f genv (Rval v) (Rval v')) ∧
  (∀genv v v'.
    v_rel genv v v'
    ⇒
    result_rel f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!genv a.
    result_rel f genv (Rerr (Rabort a)) (Rerr (Rabort a)))
End

val result_rel_eqns = Q.prove (
  `(!genv v r.
    result_rel f genv (Rval v) r ⇔
      ?v'. f genv v v' ∧ r = Rval v') ∧
   (!genv v r.
    result_rel f genv (Rerr (Rraise v)) r ⇔
      ?v'. v_rel genv v v' ∧ r = Rerr (Rraise v')) ∧
   (!genv v r a.
    result_rel f genv (Rerr (Rabort a)) r ⇔
      r = Rerr (Rabort a))`,
  srw_tac[][result_rel_cases] >>
  metis_tac []);

Inductive sv_rel:
  (!genv v v'.
    v_rel genv v v'
    ⇒
    sv_rel genv (Refv v) (Refv v')) ∧
  (!genv w.
    sv_rel genv (W8array w) (W8array w)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    sv_rel genv (Varray vs) (Varray vs'))
End

val sv_rel_weak = Q.prove (
  `!genv sv sv' genv'.
   sv_rel genv sv sv' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   sv_rel genv' sv sv'`,
  srw_tac[][sv_rel_cases] >>
  metis_tac [v_rel_weak, LIST_REL_EL_EQN]);

Definition inc_compile_def:
  inc_compile env st decs =
  let (_, st', env', decs') = source_to_flat$compile_decs 0 st env decs in
  (glob_alloc st' (<| next := st |>) :: decs', env', st')
End

val _ = type_abbrev ("compiler_state", ``: next_indices``);

Inductive s_rel:
  (!genv_c s s'.
    LIST_REL (sv_rel <| v := s'.globals; c := genv_c |>) s.refs s'.refs ∧
    s.clock = s'.clock ∧
    s.ffi = s'.ffi ∧
    s'.c = FDOM genv_c
    ⇒
    s_rel genv_c s s')
End

Inductive env_all_rel:
  (!genv map env_v_local env env' locals.
    (?l. env_v_local = alist_to_ns l ∧ MAP FST l = locals) ∧
    global_env_inv genv map (set locals) env ∧
    env_rel genv env_v_local env'
    ⇒
    env_all_rel genv map
      <| c := env.c; v := nsAppend env_v_local env.v |>
      <| v := env' |>
      locals)
End

val env_all_rel_weak = Q.prove (
  `!genv map locals env env' genv'.
   env_all_rel genv map env env' locals ∧
   genv.c SUBMAP genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   env_all_rel genv' map env env' locals`,
  rw [env_all_rel_cases] >>
  imp_res_tac env_rel_weak >>
  imp_res_tac global_env_inv_weak >>
  MAP_EVERY qexists_tac [`alist_to_ns l`, `env''`, `env'''`] >>
  rw [] >>
  metis_tac [SUBMAP_FDOM_SUBSET, SUBSET_TRANS]);

val match_result_rel_def = Define
  `(match_result_rel genv env' (Match env) (Match env_i1) =
     ?env''. env = env'' ++ env' ∧ env_rel genv (alist_to_ns env'') env_i1) ∧
   (match_result_rel genv env' No_match No_match = T) ∧
   (match_result_rel genv env' Match_type_error _ = T) ∧
   (match_result_rel genv env' _ _ = F)`;

Theorem match_result_rel_imp:
  match_result_rel genv env m1 m2 ==>
  (m1 = Match_type_error \/ (m1 = No_match /\ m2 = No_match)
    \/ (?env1 env2. m1 = Match env1 /\ m2 = Match env2))
Proof
  Cases_on `m1` \\ Cases_on `m2` \\ simp [match_result_rel_def]
QED

(* semantic functions respect relation *)


Triviality v_rel_l_cases = TypeBase.nchotomy_of ``: semanticPrimitives$v``
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (curry mk_comb ``v_rel genv``)
  |> map (fn t => mk_comb (t, ``v2 : v``))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

val do_eq = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
   (!v1 v2 r v1_i1 v2_i1.
    do_eq v1 v2 = r ∧
    v_rel genv v1 v1_i1 ∧
    v_rel genv v2 v2_i1
    ⇒
    do_eq v1_i1 v2_i1 = r) ∧
   (!vs1 vs2 r vs1_i1 vs2_i1.
    do_eq_list vs1 vs2 = r ∧
    LIST_REL (v_rel genv) vs1 vs1_i1 ∧
    LIST_REL (v_rel genv) vs2 vs2_i1
    ⇒
    do_eq_list vs1_i1 vs2_i1 = r)`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.do_eq_ind >>
  rpt strip_tac >>
  fs [terminationTheory.do_eq_def, flatSemTheory.do_eq_def, v_rel_l_cases] >>
  rveq >> fs [] >>
  rpt (irule COND_CONG >> rpt strip_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  fs [flatSemTheory.ctor_same_type_def,
    semanticPrimitivesTheory.ctor_same_type_def] >>
  TRY every_case_tac >>
  metis_tac [SOME_11, genv_c_ok_def
    |> SIMP_RULE (srw_ss()) [semanticPrimitivesTheory.ctor_same_type_def]]
  );

val v_to_char_list = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.v_to_char_list_ind >>
  srw_tac[][terminationTheory.v_to_char_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, flatSemTheory.v_to_char_list_def,
                          genv_c_ok_def, has_lists_def] >>
  rw []
  >- (
    `cn2 = (nil_tag,SOME list_id)` by metis_tac [] >>
    rw [flatSemTheory.v_to_char_list_def])
  >- (
    `cn2 = (cons_tag,SOME list_id)` by metis_tac [] >>
    rw [flatSemTheory.v_to_char_list_def]));

val v_to_list = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      LIST_REL (v_rel genv) vs1 vs2`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.v_to_list_ind >>
  srw_tac[][terminationTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[has_lists_def, genv_c_ok_def, v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][]
  >- (
    `cn2 = (nil_tag,SOME list_id)` by metis_tac [] >>
    rw [v_to_list_def])
  >- (
    `cn2 = (cons_tag,SOME list_id)` by metis_tac [] >>
    rw [v_to_list_def] >>
    every_case_tac >>
    metis_tac [NOT_SOME_NONE, SOME_11]));

val vs_to_string = Q.prove(
  `∀v1 v2 s.
    LIST_REL (v_rel genv) v1 v2 ⇒
    vs_to_string v1 = SOME s ⇒
    vs_to_string v2 = SOME s`,
  ho_match_mp_tac terminationTheory.vs_to_string_ind
  \\ rw[terminationTheory.vs_to_string_def,vs_to_string_def]
  \\ fs[v_rel_eqns]
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ fs[]
  \\ rw[vs_to_string_def]);

val v_rel_lems = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
    (!b. v_rel genv (Boolv b) (Boolv b)) ∧
    v_rel genv div_exn_v div_exn_v ∧
    v_rel genv chr_exn_v chr_exn_v ∧
    v_rel genv bind_exn_v bind_exn_v ∧
    v_rel genv sub_exn_v subscript_exn_v`,
  rw [semanticPrimitivesTheory.div_exn_v_def, flatSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, flatSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, flatSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, flatSemTheory.subscript_exn_v_def,
      v_rel_eqns, genv_c_ok_def, has_exns_def, has_bools_def,
      semanticPrimitivesTheory.Boolv_def, flatSemTheory.Boolv_def] >>
  every_case_tac >>
  simp [v_rel_eqns]);

Theorem list_to_v_v_rel:
   !xs ys.
     has_lists genv.c ∧ LIST_REL (v_rel genv) xs ys ⇒
       v_rel genv (list_to_v xs) (list_to_v ys)
Proof
  Induct >>
  rw [] >>
  fs [LIST_REL_EL_EQN, flatSemTheory.list_to_v_def, has_lists_def,
      v_rel_eqns, semanticPrimitivesTheory.list_to_v_def]
QED

Theorem LIST_REL_IMP_EL2: (* TODO: move *)
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH ys ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

Theorem LIST_REL_IMP_EL: (* TODO: move *)
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH xs ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

val s_i1 = ``s_i1 : (compiler_state, 'ffi) flatSem$state``;
val s1_i1 = mk_var ("s1_i1", type_of s_i1);

val do_app = Q.prove (
  `!genv s1 s2 op vs r ^s1_i1 vs_i1.
    do_app s1 op vs = SOME (s2, r) ∧
    LIST_REL (sv_rel genv) (FST s1) s1_i1.refs ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    SND s1 = s1_i1.ffi ∧
    genv_c_ok genv.c ∧
    op ≠ AallocEmpty
    ⇒
     ∃r_i1 s2_i1.
       LIST_REL (sv_rel genv) (FST s2) s2_i1.refs ∧
       SND s2 = s2_i1.ffi ∧
       s1_i1.globals = s2_i1.globals ∧
       result_rel v_rel genv r r_i1 ∧
       do_app s1_i1 (astOp_to_flatOp op) vs_i1 = SOME (s2_i1, r_i1)`,
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1` >>
  Cases_on `op = ConfigGC` >-
     (simp [astOp_to_flatOp_def] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, Unitv_def]) >>
  pop_assum mp_tac >>
  Cases_on `op` >>
  simp [astOp_to_flatOp_def]
  >- ((* Opn *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opw *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems]
      \\ Cases_on`o'` \\ fs[opw8_lookup_def,opw64_lookup_def])
  >- ((* Shift *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      TRY (rename1 `shift8_lookup s11 w11 n11`) >>
      TRY (rename1 `shift64_lookup s11 w11 n11`) >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems]
      \\ Cases_on`w11` \\ Cases_on`s11` \\ fs[shift8_lookup_def,shift64_lookup_def])
  >- ((* Equality *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct, v_rel_lems])
  >- ( (*FP_cmp *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_uop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_bop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_top *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opapp *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opassign *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def, Unitv_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ((* Opref *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Opderef *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- ((* Aw8alloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Aw8sub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, v_rel_lems])
  >- ((* Aw8length *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def])
  >- ((* Aw8update *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][Unitv_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][v_rel_lems])
  >- ((* WordFromInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* WordToInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* CopyStrStr *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases]
    \\ simp[v_rel_lems,v_rel_eqns])
  >- ((* CopyStrAw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* CopyAw8Str *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns])
  >- ((* CopyAw8Aw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* Ord *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems])
  >- ((* Chr *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Chopb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Implode *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >- (rename [`Explode`] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][] >>
      Induct_on `str` >>
      fs [semanticPrimitivesTheory.list_to_v_def,flatSemTheory.list_to_v_def] >>
      simp [Once v_rel_cases] >>
      fs [genv_c_ok_def,has_lists_def] >>
      simp [Once v_rel_cases])
  >- ((* Strsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[stringTheory.IMPLODE_EXPLODE_I, v_rel_lems])
  >- ((* Strlen *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Strcat *)
    rw[semanticPrimitivesPropsTheory.do_app_cases,flatSemTheory.do_app_def]
    \\ fs[LIST_REL_def]
    \\ imp_res_tac v_to_list \\ fs[]
    \\ imp_res_tac vs_to_string \\ fs[result_rel_cases,v_rel_eqns] )
  >- ((* VfromList *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >- ((* Vsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, v_rel_lems])
  >- ((* Vlength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aalloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Asub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      decide_tac)
  >- ((* Alength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH])
  >- ((* Aupdate *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def,Unitv_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      decide_tac)
  >- ((* Asub_unsafe *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      decide_tac)
  >- ((* Aupdate_unsafe *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      drule_then drule LIST_REL_IMP_EL2 >>
      disch_tac >>
      every_case_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[Unitv_def] >>
      DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >>
      full_simp_tac(srw_ss())[Unitv_def, sv_rel_cases] >>
      DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >>
      full_simp_tac(srw_ss())[] >>
      decide_tac)
  >- ((* Aw8sub_unsafe *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, v_rel_lems])
  >- ((* Aw8update_unsafe *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, Unitv_def, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][v_rel_lems] >> CCONTR_TAC >> rfs [] >> rveq >> fs [])
  >- ((* ListAppend *)
    simp [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
    rw [] >>
    fs [] >>
    rw [] >>
    imp_res_tac v_to_list >>
    fs [] >>
    rw [result_rel_cases] >>
    irule list_to_v_v_rel >>
    fs [genv_c_ok_def, LIST_REL_EL_EQN, EL_APPEND_EQN] >>
    rw [])
  >- ((* FFI *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns,Unitv_def] \\ rw[] \\
      fs[store_lookup_def, LIST_REL_EL_EQN] \\ fs[] \\ rfs[] \\
      res_tac \\
      qpat_x_assum`EL _ _ = _`assume_tac \\ fs[] \\
      qhdtm_x_assum`sv_rel`mp_tac \\
      simp[Once sv_rel_cases] \\ rw[] \\
      fs[IMPLODE_EXPLODE_I] \\
      CASE_TAC \\ fs[store_assign_def,store_v_same_type_def,EL_LUPDATE] \\ rfs[] \\ rw[EL_LUPDATE]
      \\ rw[sv_rel_cases, result_rel_cases, v_rel_eqns])
  >- ((* Eval *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
  )
  >- ((* EnvLookup *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      rveq >> fs[] >>
      fs[v_rel_l_cases]
  ));

val find_recfun = Q.prove (
  `!x funs e comp_map y t.
    find_recfun x funs = SOME (y,e)
    ⇒
    find_recfun x (compile_funs t comp_map funs) =
      SOME (y, compile_exp t (comp_map with v := nsBind y (Local t y) comp_map.v) e)`,
   induct_on `funs` >>
   srw_tac[][Once find_recfun_def, compile_exp_def] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]);

val do_app_rec_help = Q.prove (
  `!genv comp_map env_v_local env_v_local' env_v_top funs t.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env' ∧
    LENGTH ts = LENGTH funs' + LENGTH env_v_local'.v
    ⇒
     env_rel genv
       (alist_to_ns
          (MAP
             (λ(f,n,e).
                (f,
                 Recclosure
                   (env' with v := nsAppend env_v_local env'.v)
                   funs' f)) funs))
       (MAP
          (λ(fn,n,e).
             (fn,
              Recclosure env_v_local'
                (compile_funs t
                   (comp_map with v :=
                     (FOLDR (λ(x,v) e. nsBind x v e) comp_map.v
                      (MAP2 (λt x. (x,Local t x)) ts
                         (MAP FST funs' ++ MAP FST env_v_local'.v)))) funs')
                fn))
          (compile_funs t
             (comp_map with v :=
               (FOLDR (λ(x,v) e. nsBind x v e) comp_map.v
                (MAP2 (λt x. (x,Local t x)) ts
                   (MAP FST funs' ++ MAP FST env_v_local'.v)))) funs))`,
  induct_on `funs`
  >- srw_tac[][v_rel_eqns, compile_exp_def] >>
  rw [] >>
  PairCases_on`h`>>fs[compile_exp_def]>>
  simp[v_rel_eqns]>>
  simp [Once v_rel_cases] >>
  MAP_EVERY qexists_tac [`comp_map`, `env'`, `env_v_local`, `t`,`ts`] >>
  simp[compile_exp_def,bind_locals_def]>>
  simp_tac (std_ss) [GSYM APPEND, namespaceTheory.nsBindList_def]);

val global_env_inv_add_locals = Q.prove (
  `!genv comp_map locals1 locals2 env.
    global_env_inv genv comp_map locals1 env
    ⇒
    global_env_inv genv comp_map (locals2 ∪ locals1) env`,
  srw_tac[][v_rel_eqns] >>
  metis_tac []);

val global_env_inv_extend2 = Q.prove (
  `!genv comp_map env new_vars env' locals env_c.
    set (MAP (Short o FST) new_vars) = nsDom env' ∧
    global_env_inv genv comp_map locals env ∧
    global_env_inv genv (comp_map with v := alist_to_ns new_vars) locals <| v := env'; c := env_c |>
    ⇒
    global_env_inv genv (comp_map with v := nsBindList new_vars comp_map.v) locals
        (env with v := nsAppend env' env.v)`,
  srw_tac[][v_rel_eqns, GSYM nsAppend_to_nsBindList] >>
  fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_none, nsLookup_alist_to_ns_some] >>
  res_tac >>
  fs [] >>
  rw [] >>
  qexists_tac `n` >>
  rw [] >>
  Cases_on `x` >>
  fs [] >>
  rw []
  >- (
    `Short n' ∉ nsDom env'` by metis_tac [nsLookup_nsDom, NOT_SOME_NONE] >>
    qexists_tac`t` >>
    disj2_tac >>
    rw [ALOOKUP_NONE] >>
    qpat_x_assum `_ = nsDom _` (assume_tac o GSYM) >>
    fs [MEM_MAP] >>
    fs [namespaceTheory.id_to_mods_def])
  >- (
    fs [namespaceTheory.id_to_mods_def] >>
    Cases_on `p1` >>
    fs [] >>
    rw []));

val lookup_build_rec_env_lem = Q.prove (
  `!x cl_env funs' funs.
    ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs) x = SOME v
    ⇒
    v = semanticPrimitives$Recclosure cl_env funs' x`,
  induct_on `funs` >>
  srw_tac[][] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]);

val sem_env_eq_lemma = Q.prove (
  `!(env:'a sem_env) x. (env with v := x) = <| v := x; c := env.c |>`,
  rw [] >>
  rw [sem_env_component_equality]);

val do_opapp = Q.prove (
  `!genv vs vs_i1 env e.
    semanticPrimitives$do_opapp vs = SOME (env, e) ∧
    LIST_REL (v_rel genv) vs vs_i1
    ⇒
     ∃comp_map env_i1 locals t1 ts.
       env_all_rel genv comp_map env env_i1 locals ∧
       LENGTH ts = LENGTH locals ∧
       flatSem$do_opapp vs_i1 = SOME (env_i1, compile_exp t1 (comp_map with v := bind_locals ts locals comp_map.v) e)`,
   srw_tac[][do_opapp_cases, flatSemTheory.do_opapp_def] >>
   full_simp_tac(srw_ss())[LIST_REL_CONS1] >>
   srw_tac[][]
   >- (
       qpat_x_assum `v_rel genv (Closure _ _ _) _` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       rename [`v_rel _ v v'`, `env_rel _ envL env'.v`, `nsBind name _ _`] >>
       MAP_EVERY qexists_tac [`comp_map`, `name :: MAP FST env'.v`, `t`, `ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def, FOLDR_MAP] >>
       fs[ADD1]>>
       MAP_EVERY qexists_tac [`nsBind name v envL`, `env`] >>
       simp [flatSemTheory.environment_component_equality,
         sem_env_component_equality] >>
       srw_tac[][v_rel_eqns]
       >- (
         drule env_rel_dom >>
         rw [MAP_o] >>
         rw_tac list_ss [GSYM alist_to_ns_cons] >>
         qexists_tac`(name,v)::l`>>simp[])>>
       full_simp_tac(srw_ss())[v_rel_eqns] >>
       metis_tac [])
   >- (
     rename [`find_recfun name funs = SOME (arg, e)`,
             `v_rel _ (Recclosure env _ _) fun_v'`,
             `v_rel _ v v'`] >>
     qpat_x_assum `v_rel genv (Recclosure _ _ _) _` mp_tac >>
     srw_tac[][Once v_rel_cases] >>
     srw_tac[][] >>
     imp_res_tac find_recfun >>
     srw_tac[][]
     >- (
       MAP_EVERY qexists_tac [`comp_map`, `arg :: MAP FST funs ++ MAP FST env_v_local'.v`,`t`,`t::ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def] >>
       srw_tac[][]>>fs[]
       >- (
         rw [sem_env_component_equality, flatSemTheory.environment_component_equality] >>
         MAP_EVERY qexists_tac [`nsBind arg v (build_rec_env funs (env' with v := nsAppend env_v_local env'.v) env_v_local)`, `env'`] >>
         srw_tac[][semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION]
         >- (
           imp_res_tac env_rel_dom >>
           simp [] >>
           rw_tac list_ss [GSYM alist_to_ns_cons] >>
           simp [] >>
           simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
           rpt (pop_assum kall_tac) >>
           induct_on `funs` >>
           rw [] >>
           pairarg_tac >>
           rw [])
         >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
         >- (
           simp [v_rel_eqns, build_rec_env_merge] >>
           match_mp_tac env_rel_append >>
           simp [] >>
           metis_tac [do_app_rec_help]))
       >- (
         simp[compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
         full_simp_tac(srw_ss())[FST_triple]))
     >- (
       MAP_EVERY qexists_tac [`comp_map with v := nsBindList new_vars comp_map.v`, `[arg]`, `t1`, `[t2]`] >>
       srw_tac[][env_all_rel_cases, namespaceTheory.nsBindList_def,bind_locals_def] >>
       rw [GSYM namespaceTheory.nsBindList_def] >>
       MAP_EVERY qexists_tac [`nsSing arg v`, `env with v := build_rec_env funs env env.v`] >>
       simp [semanticPrimitivesTheory.sem_env_component_equality,
             environment_component_equality] >>
       srw_tac[][semanticPrimitivesTheory.sem_env_component_equality,
             semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION,
             environment_component_equality]
       >- (
         qexists_tac `[(arg,v)]` >>
         rw [namespaceTheory.nsSing_def, namespaceTheory.nsBind_def,
             namespaceTheory.nsEmpty_def])
       >- (
         irule global_env_inv_extend2 >>
         rw []
         >- (
           `MAP (Short:tvarN -> (tvarN, tvarN) id) (MAP FST new_vars) = MAP Short (MAP FST (REVERSE funs))` by metis_tac [] >>
           fs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
         >- metis_tac [global_env_inv_add_locals, UNION_EMPTY]
         >- (
           qexists_tac `env.c` >>
           srw_tac[][v_rel_eqns] >>
           fs [nsLookup_alist_to_ns_some] >>
           rw []
           >- (
             `MEM x' (MAP FST funs)`
                     by (imp_res_tac ALOOKUP_MEM >>
                         full_simp_tac(srw_ss())[MEM_MAP] >>
                         PairCases_on `y` >>
                         srw_tac[][] >>
                         full_simp_tac(srw_ss())[] >>
                         metis_tac [FST, MEM_MAP, pair_CASES]) >>
             res_tac >>
             qexists_tac `n` >>
             srw_tac[][] >>
             drule lookup_build_rec_env_lem >>
             srw_tac[][Once v_rel_cases] >>
             MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t2`, `t3`] >>
             srw_tac[][find_recfun_ALOOKUP])
           >- fs [v_rel_eqns]))
       >- (
         simp [Once v_rel_cases] >>
         qexists_tac `v` >>
         qexists_tac `nsEmpty` >>
         rw [namespaceTheory.nsSing_def, namespaceTheory.nsEmpty_def,
             namespaceTheory.nsBind_def] >>
         simp [Once v_rel_cases, namespaceTheory.nsEmpty_def]))));

Theorem pat_bindings_compile_pat[simp]:
 !comp_map (p:ast$pat) vars. pat_bindings (compile_pat comp_map p) vars = pat_bindings p vars
Proof
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def, pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [pat_bindings_def,astTheory.pat_bindings_def, PULL_FORALL]
QED

val eta2 = Q.prove (
  `!f x. (\y. f x y) = f x`,
  metis_tac []);

val ctor_same_type_refl = Q.prove (
  `ctor_same_type x x`,
  Cases_on `x` >>
  rw [ctor_same_type_def] >>
  rename [`SOME x`] >>
  Cases_on `x` >>
  rw [ctor_same_type_def]);

Triviality ctor_same_type_SND:
  ctor_same_type (SOME x) (SOME y) = (SND x = SND y)
Proof
  Cases_on `x` \\ Cases_on `y` \\ simp [ctor_same_type_def]
QED

Theorem genv_c_ok_pmatch_stamps_ok:
  s_rel genv_c s t /\
  nsLookup comp_map_c nm = SOME flat_gp_stamp /\
  same_type src_stamp src_stamp' /\
  genv_c_ok genv_c /\
  FLOOKUP genv_c ((I ## OPTION_MAP FST) flat_gp_stamp, l) = SOME src_stamp /\
  FLOOKUP genv_c (flat_stamp', l') = SOME src_stamp' ==>
  pmatch_stamps_ok t.c (SOME flat_gp_stamp) (SOME flat_stamp') l l'
Proof
  rw [genv_c_ok_def]
  \\ `ctor_same_type (SOME src_stamp) (SOME src_stamp')`
    by simp [semanticPrimitivesTheory.ctor_same_type_def]
  \\ `SND ((I ## OPTION_MAP FST) flat_gp_stamp) = SND flat_stamp'`
    by metis_tac [ctor_same_type_SND]
  \\ PairCases_on `flat_gp_stamp` \\ PairCases_on `flat_stamp'`
  \\ Cases_on `flat_stamp'1`
  >- (
    (* exceptions *)
    fs []
    \\ rw [pmatch_stamps_ok_cases]
    \\ fs [s_rel_cases, FDOM_FLOOKUP]
  )
  \\ fs [EXISTS_PROD]
  \\ simp [pmatch_stamps_ok_cases]
  \\ fs [s_rel_cases, FDOM_FLOOKUP]
  (* genv/comp_map accord needs to establish MEM *)
  \\ cheat
QED

Triviality FST_PAIR_MAP_I:
  FST ((I ## f) x) = FST x
Proof
  Cases_on `x` \\ simp []
QED

Theorem genv_c_ok_same_type_FST_eq_imp_same_ctor:
  genv_c_ok genv_c ∧
  FLOOKUP genv_c (cn1, l1) = SOME stamp1 ∧
  FLOOKUP genv_c (cn2, l2) = SOME stamp2 ∧
  same_type stamp1 stamp2 ∧
  FST cn1 = FST cn2 ∧ l1 = l2 ⇒
  same_ctor stamp1 stamp2
Proof
  Cases_on `cn1` \\ Cases_on `cn2`
  \\ fs [genv_c_ok_def, ctor_same_type_OPTREL, OPTREL_def,
            semanticPrimitivesTheory.ctor_same_type_def, same_ctor_def]
  \\ metis_tac [SND, SOME_11]
QED

val pmatch = Q.prove (
  `(!cenv s p v env r env' env'' env_i1 ^s_i1 v_i1 st'.
    semanticPrimitives$pmatch cenv s p v env = r ∧
    s_rel genv.c st' s_i1 ∧
    genv_c_ok genv.c ∧
    (!x arity stamp.
      nsLookup cenv x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c ((I ## OPTION_MAP FST) cn,arity) = SOME stamp) ∧
    env = env' ++ env'' ∧
    s_i1.globals = genv.v ∧
    st' = <| clock := clk; refs := s; ffi := ffi; next_type_stamp := nts;
                    next_exn_stamp := nes |> ∧
    v_rel genv v v_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      flatSem$pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1) ∧
   (!cenv s ps vs env r env' env'' env_i1 ^s_i1 vs_i1 st'.
    pmatch_list cenv s ps vs env = r ∧
    genv_c_ok genv.c ∧
    (!x arity stamp.
      nsLookup cenv x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c ((I ## OPTION_MAP FST) cn,arity) = SOME stamp) ∧
    env = env' ++ env'' ∧
    s_i1.globals = genv.v ∧
    s_rel genv.c st' s_i1 ∧
    st' = <| clock := clk; refs := s; ffi := ffi; next_type_stamp := nts;
                    next_exn_stamp := nes |> ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1)`,
  ho_match_mp_tac terminationTheory.pmatch_ind >>
  srw_tac[][terminationTheory.pmatch_def, flatSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, flatSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >- (
    TOP_CASE_TAC >- simp [match_result_rel_def] >>
    fs [] >>
    qmatch_assum_rename_tac `nsLookup _ _ = SOME p` >>
    `?l stamp. p = (l, stamp)` by metis_tac [pair_CASES] >> fs [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def] >>
    last_assum (drule_then strip_assume_tac) >>
    rfs [eta2] >>
    drule_then (drule_then (fn t => CHANGED_TAC (DEP_REWRITE_TAC [t])))
        genv_c_ok_pmatch_stamps_ok >>
    simp [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def]
    >- (
      (* same ctor *)
      TOP_CASE_TAC >> simp [match_result_rel_def] >>
      rw [] >>
      fs [semanticPrimitivesTheory.same_ctor_def] >>
      metis_tac [genv_c_ok_def, FST_PAIR_MAP_I]
    )
    >- (
      (* diff ctor *)
      fs [] >>
      rw [match_result_rel_def] >>
      drule_then (drule_then (drule_then drule))
        genv_c_ok_same_type_FST_eq_imp_same_ctor >>
      simp []
    )
  )
  >- (simp [pmatch_stamps_ok_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def, s_rel_cases] >>
      metis_tac [])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def, s_rel_cases]
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [LIST_REL_LENGTH])
      >- (first_x_assum match_mp_tac >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN, sv_rel_cases] >>
          res_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          `<|v := s_i1.globals; c := genv.c|> = genv`
          by rw [theorem "global_env_component_equality"] >>
          metis_tac [])
      >> full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[sv_rel_cases] >>
          metis_tac [store_v_distinct])
  >- (
      TOP_CASE_TAC >> fs [match_result_rel_def]
      >- (
        (* no match *)
        rpt (first_x_assum (first_assum o mp_then Any strip_assume_tac)) >>
        fs [] >>
        rpt (first_x_assum (qspec_then `cenv'` assume_tac)) >>
        rpt (CASE_TAC >> fs [match_result_rel_def]) >>
        rfs [match_result_rel_def]
      ) >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      srw_tac[][] >>
      pop_assum mp_tac >>
      pop_assum mp_tac >>
      res_tac >>
      srw_tac[][] >>
      CCONTR_TAC >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [match_result_rel_def, match_result_distinct])) ;

(* compiler correctness *)

val opt_bind_lem = Q.prove (
  `opt_bind NONE = \x y.y`,
  rw [FUN_EQ_THM, libTheory.opt_bind_def]);

val env_updated_lem = Q.prove (
  `env with v updated_by (λy. y) = (env : 'a flatSem$environment)`,
  rw [environment_component_equality]);

val evaluate_foldr_let_err = Q.prove (
  `!env s s' exps e x.
    flatSem$evaluate env s exps = (s', Rerr x)
    ⇒
    evaluate env s [FOLDR (Let t NONE) e exps] = (s', Rerr x)`,
  Induct_on `exps` >>
  rw [evaluate_def] >>
  fs [Once evaluate_cons] >>
  every_case_tac >>
  fs [evaluate_def] >>
  rw [] >>
  first_x_assum drule >>
  disch_then (qspec_then `e` mp_tac) >>
  rw [] >>
  every_case_tac >>
  fs [opt_bind_lem, env_updated_lem]);

Theorem can_pmatch_all_IMP_pmatch_rows:
  can_pmatch_all env.c st'.refs (MAP FST pes) v /\
  s_rel genv.c st' ^s_i1 /\ genv_c_ok genv.c /\
  env_all_rel (genv with v := s_i1.globals) comp_map env env_i1 locals /\
  v_rel (genv with v := s_i1.globals) v v' ==>
  pmatch_rows
    (compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes)
    s_i1 v' ≠ Match_type_error
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,compile_exp_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ fs [can_pmatch_all_def]
  \\ `?res. pmatch env.c st'.refs p_1 v [] = res` by fs []
  \\ `s_rel (genv with v := s_i1.globals).c st' s_i1` by fs []
  \\ drule_then drule (pmatch |> CONJUNCT1)
  \\ REWRITE_TAC [semanticPrimitivesTheory.state_component_equality]
  \\ simp []
  \\ disch_then (qspecl_then [
       `comp_map with v := bind_locals ts locals comp_map.v`,
       `[]`, `v'`] mp_tac)
  \\ impl_tac THEN1
   (fs [v_rel_rules,env_all_rel_cases]
    \\ rveq \\ fs []
    \\ qpat_x_assum `global_env_inv _ _ _ _` mp_tac
    \\ simp [Once v_rel_cases]
  )
  \\ strip_tac
  \\ qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm`
  \\ Cases_on `res`
  \\ Cases_on`mm` \\ full_simp_tac(srw_ss())[match_result_rel_def]
  \\ TOP_CASE_TAC \\ fs []
QED

val env_domain_eq_def = Define `
  env_domain_eq (var_map : source_to_flat$environment) (env : 'a sem_env)⇔
    nsDom var_map.v = nsDom env.v ∧
    nsDomMod var_map.v = nsDomMod env.v ∧
    nsDom var_map.c = nsDom env.c ∧
    nsDomMod var_map.c = nsDomMod env.c`;

val env_domain_eq_append = Q.prove (
  `env_domain_eq env1 env1' ∧
   env_domain_eq env2 env2'
   ⇒
   env_domain_eq (extend_env env1 env2) (extend_dec_env env1' env2')`,
  rw [env_domain_eq_def, extend_env_def, extend_dec_env_def,nsLookupMod_nsAppend_some,
      nsLookup_nsAppend_some, nsLookup_nsDom, namespaceTheory.nsDomMod_def,
      EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  metis_tac [option_nchotomy, NOT_SOME_NONE, pair_CASES]);

val global_env_inv_append = Q.prove (
  `!genv var_map1 var_map2 env1 env2.
    env_domain_eq var_map1 env1 ∧
    global_env_inv genv var_map1 {} env1 ∧
    global_env_inv genv var_map2 {} env2
    ⇒
    global_env_inv genv (extend_env var_map1 var_map2) {} (extend_dec_env env1 env2)`,
  rw [env_domain_eq_def, v_rel_eqns, nsLookup_nsAppend_some, extend_env_def, extend_dec_env_def] >>
  first_x_assum drule >>
  rw []
  >- rw []
  >- (
    qexists_tac `n` >>
    qexists_tac `v'` >>
    qexists_tac `t` >>
    rw [] >>
    disj2_tac >>
    rw []
    >- (
      fs [EXTENSION, namespaceTheory.nsDom_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])
    >- (
      fs [EXTENSION, namespaceTheory.nsDomMod_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy]))
  >- rw []
  >- (
    rw [] >>
    qexists_tac `cn` >>
    rw [] >>
    disj2_tac >>
    rw []
    >- (
      fs [EXTENSION, namespaceTheory.nsDom_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [pair_CASES, NOT_SOME_NONE, option_nchotomy])
    >- (
      fs [EXTENSION, namespaceTheory.nsDomMod_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])));

val result_rel_imp = hd (RES_CANON result_rel_cases);

Definition idx_prev_def:
  idx_prev idx idx2 <=>
  idx.vidx <= idx2.vidx /\ idx.tidx <= idx2.tidx /\ idx.eidx <= idx2.eidx
End

Theorem idx_prev_refl:
  idx_prev idx idx
Proof
  simp [idx_prev_def]
QED

Theorem idx_prev_trans:
  idx_prev idx idx2 /\ idx_prev idx2 idx3 ==> idx_prev idx idx3
Proof
  simp [idx_prev_def]
QED

val _ = Datatype `idx_types =
  Idx_Var | Idx_Type | Idx_Exn`;

Theorem idx_types_FORALL:
  (!x. P x) = (P Idx_Var ∧ P Idx_Type ∧ P Idx_Exn)
Proof
  EQ_TAC \\ rw []
  \\ Cases_on `x` \\ simp []
QED

Definition ALL_DISJOINT_DEF:
  ALL_DISJOINT xs ⇔
  ∀i j. i < LENGTH xs ∧ j < LENGTH xs ∧ i ≠ j ⇒ EL i xs ∩ EL j xs = ∅
End

Definition idx_block_def:
  idx_block start_idx end_idx =
  {(i, Idx_Var) | start_idx.vidx ≤ i ∧ i < end_idx.vidx} ∪
  {(i, Idx_Type) | start_idx.tidx ≤ i ∧ i < end_idx.tidx} ∪
  {(i, Idx_Exn) | start_idx.eidx ≤ i ∧ i < end_idx.eidx}
End

Definition idx_final_block_def:
  idx_final_block start_idx =
  {(i, Idx_Var) | start_idx.vidx ≤ i} ∪
  {(i, Idx_Type) | start_idx.tidx ≤ i} ∪
  {(i, Idx_Exn) | start_idx.eidx ≤ i}
End

(* the compiler allocates names in order in blocks, one block for the initial
   compile and one for each Eval instance. however, the declarations in the
   block do not necessarily evaluate in the same order. so, idx..end_idx is
   the remaining range allocated in this block. addresses may also be held by
   other blocks, used for things in envs, or in the unallocated range
   still available to the compiler. *)
Definition idx_range_rel_def:
  idx_range_rel genv s_n_ts s_n_en s_eval idxs ⇔
    ?idx end_idx fin_idx other_blocks.
    idxs = (idx, end_idx, other_blocks) ∧
    s_eval = Eval <| compile := inc_compile; compiler_state := fin_idx |> ∧
    idx_prev end_idx fin_idx ∧
    (fin_idx.vidx = LENGTH genv.v) ∧
    ALL_DISJOINT [idx_block idx end_idx; idx_final_block fin_idx; other_blocks;
        {(i, Idx_Var) | i < LENGTH genv.v ∧ EL i genv.v <> NONE} ∪
        {(i, Idx_Type) | ?cn a. ((cn, SOME i), a) ∈ FDOM genv.c} ∪
        {(i, Idx_Exn) | ?a. ((i, NONE), a) ∈ FDOM genv.c}] ∧
    (!cn t. t ≥ s_n_ts ⇒ TypeStamp cn t ∉ FRANGE genv.c) ∧
    (!cn. cn ≥ s_n_en ⇒ ExnStamp cn ∉ FRANGE genv.c)
End

Definition invariant_def:
  invariant genv idxs s s_i1 ⇔
    genv_c_ok genv.c ∧
    s_rel genv.c s s_i1 ∧
    idx_range_rel genv s.next_type_stamp s.next_exn_stamp s_i1.eval_mode idxs ∧
    genv.v = s_i1.globals
End

Theorem can_pmatch_all_IMP_pmatch_rows2:
  can_pmatch_all env.c st.refs (MAP FST pes) v /\
  invariant genv idxs st s_i1 /\
  env_all_rel genv comp_map env env_i1 locals /\
  v_rel genv v v' ==>
  pmatch_rows
    (compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes)
    s_i1 v' ≠ Match_type_error
Proof
  rw [invariant_def]
  \\ drule_then drule can_pmatch_all_IMP_pmatch_rows
  \\ simp []
  \\ `?gv gc. genv = <| v := gv; c := gc |>`
    by simp [theorem "global_env_component_equality"]
  \\ fs [] \\ rfs []
  \\ metis_tac []
QED

val s = mk_var("s",
  ``evaluate$evaluate`` |> type_of |> strip_fun |> #1 |> el 1
  |> type_subst[alpha |-> ``:'ffi``]);

fun inst_only_tac ty (assums, goal) = let
    fun is_ty t = (type_of t = ty)
    val xs = Term.free_varsl (goal :: assums) |> filter is_ty
    val x = if length xs = 1 then hd xs
      else failwith ("inst_only_tac: " ^ Int.toString (length xs) ^
        " matching terms")
    open ConseqConv
    fun cconv dir tm = if dir <> CONSEQ_CONV_WEAKEN_direction
      then failwith "inst_only_tac: cconv: only weakens"
      else if type_of (fst (dest_forall tm)) <> ty
      then failwith "inst_only_tac: cconv: can't apply"
      else (ASSUME tm |> SPEC x |> DISCH tm)
    val depth_cc = REDEPTH_CONSEQ_CONV cconv
    fun weaken thm = MP (depth_cc CONSEQ_CONV_WEAKEN_direction (concl thm)) thm
      handle UNCHANGED => thm
  in (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o weaken) o List.rev)
    \\ TRY (CONSEQ_CONV_TAC depth_cc))
    (assums, goal)
  end

Theorem invariant_globals:
  invariant genv idxs s s_i1 ==> s_i1.globals = genv.v
Proof
  simp [invariant_def]
QED

Theorem invariant_genv_c_ok:
  invariant genv idxs s s_i1 ==> genv_c_ok genv.c
Proof
  simp [invariant_def]
QED

Theorem invariant_change_clock:
   invariant genv env st1 st2 ⇒
   invariant genv env (st1 with clock := k) (st2 with clock := k)
Proof
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases]
QED

Theorem invariant_dec_clock:
   invariant genv env st1 st2 ⇒
   invariant genv env (dec_clock st1) (dec_clock st2)
Proof
  simp [invariant_def, dec_clock_def, evaluateTheory.dec_clock_def]
  \\ simp [s_rel_cases]
QED

Theorem invariant_IMP_s_rel:
  invariant genv idxs s s_i1 ⇒ s_rel genv.c s s_i1
Proof
  simp [invariant_def]
QED

Theorem invariant_refs_rel_simple:
  invariant genv idxs s s_i1 ⇒ LIST_REL (sv_rel genv) s.refs s_i1.refs
Proof
  simp [invariant_def, s_rel_cases]
  \\ `?gv gc. genv = <| v := gv; c := gc |>`
    by simp [theorem "global_env_component_equality"]
  \\ simp []
QED

Theorem genv_norm:
  genv.v = v ==> <|v := v; c := genv.c|> = genv
Proof
  simp [theorem "global_env_component_equality"]
QED

Theorem v_rel_Bool_eqn:
  genv_c_ok genv.c ==> (v_rel genv (Boolv b) v <=> (v = Boolv b))
Proof
  rw [v_rel_eqns, Boolv_def, semanticPrimitivesTheory.Boolv_def, genv_c_ok_def,
    has_bools_def, PULL_EXISTS]
  \\ EQ_TAC \\ fs []
  \\ rw []
  \\ metis_tac []
QED

Triviality inv_v_rel_Bool_eqn:
  invariant genv idxs s s_i1 ==> (v_rel genv (Boolv b) v <=> (v = Boolv b))
Proof
  simp [invariant_def, v_rel_Bool_eqn]
QED

Theorem evaluate_Bool:
  s_rel genv_c s s' ∧ genv_c_ok genv_c ==>
  evaluate env s' [Bool t b] = (s', Rval [Boolv b])
Proof
  rw [s_rel_cases, Bool_def]
  \\ simp [evaluate_def]
  \\ fs [genv_c_ok_def, has_bools_def, FDOM_FLOOKUP]
  \\ simp [backend_commonTheory.bool_to_tag_def, Boolv_def]
  \\ every_case_tac
QED

Theorem Boolv_11:
  (Boolv b = Boolv b') = (b = b')
Proof
  simp [Boolv_def] \\ every_case_tac \\ EVAL_TAC
QED

Triviality opt_case_bool_eq:
  option_CASE opt nc sc <=> (opt = NONE /\ nc) \/ (?x. opt = SOME x /\ sc x)
Proof
  Cases_on `opt` \\ simp []
QED

Theorem bind_locals_fold_nsBind:
  nsBind nm (Local t nm) (bind_locals ts locals v_map) =
  bind_locals (t :: ts) (nm :: locals) v_map
Proof
  simp [bind_locals_def, namespaceTheory.nsBindList_def]
QED

fun PART_MATCH2 finder thm tm = let
    val thm2 = PART_MATCH finder thm tm
    val vs = Term.FVL [concl thm, tm] empty_varset
    val vs2 = Term.FVL [concl thm2] empty_varset
    val new_vs = HOLset.difference (vs2, vs)
  in GENL (HOLset.listItems new_vs) thm2 end

fun PATH_LOOKUP path =
  let
    val limit = size path
    fun dest_b t = dest_abs (rand t) handle HOL_ERR _ => dest_abs t
    fun recurse i t =
      if i = limit then t
      else
        case String.sub (path, i) of
            #"a" => recurse (i + 1) (snd (dest_abs t))
          | #"b" => recurse (i + 1) (snd (dest_b t))
          | #"l" => recurse (i + 1) (rator t)
          | #"r" => recurse (i + 1) (rand t)
          | c => failwith ("PATH_LOOKUP: invalid character: " ^ str c)
  in
    recurse 0
  end

fun part_match_pat_path_tac cont thm path pat (assums, goal) = let
    val finder = find_term (can (match_term pat))
    val inst_thm = PART_MATCH2 (finder o PATH_LOOKUP path) thm (finder goal)
  in (cont inst_thm : tactic) (assums, goal) end

fun q_part_match_pat_path_tac path q_pat (cont : thm_tactic) thm =
    Q_TAC (part_match_pat_path_tac cont thm path) q_pat

val q_part_match_pat_tac = q_part_match_pat_path_tac ""

;

Theorem compile_decs_idx_prev:
  !n next env ds n' next' env' ds_i1.
    compile_decs n next env ds = (n', next',env',ds_i1)
    ⇒
    idx_prev next next'
Proof
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def, idx_prev_def] >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []
QED

Triviality compile_decs_num_bindings = compile_decs_idx_prev
  |> REWRITE_RULE [idx_prev_def]

Triviality v_rel_eqns_non_global =
  v_rel_eqns |> BODY_CONJUNCTS
    |> filter (null o find_terms (can (match_term ``global_env_inv``)) o concl)
    |> map GEN_ALL |> LIST_CONJ

Theorem ALL_DISJOINT_SUBSETS:
  !xs ys. ALL_DISJOINT xs ∧ LIST_REL (\x y. y ⊆ x) xs ys ⇒
  ALL_DISJOINT ys
Proof
  rw [ALL_DISJOINT_DEF, LIST_REL_EL_EQN]
  \\ fs [EXTENSION, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem ALL_DISJOINT_MOVE:
  ! i j mv_set xs ys. ALL_DISJOINT xs ∧
  ys = LUPDATE (EL i xs DIFF mv_set) i (LUPDATE (EL j xs UNION mv_set) j xs) ∧
  mv_set ⊆ EL i xs ∧
  i < LENGTH xs ∧
  j < LENGTH xs
  ⇒
  ALL_DISJOINT ys
Proof
  rw [ALL_DISJOINT_DEF, LIST_REL_EL_EQN, EL_LUPDATE]
  \\ rw []
  \\ fs [EXTENSION, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem idx_range_shrink:
  idx_range_rel genv nts nes eval_mode (l_idx, r_idx, others) ∧
  idx_prev l_idx l_idx' ∧ idx_prev l_idx' r_idx
  ⇒
  idx_range_rel genv nts nes eval_mode (l_idx', r_idx, others)
Proof
  rw [idx_range_rel_def]
  \\ drule_then irule ALL_DISJOINT_SUBSETS
  \\ simp [SUBSET_DEF]
  \\ simp [idx_block_def]
  \\ fs [idx_prev_def]
  \\ rw []
QED

Theorem invariant_idx_range_shrink:
  invariant genv (l_idx, r_idx, others) st st' ∧
  idx_prev l_idx l_idx' ∧ idx_prev l_idx' r_idx
  ⇒
  invariant genv (l_idx', r_idx, others) st st'
Proof
  simp [invariant_def]
  \\ metis_tac [idx_range_shrink]
QED

Theorem pmatch_invariant:
  invariant genv idxs st st' ∧
  env_all_rel genv comp_map env <|v := []|> [] ∧
  v_rel genv v v' ⇒
  match_result_rel genv [] (pmatch env.c st.refs p v [])
    (pmatch st' (compile_pat comp_map p) v' [])
Proof
  rw [invariant_def]
  \\ `?res. pmatch env.c st.refs p v [] = res` by simp []
  \\ drule_then drule (CONJUNCT1 pmatch)
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ disch_then irule
  \\ simp [v_rel_eqns]
  \\ fs [s_rel_cases, env_all_rel_cases]
  \\ fs [Once v_rel_cases]
QED

val evaluate_make_varls = Q.prove (
  `!n t idx vars g g' s env vals len.
    s.globals = g ++ REPLICATE len NONE ++ g' ∧
    LENGTH g = idx ∧
    LENGTH vals = LENGTH vars ∧
    len = LENGTH vars ∧
    (!n. n < LENGTH vals ⇒ ALOOKUP env.v (EL n vars) = SOME (EL n vals))
    ⇒
    flatSem$evaluate env s [make_varls n t idx vars] =
    (s with globals := g ++ MAP SOME vals ++ g', Rval [flatSem$Conv NONE []])`,
  ho_match_mp_tac make_varls_ind >>
  rw [make_varls_def, evaluate_def]
  >- fs [state_component_equality]
  >- (
    every_case_tac >>
    fs [] >>
    rfs [do_app_def, state_component_equality, ALOOKUP_NONE] >>
    rw []
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_MAP] >>
      metis_tac [FST])
    >- (
      fs [EL_APPEND_EQN] >>
      `1 = SUC 0` by decide_tac >>
      full_simp_tac bool_ss [REPLICATE] >>
      fs []) >>
    `LENGTH g ≤ LENGTH g` by rw [] >>
    imp_res_tac LUPDATE_APPEND2 >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    `1 = SUC 0` by decide_tac >>
    full_simp_tac bool_ss [REPLICATE] >>
    fs [LUPDATE_compute] >>
    imp_res_tac ALOOKUP_MEM >>
    fs [] >>
    rw [] >>
    Cases_on `vals` >>
    fs [Unitv_def]) >>
  every_case_tac >>
  fs [] >>
  rfs [do_app_def, state_component_equality, ALOOKUP_NONE]
  >- (
    first_x_assum (qspec_then `0` mp_tac) >>
    simp [] >>
    CCONTR_TAC >>
    fs [] >>
    imp_res_tac ALOOKUP_MEM >>
    fs [MEM_MAP] >>
    metis_tac [FST])
  >- fs [EL_APPEND_EQN] >>
  `env with v updated_by opt_bind NONE v = env`
  by rw [environment_component_equality, libTheory.opt_bind_def] >>
  rw [] >>
 `LENGTH g ≤ LENGTH g` by rw [] >>
  imp_res_tac LUPDATE_APPEND2 >>
  full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
  fs [LUPDATE_compute] >>
  first_x_assum (qspecl_then [`g++[SOME x']`, `g'`, `q`, `env`, `TL vals`] mp_tac) >>
  simp [] >>
  Cases_on `vals` >>
  fs [] >>
  impl_tac
  >- (
    rw [] >>
    first_x_assum (qspec_then `n+1` mp_tac) >>
    simp [GSYM ADD1]) >>
  first_x_assum (qspec_then `0` mp_tac) >>
  rw [state_component_equality]);

Theorem EL_APPEND_IF:
  EL i (xs ++ ys) = if i < LENGTH xs then EL i xs else EL (i - LENGTH xs) ys
Proof
  rw [EL_APPEND1, EL_APPEND2]
QED

Theorem ALL_DISJOINT_elem:
  !x i. ALL_DISJOINT xs ∧
  i < LENGTH xs ∧
  x ∈ EL i xs ⇒
  EVERY I (MAPi (\j y. j = i ∨ x ∉ y) xs)
Proof
  simp [ALL_DISJOINT_DEF, EVERY_EL, EXTENSION]
  \\ metis_tac []
QED

Theorem idx_range_rel_v_REPLICATE_NONE:
  idx_range_rel genv nts nes eval_mode (idx, end_idx, others) ∧
  n + idx.vidx <= end_idx.vidx
  ==>
  ?pre post. genv.v = pre ++ REPLICATE n NONE ++ post ∧
    LENGTH pre = idx.vidx
Proof
  rw [idx_range_rel_def]
  \\ qexists_tac `TAKE idx.vidx genv.v`
  \\ qexists_tac `DROP (idx.vidx + n) genv.v`
  \\ fs [idx_prev_def]
  \\ qsuff_tac `!i. idx.vidx <= i /\ i < n + idx.vidx ==> EL i genv.v = NONE`
  >- (
    REWRITE_TAC [GSYM LIST_REL_eq, LIST_REL_EL_EQN]
    \\ simp [EL_APPEND_IF]
    \\ rw [] \\ rw []
    \\ simp [EL_TAKE, EL_REPLICATE, EL_DROP]
  )
  \\ rw []
  \\ qspecl_then [`(i, Idx_Var)`, `0`] drule ALL_DISJOINT_elem
  \\ simp [idx_block_def]
QED

Theorem subglobals_NONE:
  subglobals (REPLICATE n NONE) g <=> n <= LENGTH g
Proof
  csimp [subglobals_def, EL_REPLICATE]
QED

Triviality EL_add_SOME_SOME:
  EL i (pre ++ MAP SOME xs ++ post) <> NONE <=>
  (EL i (pre ++ REPLICATE (LENGTH xs) NONE ++ post) <> NONE ∨
    (LENGTH pre <= i ∧ i < LENGTH pre + LENGTH xs))
Proof
  simp [EL_APPEND_IF]
  \\ rw []
  \\ fs [EL_MAP]
QED

val ALOOKUP_alloc_defs_EL = Q.prove (
  `!funs l n m.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    n < LENGTH funs
    ⇒
    ∃tt.
    ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
      SOME (Glob tt (l + LENGTH funs − (n + 1)))`,
  gen_tac >>
  Induct_on `LENGTH funs` >>
  rw [] >>
  Cases_on `REVERSE funs` >>
  fs [alloc_defs_def] >>
  rw []
  >- (
    `LENGTH funs = n + 1` suffices_by decide_tac >>
    rfs [EL_MAP] >>
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, FST_triple] >>
    fs [ALL_DISTINCT_APPEND, MEM_MAP, FORALL_PROD] >>
    fs [MEM_EL, EL_REVERSE] >>
    `PRE (LENGTH t - n) < LENGTH t` by decide_tac >>
    fs [METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
    metis_tac [FST, pair_CASES, PAIR_EQ])
  >- (
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    Cases_on `n = LENGTH t` >>
    fs [EL_APPEND2] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, ADD1] >>
    first_x_assum (qspec_then `REVERSE t` mp_tac) >>
    simp [] >>
    fs [ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MAP_REVERSE]>>
    disch_then(qspec_then`l+1` assume_tac)>>fs[]));

val ALOOKUP_alloc_defs = Q.prove (
  `!env x v l tt.
    ALOOKUP (REVERSE env) x = SOME v
    ⇒
    ∃n t.
      ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME (Glob t (l + n)) ∧
      n < LENGTH (MAP FST env) ∧
      EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v`,
  Induct_on `env` >>
  rw [ALOOKUP_APPEND, alloc_defs_append] >>
  every_case_tac >>
  fs [alloc_defs_def]
  >- (
    PairCases_on `h` >>
    fs [EL_APPEND_EQN])
  >- (
    PairCases_on `h` >>
    fs [] >>
    first_x_assum drule >>
    disch_then (qspecl_then [`l`,`tt`] mp_tac) >>
    rw [])
  >- (
    PairCases_on `h` >>
    fs [] >>
    rw [] >>
    fs [ALOOKUP_NONE, MAP_REVERSE] >>
    drule ALOOKUP_MEM >>
    rw [] >>
    `MEM h0 (MAP FST (alloc_defs tt l (REVERSE (MAP FST env))))`
      by (rw [MEM_MAP] >> metis_tac [FST]) >>
    fs [fst_alloc_defs])
  >- (
    first_x_assum drule >>
    disch_then (qspecl_then [`l`,`tt`] mp_tac) >>
    rw [EL_APPEND_EQN]));

val global_env_inv_extend = Q.prove (
  `!pat_env genv pat_env' tt g1 g2.
    env_rel genv (alist_to_ns pat_env) pat_env' ∧
    genv.v = g1 ⧺ MAP SOME (REVERSE (MAP SND pat_env')) ⧺ g2 ∧
    ALL_DISTINCT (MAP FST pat_env)
    ⇒
    global_env_inv genv
      <|c := nsEmpty;
        v := alist_to_ns (alloc_defs tt (LENGTH g1) (REVERSE (MAP FST pat_env')))|>
      ∅
      <|v := alist_to_ns pat_env; c := nsEmpty|>`,
  rw [v_rel_eqns, extend_dec_env_def, extend_env_def, nsLookup_nsAppend_some,
      nsLookup_alist_to_ns_some] >>
  rfs [Once (GSYM alookup_distinct_reverse)] >>
  drule ALOOKUP_alloc_defs >>
  disch_then (qspecl_then [`LENGTH g1`, `tt`] strip_assume_tac) >>
  drule env_rel_dom >>
  fs [env_rel_el] >>
  rw [] >>
  fs [MAP_REVERSE, PULL_EXISTS] >>
  rw [EL_APPEND_EQN] >>
  rw [EL_REVERSE, EL_MAP] >>
  irule v_rel_weak >>
  qexists_tac `genv` >>
  rw [subglobals_def] >>
  fs [EL_APPEND_EQN] >>
  rw [] >>
  fs [EL_REPLICATE] >>
  rfs [EL_REVERSE, EL_MAP] >>
  rw []);

Theorem invariant_make_varls:
  invariant genv (idx, end_idx, others) st st' ∧
  idx.vidx = vidx ∧
  idx.vidx + LENGTH vars <= end_idx.vidx ∧
  vars = REVERSE (MAP FST env.v) ∧
  ALL_DISTINCT (MAP FST env.v)
  ⇒
  ?genv' st''.
  evaluate env st' [make_varls n t vidx vars] = (st'', Rval [Unitv]) ∧
  invariant genv' (idx with vidx := idx.vidx + LENGTH vars, end_idx, others)
    st st'' ∧
  genv'.c = genv.c ∧
  subglobals genv.v genv'.v ∧
  (!env1 tt. env_rel genv' (alist_to_ns env1) env.v ⇒
    global_env_inv genv'
      <|c := nsEmpty;
        v := alist_to_ns (alloc_defs tt vidx (REVERSE (MAP FST env.v)))|>
      ∅
      <|v := alist_to_ns env1; c := nsEmpty|>
  )
Proof
  rw [invariant_def]
  \\ drule_then drule idx_range_rel_v_REPLICATE_NONE
  \\ rw []
  \\ drule_then drule evaluate_make_varls
  \\ disch_then (q_part_match_pat_tac `evaluate _ _ _ ` mp_tac)
  \\ disch_then (qspec_then `REVERSE (MAP SND env.v)` mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    rw []
    \\ simp [GSYM MAP_REVERSE, EL_MAP, EL_REVERSE]
    \\ simp [ALOOKUP_ALL_DISTINCT_EL]
  )
  \\ rw []
  \\ simp [Unitv_def]
  \\ qexists_tac `genv with v :=
    pre ++ MAP SOME (REVERSE (MAP SND env.v)) ++ post`
  \\ simp [subglobals_refl_append, subglobals_NONE]
  \\ rpt conj_tac
  >- (
    fs [s_rel_cases]
    \\ irule LIST_REL_mono
    \\ simp [Once CONJ_COMM]
    \\ asm_exists_tac
    \\ rw []
    \\ drule_then irule sv_rel_weak
    \\ simp [subglobals_refl_append, subglobals_NONE]
  )
  >- (
    fs [idx_range_rel_def]
    \\ simp [EL_add_SOME_SOME]
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp []
    \\ qexists_tac `{(i, Idx_Var) | idx.vidx <= i /\ i < idx.vidx + LENGTH env.v}`
    \\ simp [LUPDATE_compute]
    \\ simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def,
        SUBSET_DEF]
    \\ rw []
    \\ EQ_TAC \\ rw []
    \\ simp []
  )
  >- (
    rw []
    \\ qpat_assum `LENGTH _ = _.vidx` (fn t => REWRITE_TAC [GSYM t])
    \\ irule global_env_inv_extend
    \\ imp_res_tac env_rel_dom
    \\ fs []
  )
QED

Theorem compile_funs_dom2:
  MAP FST (compile_funs t env funs) = MAP FST funs
Proof
  qspec_then `funs` mp_tac source_to_flatTheory.compile_funs_dom
  \\ simp [ELIM_UNCURRY, ETA_THM]
QED

Theorem v_to_environment:
  v_to_env v = SOME env ∧ v_rel genv v v' ⇒
  ?comp_map. v_to_environment v' = SOME comp_map ∧
  global_env_inv genv comp_map {} env
Proof
  cheat
QED

Theorem v_to_decs:
  v_to_decs v = SOME ds ∧ v_rel genv v v' ⇒
  v_to_decs v' = SOME ds
Proof
  cheat
QED

Theorem v_rel_environment_to_v:
  global_env_inv genv comp_map {} env ==>
  v_rel genv (Env env) (environment_to_v comp_map)
Proof
  cheat
QED

Theorem genv_c_ok_extend:
  genv_c_ok c ∧
  (! cn arity stamp. FLOOKUP c_ext (cn, arity) = SOME stamp ⇒
    (same_type (ExnStamp 0) stamp <=> SND cn = NONE) ∧
    (! cn' arity' stamp'. FLOOKUP c_ext (cn', arity') = SOME stamp' ⇒
      (same_type stamp stamp' <=> ctor_same_type (SOME cn) (SOME cn')) ∧
      (stamp = stamp' ⇒ (cn = cn' ∧ arity = arity'))) ∧
    (! cn' arity' stamp'. FLOOKUP c (cn', arity') = SOME stamp' ⇒
      stamp <> stamp' ∧
      (SND cn <> NONE ⇒ SND cn <> SND cn') ∧
      (! s s' n. stamp = TypeStamp s n ⇒ stamp' <> TypeStamp s' n)))
  ⇒
  genv_c_ok (FUNION c c_ext)
Proof
  rw []
  \\ fs [genv_c_ok_def]
  \\ qsuff_tac `! cn arity stamp. FLOOKUP c (cn, arity) = SOME stamp ⇒
        (same_type (ExnStamp 0) stamp <=> SND cn = NONE)`
  \\ simp [FORALL_PROD]
  \\ rpt (disch_tac ORELSE conj_tac)
  >- fs [has_bools_def, FLOOKUP_FUNION]
  >- fs [has_exns_def, FLOOKUP_FUNION]
  >- fs [has_lists_def, FLOOKUP_FUNION]
  >- (
    (* ctor same type *)
    rw []
    \\ fs [FLOOKUP_FUNION, option_case_eq]
    \\ res_tac
    \\ fs [semanticPrimitivesTheory.ctor_same_type_def, same_type_def,
            ctor_same_type_def]
    \\ fs [ctor_same_type_refl]
    \\ Cases_on `stamp1` \\ Cases_on `stamp2`
    \\ fs [semanticPrimitivesTheory.ctor_same_type_def, same_type_def,
            ctor_same_type_def]
    \\ rfs []
  )
  >- (
    rpt (gen_tac ORELSE disch_tac)
    \\ fs [FLOOKUP_FUNION, option_case_eq]
    \\ res_tac
    \\ fs []
  )
  >- (
    fs [has_exns_def, FORALL_PROD]
    \\ rw []
    \\ last_x_assum drule
    \\ disch_then (qspec_then `div_tag` drule)
    \\ simp [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def]
    \\ Cases_on `stamp`
    \\ simp [semanticPrimitivesTheory.div_stamp_def, same_type_def]
  )
QED

Theorem invariant_begin_eval:
  invariant genv (idx, end_idx, other) st st' ⇒
  st'.eval_mode = Eval e ∧ e.compiler_state = fin_idx ∧
  idx_prev fin_idx new_end_idx ∧ idx_prev new_end_idx new_fin_idx ⇒
  ? genv'. invariant genv' (fin_idx, new_end_idx, idx_block idx end_idx ∪ other)
    st (st' with <| eval_mode := Eval (e with compiler_state := new_fin_idx);
            globals := st'.globals ++
                REPLICATE (new_fin_idx.vidx - fin_idx.vidx) NONE |>) ∧
  genv'.c = genv.c ∧ subglobals genv.v genv'.v
Proof
  rw [invariant_def]
  \\ qabbrev_tac `genv' = genv with v := genv.v ++
        REPLICATE (new_fin_idx.vidx - e.compiler_state.vidx) NONE`
  \\ `subglobals genv.v genv'.v`
    by fs [markerTheory.Abbrev_def, subglobals_def, EL_APPEND1]
  \\ qexists_tac `genv'`
  \\ fs [idx_range_rel_def, s_rel_cases, idx_prev_def, markerTheory.Abbrev_def]
  \\ rveq \\ fs [] \\ rfs []
  \\ conj_tac
  >- (
    irule LIST_REL_mono
    \\ goal_assum (first_assum o mp_then (Pat `LIST_REL`) mp_tac)
    \\ rw []
    \\ drule_then irule sv_rel_weak
    \\ simp []
  )
  \\ csimp [EL_APPEND_IF, bool_case_eq, EL_REPLICATE]
  \\ qspecl_then [`0`, `2`] drule ALL_DISJOINT_MOVE
  \\ disch_then (qspec_then `idx_block idx end_idx` mp_tac)
  \\ rw [LUPDATE_compute]
  \\ qspecl_then [`1`, `0`] drule ALL_DISJOINT_MOVE
  \\ disch_then (qspec_then `idx_block fin_idx new_end_idx` mp_tac)
  \\ simp [LUPDATE_compute]
  \\ impl_tac
  >- (
    simp [idx_block_def, idx_final_block_def]
    \\ simp [SUBSET_DEF, PULL_EXISTS]
  )
  \\ rw []
  \\ drule_then irule ALL_DISJOINT_SUBSETS
  \\ simp []
  \\ simp [SUBSET_DEF, PULL_EXISTS]
  \\ rw [idx_final_block_def, idx_block_def]
QED

Theorem invariant_end_eval:
  invariant genv (fin_idx, fin_idx, idx_block idx end_idx ∪ other) st st' ∧
  invariant prev_genv (idx, end_idx, other) prev_st prev_st' ∧
  idx_prev end_idx fin_idx ⇒
  invariant genv (idx, end_idx, other) st st'
Proof
  rw [invariant_def]
  \\ fs [idx_range_rel_def]
  \\ conj_tac >- metis_tac [idx_prev_trans]
  \\ drule (Q.SPECL [`2`, `0`, `mv_set`, `[_; _; mv_set ∪ other; _]`]
        ALL_DISJOINT_MOVE)
  \\ rw [LUPDATE_compute]
  \\ drule_then irule ALL_DISJOINT_SUBSETS
  \\ simp []
  \\ simp [SUBSET_DEF, PULL_EXISTS]
  \\ imp_res_tac (Q.SPECL [`x`, `2`] ALL_DISJOINT_elem)
  \\ fs []
QED

Theorem alloc_tags1_correct:
  ! ctors ns spt tag_list.
  alloc_tags1 ctors = (ns, spt, tag_list) ∧
  ALL_DISTINCT (MAP FST ctors) ==>
  ? cn_tags.
  ns = alist_to_ns (MAP (\(cn, tag, arity). (cn, tag)) cn_tags) ∧
  set (MAP SND cn_tags) = {(tag, arity) |
    ∃max. lookup arity spt = SOME max ∧ tag < max} ∧
  tag_list = MAP SND cn_tags ∧
  ALL_DISTINCT tag_list ∧
  LIST_REL (\(cn, ts) (cn', _, arity). cn = cn' ∧ arity = LENGTH ts)
    ctors cn_tags ∧
  MAP FST ctors = MAP FST cn_tags
Proof
  ho_match_mp_tac alloc_tags1_ind
  \\ simp [alloc_tags1_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ simp [PULL_EXISTS, EXISTS_PROD, lookup_def]
  \\ qexists_tac `cn_tags`
  \\ fs [lookup_inc_def, option_case_eq] \\ rveq \\ fs []
  \\ simp [EVERY_MEM, MEM_MAP, FORALL_PROD, EXISTS_PROD]
  \\ simp [lookup_insert, EXTENSION]
  \\ rw [] \\ EQ_TAC \\ rw []
  \\ rw [] \\ fs []
  \\ fs [bool_case_eq, Q.ISPEC `SOME v` EQ_SYM_EQ]
QED

Theorem alloc_tags_invariant:
  alloc_tags idx.tidx (ctors : (string # ast_t list) list) = (ns, cids) ∧
  invariant genv (idx, end_idx, os) st st' ∧
  global_env_inv genv comp_map {} env ∧
  ALL_DISTINCT (MAP FST ctors) ∧
  idx.tidx + 1 <= end_idx.tidx
  ⇒
  ?genv'.
  genv.c ⊑ genv'.c ∧
  genv'.v = genv.v ∧
  invariant genv' (idx with tidx := idx.tidx + 1, end_idx, os)
    (st with next_type_stamp := st.next_type_stamp + 1)
    (st' with c updated_by $UNION {((idx',SOME idx.tidx),arity) |
                       (∃max. lookup arity cids = SOME max ∧ idx' < max)})
Proof
  rw [invariant_def]
  \\ fs [s_rel_cases]
  \\ fs [alloc_tags_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `ctors = []`
  >- (
    fs [alloc_tags1_def] \\ rveq \\ fs []
    \\ qexists_tac `genv`
    \\ simp [lookup_def]
    \\ fs [idx_range_rel_def]
    \\ drule_then irule ALL_DISJOINT_SUBSETS
    \\ simp []
    \\ simp [SUBSET_DEF, idx_block_def]
    \\ rw []
  )
  \\ drule alloc_tags1_correct
  \\ rw []
  \\ qexists_tac `genv with <| c := FUNION genv.c (alist_to_fmap
        (MAP (\(cn, tag, arity). (((tag, SOME idx.tidx), arity),
            TypeStamp cn st.next_type_stamp)) cn_tags)) |>`
  \\ rw [SUBMAP_FUNION_ID]
  >- (
    drule_then irule genv_c_ok_extend
    \\ rw [FORALL_PROD]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [MEM_MAP, EXISTS_PROD] \\ rveq \\ fs []
    \\ simp [same_type_def, ctor_same_type_def]
    \\ rveq \\ fs []
    \\ imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM
    \\ fs []
    \\ TRY strip_tac
    \\ rveq \\ fs []
    \\ fs [idx_range_rel_def]
    \\ rfs [FRANGE_FLOOKUP]
    \\ qspecl_then [`(i,Idx_Type)`, `0`] drule ALL_DISJOINT_elem
    \\ simp [idx_block_def]
    \\ qexists_tac `idx.tidx`
    \\ simp [FDOM_FLOOKUP]
    \\ metis_tac []
  )
  >- (
    irule LIST_REL_mono >>
    goal_assum (first_assum o mp_then (Pat `LIST_REL`) mp_tac) >>
    rw [] >>
    irule sv_rel_weak >>
    goal_assum (first_assum o mp_then (Pat `sv_rel`) mp_tac) >>
    simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    fs [EXTENSION, FORALL_PROD, MEM_MAP, EXISTS_PROD]
    \\ metis_tac []
  )
  >- (
    fs [idx_range_rel_def]
    \\ rw []
    \\ fs [FRANGE_FLOOKUP, FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
    \\ TRY (CCONTR_TAC \\ fs [] \\ imp_res_tac ALOOKUP_MEM
      \\ fs [MEM_MAP, EXISTS_PROD] \\ NO_TAC)
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp [LUPDATE_compute]
    \\ qexists_tac `{(idx.tidx, Idx_Type)}`
    \\ simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def]
    \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ rw [] \\ EQ_TAC \\ rw []
    \\ fs [NOT_NIL_EQ_LENGTH_NOT_0, quantHeuristicsTheory.LIST_LENGTH_2]
    \\ rveq \\ fs [EXISTS_PROD]
    \\ metis_tac []
  )
QED

Theorem compile_correct:
  (∀ ^s env es s' r genv comp_map env_i1 ^s_i1 es_i1 locals t ts idxs.
    evaluate$evaluate s env es = (s', r) ∧
    invariant genv idxs s s_i1 ∧
    env_all_rel genv comp_map env env_i1 locals ∧
    LENGTH ts = LENGTH locals ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    es_i1 = compile_exps t (comp_map with v := bind_locals ts locals comp_map.v) es
    ⇒
    ?s'_i1 r_i1 genv'.
    flatSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) ∧
    result_rel (LIST_REL o v_rel) genv' r r_i1 ∧
    invariant genv' idxs s' s'_i1 ∧
    genv.c SUBMAP genv'.c ∧
    subglobals genv.v genv'.v) ∧
  (∀ ^s env v pes err_v genv comp_map s' r env_i1 ^s_i1 v_i1 pes_i1
         err_v_i1 locals t ts idxs.
    evaluate$evaluate_match s env v pes err_v = (s', r) ∧
    invariant genv idxs s s_i1 ∧
    env_all_rel genv comp_map env env_i1 locals ∧
    v_rel genv v v_i1 ∧
    LENGTH ts = LENGTH locals ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    pes_i1 = compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes ∧
    pmatch_rows pes_i1 s_i1 v_i1 <> Match_type_error ∧
    v_rel genv err_v err_v_i1
    ⇒
    ?s'_i1 r_i1 genv'.
    flatProps$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) ∧
    result_rel (LIST_REL o v_rel) genv' r r_i1 ∧
    invariant genv' idxs s' s'_i1 ∧
    genv.c SUBMAP genv'.c ∧
    subglobals genv.v genv'.v) ∧
  (∀ ^s env ds s' r t idx end_idx os comp_map ^s_i1 idx' comp_map' ds_i1 t'
        genv.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    invariant genv (idx, end_idx, os) s s_i1 ∧
    source_to_flat$compile_decs t idx comp_map ds = (t', idx', comp_map', ds_i1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    global_env_inv genv comp_map {} env ∧
    idx_prev idx' end_idx
    ⇒
    ? ^s1_i1 genv' r_i1.
    flatSem$evaluate_decs s_i1 ds_i1 = (s1_i1,r_i1) ∧
    invariant genv' (idx', end_idx, os) s' s1_i1 ∧
    genv.c SUBMAP genv'.c ∧
    subglobals genv.v genv'.v ∧
    (!env'.
      r = Rval env'
      ⇒
      r_i1 = NONE ∧
      env_domain_eq comp_map' env' ∧
      global_env_inv genv' comp_map' {} env') ∧
    (!err.
      r = Rerr err
      ⇒
      ?err_i1.
        r_i1 = SOME err_i1 ∧
        result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))
  )

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rw [terminationTheory.full_evaluate_def, flat_evaluate_def,
    compile_exp_def, compile_decs_def]
  \\ fs [result_rel_eqns, v_rel_eqns_non_global]
  \\ TRY (
    (* trivial cases *)
    goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac)
    \\ simp [subglobals_refl]
    \\ NO_TAC
  )
  >- ( (* sequencing *)
    fs [pair_case_eq] \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ reverse (fs [result_case_eq])
    >- (
      rveq \\ fs []
      \\ rw []
      \\ fs [result_rel_cases]
      \\ asm_exists_tac \\ simp []
    )
    \\ fs [pair_case_eq]
    \\ rveq \\ fs []
    \\ rw []
    \\ fs [result_rel_cases]
    \\ rveq \\ fs []
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ first_x_assum (drule_then (drule_then drule))
    \\ impl_tac >- (CCONTR_TAC >> fs [])
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
    \\ rw [] \\ fs [] \\ rveq \\ fs []
    \\ metis_tac [v_rel_weak, SUBMAP_TRANS, subglobals_trans]
  )
  >- (
    (* Raise *)
    fs [pair_case_eq]
    \\ rveq \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ fs [result_rel_cases] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ imp_res_tac evaluate_sing
    \\ rveq \\ fs []
    \\ asm_exists_tac \\ simp []
  )
  >- ( (* Handle *)
    fs [pair_case_eq] \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs []
    \\ TRY (asm_exists_tac \\ simp [])
    \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ first_x_assum (drule_then drule)
    \\ rpt (disch_then drule)
    \\ disch_then (first_assum o mp_then (Pat `v_rel`) mp_tac)
    \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows2]
    \\ rw [] \\ fs []
    \\ metis_tac [SUBMAP_TRANS, subglobals_trans]
  )
  >- ( (* Constructors *)
    fs [pair_case_eq] \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ fs [do_con_check_def, opt_case_bool_eq, EXISTS_PROD]
    >- (
      (* tuple *)
      rfs [build_conv_def, compile_exps_reverse, evaluate_def]
      \\ goal_assum (first_assum o mp_then (Pat `subglobals`) mp_tac)
      \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
      \\ simp [v_rel_eqns]
    )
    (* named constructor *)
    \\ rveq \\ fs [build_conv_def, compile_exps_reverse, evaluate_def]
    \\ fs [env_all_rel_cases] \\ rveq \\ fs []
    \\ fs [v_rel_eqns]
    \\ first_x_assum drule
    \\ rw [EXISTS_PROD]
    \\ goal_assum (first_assum o mp_then (Pat `subglobals`) mp_tac)
    \\ simp [type_group_id_type_MAP, evaluate_def]
    \\ fs [invariant_def, s_rel_cases, FDOM_FLOOKUP, compile_exps_length]
    \\ rfs []
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
    \\ simp [v_rel_eqns]
    \\ imp_res_tac evaluatePropsTheory.evaluate_length
    \\ fs []
    \\ metis_tac [FLOOKUP_SUBMAP]
  )
  >- ((* Variable lookup *)
    fs [option_case_eq]
    \\ fs [env_all_rel_cases]
    \\ rveq \\ fs []
    \\ fs [nsLookup_nsAppend_some]
    >- ((* Local variable *)
      fs [nsLookup_alist_to_ns_some,bind_locals_def] >>
      rw [] >>
      drule env_rel_lookup >>
      disch_then drule >>
      rw [GSYM nsAppend_to_nsBindList] >>
      simp[MAP2_MAP]>>
      every_case_tac >>
      fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
          nsLookup_alist_to_ns_none,evaluate_def]>>
      fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
      `(λ(p1:tra,p2:tvarN). p2) = SND` by fs[FUN_EQ_THM,FORALL_PROD]>>
      fs[]>>rfs[MAP_ZIP]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL, subglobals_refl]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL, subglobals_refl]
      >- (
        drule ALOOKUP_MEM >>
        rw [MEM_MAP] >>
        pairarg_tac>>fs[compile_var_def]>>
        simp [evaluate_def, result_rel_cases] >>
        metis_tac [SUBMAP_REFL, subglobals_refl])
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP])
    >- ( (* top-level variable *)
      rw [GSYM nsAppend_to_nsBindList,bind_locals_def] >>
      fs [nsLookup_alist_to_ns_none] >>
      fs [v_rel_eqns, ALOOKUP_NONE, METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
      first_x_assum drule >>
      rw [] >>
      simp[MAP2_MAP]>>
      every_case_tac >>
      fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
          nsLookup_alist_to_ns_none]>>
      fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]
      >- (Cases_on`p1`>>fs[])
      >- (
        drule ALOOKUP_MEM >>
        simp[MEM_MAP,MEM_ZIP,EXISTS_PROD]>>
        rw[]>>
        metis_tac[MEM_EL,LENGTH_MAP])
      >- (
        rfs [ALOOKUP_TABULATE] >>
        rw [] >>
        simp [evaluate_def, result_rel_cases,compile_var_def] >>
        simp [do_app_def] >>
        imp_res_tac invariant_globals >>
        fs [] >>
        metis_tac [subglobals_refl, SUBMAP_REFL])))
  >- (* Closure creation *)
     (
      rw [Once v_rel_cases] >>
      goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
      fs [env_all_rel_cases, subglobals_refl] >>
      srw_tac[][] >>
      rename [`global_env_inv genv comp_map (set (MAP FST locals)) env`] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `alist_to_ns locals`,`t`,`(t§2)::ts`] >>
      imp_res_tac env_rel_dom >>
      srw_tac[][] >>
      simp [bind_locals_def, namespaceTheory.nsBindList_def] >>
      fs [ADD1]
      >- metis_tac [sem_env_eq_lemma]
      >- metis_tac[LENGTH_MAP]
  )
  >- (
    (* App *)
    srw_tac [boolSimps.DNF_ss] [PULL_EXISTS]
    >- (
      (* empty array creation *)
      inst_only_tac ``: tra``
      \\ fs [pair_case_eq] \\ fs []
      \\ first_x_assum (drule_then (drule_then drule))
      \\ (impl_tac >- (CCONTR_TAC \\ fs []))
      \\ fs [semanticPrimitivesTheory.do_app_def]
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      >- (
        drule (CONJUNCT1 evaluatePropsTheory.evaluate_length) >>
        rw [] >>
        fs [quantHeuristicsTheory.LIST_LENGTH_2] >>
        rveq >> fs [] >>
        simp [compile_exp_def, evaluate_def] >>
        pairarg_tac >>
        fs [store_alloc_def, compile_exp_def] >>
        rpt var_eq_tac >>
        fs [result_rel_cases, Once v_rel_cases] >>
        simp [do_app_def] >>
        pairarg_tac >>
        fs [store_alloc_def] >>
        goal_assum (first_assum o mp_then (Pat `subglobals`) mp_tac) >>
        fs [invariant_def, s_rel_cases] >>
        rw []
        >- metis_tac [LIST_REL_LENGTH] >>
        simp [REPLICATE, sv_rel_cases])
      >- (
        rw [] >>
        goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
        fs [compile_exps_reverse] >>
        fs [result_rel_cases] >> rveq >> fs [] >>
        drule evaluate_foldr_let_err >>
        simp []
        )) >>
    fs [] >>
    fs [pair_case_eq] >>
    reverse (fs [result_case_eq]) >> rveq >> fs []
    >- (
      (* Rerr *)
      inst_only_tac ``: tra`` >>
      first_x_assum (drule_then (drule_then drule)) >>
      rw [evaluate_def] >>
      fs [compile_exps_reverse] >>
      goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
      fs [result_rel_cases]
    )
    \\ first_x_assum (drule_then (drule_then drule))
    (* trace has to be picked the annoying way because of the Eval case *)
    \\ rename [`compile_exps trace`]
    \\ disch_then (qspec_then `trace` mp_tac)
    \\ rw []
    \\ Cases_on `op = Eval`
    >- (
      fs []
      \\ simp [astOp_to_flatOp_def, evaluate_def]
      \\ fs [list_case_eq, option_case_eq]
      \\ rveq \\ fs []
      \\ fs [bool_case_eq]
      (* there's a problem with when the clocks are checked in Eval *)
      >- cheat
      \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
      \\ fs [result_rel_eqns] \\ rveq \\ fs []
      \\ fs [compile_exps_reverse]
      \\ simp [do_eval_def]
      \\ qpat_assum `invariant _ _ _ _` (mp_tac o REWRITE_RULE [invariant_def])
      \\ rw [idx_range_rel_def]
      \\ simp []
      \\ drule_then drule v_to_environment
      \\ drule_then drule v_to_decs
      \\ rw []
      \\ simp [inc_compile_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ fs [s_rel_cases]
      \\ rveq \\ fs []
      \\ drule_then assume_tac invariant_dec_clock
      \\ simp [glob_alloc_def, evaluate_def, do_app_def, Unitv_def]
      \\ simp [EVAL ``(dec_clock s).globals``]
      \\ drule invariant_begin_eval
      \\ fs [dec_clock_def]
      \\ rename [`compile_decs 0 _ _ _ = (_, new_fin_idx, _, _)`]
      \\ disch_then (qspecl_then [`new_fin_idx`, `new_fin_idx`] mp_tac)
      \\ imp_res_tac compile_decs_idx_prev
      \\ rw [idx_prev_refl]
      \\ last_x_assum (drule_then drule)
      \\ simp [idx_prev_refl]
      \\ drule_then (fn t => simp [t]) global_env_inv_weak
      \\ impl_tac >- (strip_tac \\ fs [])
      \\ rw []
      \\ simp []
      \\ drule_then drule invariant_end_eval
      \\ (impl_tac >- metis_tac [idx_prev_trans])
      \\ rw []
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac)
      \\ imp_res_tac result_rel_imp \\ fs [result_rel_eqns]
      \\ metis_tac [subglobals_trans, SUBMAP_TRANS, v_rel_environment_to_v,
            global_env_inv_append, global_env_inv_weak, subglobals_refl]
    ) >>
    fs [bool_case_eq]
    >- (
      fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq, option_case_eq] >>
      rveq >> fs [] >>
      fs [astOp_to_flatOp_def, evaluate_def, compile_exps_reverse] >>
      fs [result_rel_eqns] >> rveq >> fs [] >>
      drule_then assume_tac EVERY2_REVERSE >>
      drule_then drule do_opapp >>
      rw [] >>
      drule invariant_IMP_s_rel >>
      rw [s_rel_cases]
      >- (
        (* out of clock *)
        fs [] >> rveq >> fs [] >>
        goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
        simp [result_rel_eqns]
      ) >>
      fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] >>
      drule_then assume_tac invariant_dec_clock >>
      first_x_assum (drule_then (drule_then drule)) >>
      metis_tac [SUBMAP_TRANS, subglobals_trans, SUBSET_TRANS]
    ) >>
    fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, option_case_eq, pair_case_eq] >>
    rveq >> fs [] >>
    fs [result_rel_eqns] >> rveq >> fs [] >>
    drule_then assume_tac EVERY2_REVERSE >>
    imp_res_tac invariant_refs_rel_simple >>
    drule do_app >> simp [] >>
    rpt (disch_then drule) >>
    (impl_tac >- fs [invariant_def, s_rel_cases]) >>
    rw [] >>
    `astOp_to_flatOp op ≠ Opapp ∧ astOp_to_flatOp op ≠ Eval`
    by (
      rw [astOp_to_flatOp_def] >>
      Cases_on `op` >>
      simp [] >>
      fs []) >>
    fs [evaluate_def, compile_exps_reverse] >>
    imp_res_tac do_app_state_unchanged >>
    imp_res_tac do_app_const >>
    rename [`result_rel v_rel genv2`] >>
    qexists_tac `genv2` >>
    simp [] >>
    conj_tac >> TRY (fs [result_rel_cases] \\ NO_TAC) >>
    fs [invariant_def, s_rel_cases] >>
    simp [genv_norm]
  )
  >- ( (* logical operation *)
    fs [pair_case_eq] >> fs [] >>
    inst_only_tac ``: tra`` >>
    first_x_assum (drule_then (drule_then drule)) >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    rw [] >>
    reverse (fs [result_case_eq]) >> rveq >> fs []
    >- (
      goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
      fs [result_rel_cases] >> rveq >> fs [] >>
      every_case_tac >>
      simp [evaluate_def]
    ) >>
    imp_res_tac evaluatePropsTheory.evaluate_sing >>
    reverse (fs [option_case_eq, exp_or_val_case_eq, result_rel_eqns])
    >- (
      rveq >> fs [] >>
      fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs [] >>
      goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
      fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
      drule_then (fn t => simp [t]) evaluate_Bool >>
      simp [result_rel_eqns, v_rel_Bool_eqn]
    ) >>
    fs [] >> rveq >> fs [] >>
    drule_then drule env_all_rel_weak >>
    rw [] >>
    first_x_assum (drule_then (drule_then drule)) >>
    rw [] >>
    goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
    fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs [] >>
    fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
    metis_tac [subglobals_trans, SUBMAP_TRANS]
  )
  >- ( (* if *)
    fs [pair_case_eq] >> fs [] >>
    inst_only_tac ``: tra`` >>
    first_x_assum (drule_then (drule_then drule)) >>
    (impl_tac >- (CCONTR_TAC >> fs [])) >>
    rw [] >>
    imp_res_tac result_rel_imp >> rveq >> fs [] >> rveq >> fs [result_rel_eqns] >>
    TRY (asm_exists_tac >> simp [] >> NO_TAC) >>
    fs [option_case_eq] >> fs [] >>
    drule_then drule env_all_rel_weak >>
    rw [] >>
    first_x_assum (drule_then (drule_then drule)) >>
    rw [] >>
    imp_res_tac evaluatePropsTheory.evaluate_sing >>
    goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
    fs [semanticPrimitivesTheory.do_if_def, bool_case_eq] >> rveq >> fs [] >>
    fs [invariant_def, do_if_def] >>
    rfs [v_rel_Bool_eqn, Boolv_11] >>
    metis_tac [subglobals_trans, SUBMAP_TRANS]
  )
  >- ( (* Mat *)
    fs [pair_case_eq] \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ (impl_tac >- (CCONTR_TAC >> fs []))
    \\ rw []
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
    \\ TRY (asm_exists_tac \\ simp [])
    \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ fs [] \\ rveq \\ fs []
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ first_x_assum (drule_then (drule_then (drule_then drule)))
    \\ disch_then (qspec_then `bind_exn_v` mp_tac)
    \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows2]
    \\ conj_tac >- metis_tac []
    \\ impl_tac >- (fs [invariant_def, v_rel_lems])
    \\ rw []
    \\ simp []
    \\ metis_tac [SUBMAP_TRANS, subglobals_trans]
  )
  >- ( (* Let *)
    fs [pair_case_eq] \\ fs []
    \\ inst_only_tac ``: tra``
    \\ first_x_assum (drule_then (drule_then drule))
    \\ (impl_tac >- (CCONTR_TAC >> fs []))
    \\ rw []
    \\ rename [`Let opt_name _ _`]
    \\ Cases_on `opt_name`
    >- (
      (* anonymous bind *)
      simp [compile_exp_def, evaluate_def]
      \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
      \\ TRY (asm_exists_tac \\ simp [])
      \\ fs [namespaceTheory.nsOptBind_def]
      \\ drule_then drule env_all_rel_weak
      \\ rw []
      \\ first_x_assum (drule_then (drule_then drule))
      \\ rw []
      \\ simp [Q.prove (`env with v updated_by opt_bind NONE x = env`,
            simp [environment_component_equality,libTheory.opt_bind_def] )]
      \\ metis_tac [SUBMAP_TRANS, subglobals_trans]
    )
    \\ simp [compile_exp_def, evaluate_def]
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
    \\ TRY (asm_exists_tac \\ simp [])
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ imp_res_tac evaluate_sing
    \\ fs [] \\ rveq \\ fs []
    \\ simp [bind_locals_fold_nsBind]
    \\ last_x_assum (q_part_match_pat_tac `evaluate _ _ _ ` mp_tac)
    \\ disch_then drule
    \\ impl_tac >- (
      fs [env_all_rel_cases]
      \\ fs [namespaceTheory.nsOptBind_def, libTheory.opt_bind_def]
      \\ simp [PULL_EXISTS, listTheory.MAP_EQ_CONS, EXISTS_PROD]
      \\ metis_tac [env_rel_bind_one, pred_setTheory.INSERT_SING_UNION,
        global_env_inv_add_locals]
    )
    \\ rw []
    \\ simp []
    \\ metis_tac [SUBMAP_TRANS, subglobals_trans]
  )
  >- ( (* let rec *)
    fs [pair_case_eq] >>
    rw [evaluate_def] >>
    TRY (fs [compile_funs_map,MAP_MAP_o,o_DEF,UNCURRY] >>
         full_simp_tac(srw_ss())[FST_triple,ETA_AX] >>
         NO_TAC) >>
    fs [GSYM nsAppend_to_nsBindList] >>
    rw_tac std_ss [GSYM MAP_APPEND] >>
    simp[nsAppend_bind_locals]>>
    first_x_assum match_mp_tac >> simp[] >>
    full_simp_tac(srw_ss())[env_all_rel_cases] >>
    rw [] >>
    qexists_tac `build_rec_env funs <|v := nsAppend (alist_to_ns l) env'.v; c := env'.c|> (alist_to_ns l)` >>
    qexists_tac `env'` >>
    rw [semanticPrimitivesPropsTheory.build_rec_env_merge,build_rec_env_merge]
    >- (
      simp [MAP_MAP_o, UNCURRY, combinTheory.o_DEF] >>
      metis_tac [])
    >- metis_tac [global_env_inv_add_locals] >>
    rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
    match_mp_tac env_rel_append >>
    rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    rw [env_rel_el, EL_MAP, UNCURRY] >>
    simp [Once v_rel_cases] >>
    qexists_tac `comp_map` >>
    qexists_tac `env'` >>
    qexists_tac `alist_to_ns l` >>
    qexists_tac `t` >>
    qexists_tac `REPLICATE (LENGTH funs) t ++ ts` >>
    drule env_rel_dom >>
    rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY,
        bind_locals_def, nsAppend_to_nsBindList] >>
    rw [sem_env_component_equality]
    >- metis_tac[]
    >- metis_tac [LENGTH_MAP])
  >- (Cases_on`l`>>fs[evaluate_def,compile_exp_def])
  >- ( (* pattern *)
    fs [pair_case_eq] >>
    fs [match_result_case_eq] >> fs []
    >- (
      rfs[] >>
      imp_res_tac invariant_def >>
      drule_then drule (GEN_ALL (CONJUNCT1 pmatch)) >>
      simp [semanticPrimitivesTheory.state_component_equality] >>
      disch_then (q_part_match_pat_tac `pmatch _ _ _ _` mp_tac) >>
      simp [v_rel_eqns] >>
      impl_tac >- fs [v_rel_eqns, env_all_rel_cases] >>
      strip_tac >>
      imp_res_tac match_result_rel_imp >> fs [] >>
      last_x_assum (q_part_match_pat_tac `evaluate_match _ _ _ _ _` mp_tac) >>
      disch_then drule >>
      fs [pmatch_rows_def]
    ) >>
    rfs [] >>
    imp_res_tac invariant_def >>
    drule_then drule (GEN_ALL (CONJUNCT1 pmatch)) >>
    simp[semanticPrimitivesTheory.state_component_equality] >>
    disch_then (q_part_match_pat_tac `pmatch _ _ _ _` mp_tac) >>
    simp [v_rel_eqns] >>
    impl_tac >- fs [v_rel_eqns, env_all_rel_cases] >>
    strip_tac >>
    imp_res_tac match_result_rel_imp >> fs [] >>
    q_part_match_pat_tac `nsBindList _ _` assume_tac
      (GEN_ALL nsBindList_pat_tups_bind_locals) >>
    fs [] >>
    last_x_assum (q_part_match_pat_tac `evaluate _ _ _` mp_tac) >>
    disch_then drule >>
    simp[]>>
    reverse IF_CASES_TAC THEN1 fs [pmatch_rows_def] >>
    impl_tac >> fs [] >>
    simp[s_rel_cases] >>
    fs [env_all_rel_cases, match_result_rel_def] >>
    rveq >> fs [] >>
    rw [environment_component_equality, sem_env_component_equality] >>
    qexists_tac `alist_to_ns (env1 ++ l)` >>
    qexists_tac`env'` >>
    rw []
    >- (
      drule (CONJUNCT1 pmatch_extend) >>
      drule env_rel_dom >>
      rw [])
    >- metis_tac [global_env_inv_add_locals]
    >- (
      rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
      match_mp_tac env_rel_append >>
      rw [])
  )
  >- (
    (* no decs *)
    asm_exists_tac \\ simp []
    \\ simp [v_rel_eqns, subglobals_refl, empty_env_def, env_domain_eq_def]
  )
  >- (
    (* sequence of decs *)
    fs [pair_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ first_x_assum (drule_then drule)
    \\ imp_res_tac compile_decs_idx_prev
    \\ (impl_tac >- (imp_res_tac idx_prev_trans
        \\ simp [] \\ CCONTR_TAC \\ fs []))
    \\ rw []
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq \\ fs []
    >- (
      drule evaluate_decs_append_err
      \\ rw []
      \\ goal_assum (first_assum o mp_then (Pat `result_rel`) mp_tac)
      \\ fs [invariant_def]
      \\ drule_then irule idx_range_shrink
      \\ simp []
    )
    \\ fs [pair_case_eq] \\ fs []
    \\ drule_then drule global_env_inv_weak
    \\ rw []
    \\ first_x_assum (drule_then drule)
    \\ simp [global_env_inv_append]
    \\ (impl_tac >- (CCONTR_TAC \\ fs [combine_dec_result_def]))
    \\ rw []
    \\ drule_then drule evaluate_decs_append
    \\ rw []
    \\ asm_exists_tac
    \\ simp [combine_dec_result_def, result_case_eq]
    \\ rw []
    \\ TRY (drule_then irule subglobals_trans)
    \\ TRY (drule_then irule SUBMAP_TRANS)
    \\ simp []
    >- (
      imp_res_tac env_domain_eq_append
      \\ fs [extend_dec_env_def]
    )
    >- (
      q_part_match_pat_path_tac "r" `global_env_inv _ _` mp_tac
        global_env_inv_append
      \\ imp_res_tac global_env_inv_weak
      \\ disch_then imp_res_tac
      \\ fs [extend_dec_env_def]
    )
  )
  >- ( (* Let *)
    fs [pair_case_eq] >> fs [] >>
    `env_all_rel genv comp_map env <|v := []|> []`
      by (simp [env_all_rel_cases] \\ simp [v_rel_rules]) >>
    first_x_assum (drule_then drule) >>
    simp [bind_locals_def, EVAL ``nsBindList [] ns``] >>
    simp [bind_locals_def] >>
    simp [Q.prove (`(x with v := x.v) = (x : source_to_flat$environment)`,
        simp [source_to_flatTheory.environment_component_equality])] >>
    disch_then (q_part_match_pat_tac `evaluate _ _ _` mp_tac) >>
    (impl_tac >- (CCONTR_TAC >> fs [])) >>
    rw [] >>
    simp [] >>
    drule invariant_idx_range_shrink >>
    disch_then (q_part_match_pat_tac `(_, _, _)` mp_tac) >>
    simp [] >>
    (impl_tac >- simp [idx_prev_def]) >>
    rw [] >>
    imp_res_tac result_rel_imp >> fs [] >> rveq >> fs [result_rel_eqns] >>
    TRY (asm_exists_tac >> simp []) >>
    imp_res_tac evaluate_sing >>
    fs [] >> rveq >> fs [pmatch_rows_def] >>
    drule_then drule env_all_rel_weak >>
    simp [] >> disch_tac >>
    drule pmatch_invariant >>
    disch_then (q_part_match_pat_tac `pmatch _ _ _ _ _` mp_tac) >>
    disch_then (q_part_match_pat_tac `flatSem$pmatch _ _ _` mp_tac) >>
    simp [] >> disch_tac >>
    imp_res_tac invariant_genv_c_ok >>
    imp_res_tac match_result_rel_imp >> fs [] >>
    TRY (asm_exists_tac >> simp [result_rel_eqns, v_rel_lems]) >>
    fs [match_result_rel_def] >>
    drule (CONJUNCT1 pmatch_bindings) >>
    rw [] >>
    qpat_x_assum `invariant _ (_ with vidx := _, _, _) _ _` kall_tac >>
    drule invariant_make_varls >>
    disch_then (q_part_match_pat_tac `evaluate _ _ _` mp_tac) >>
    simp [] >>
    (impl_tac >- fs [idx_prev_def]) >>
    rw [] >>
    simp [] >>
    asm_exists_tac >> simp [] >>
    rw []
    >- (
      metis_tac [subglobals_trans]
    )
    >- (
      simp [env_domain_eq_def] >>
      simp [GSYM MAP_MAP_o, fst_alloc_defs, EXTENSION] >>
      rw [MEM_MAP] >>
      imp_res_tac env_rel_dom >>
      fs [] >>
      metis_tac [FST, MEM_MAP]
    )
    >- (
      first_x_assum irule >>
      metis_tac [env_rel_weak, SUBMAP_REFL]
    )
  )
  >- ( (* Letrec *)
    fs [ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
    \\ simp [compile_funs_dom2]
    \\ drule invariant_make_varls
    \\ disch_then (q_part_match_pat_tac `evaluate _ _ _` mp_tac)
    \\ simp []
    \\ impl_tac
    >- (
      simp [build_rec_env_merge, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
      \\ simp [compile_funs_dom2]
      \\ fs [idx_prev_def]
    )
    \\ rw []
    \\ simp []
    \\ asm_exists_tac
    \\ fs [build_rec_env_merge, MAP_MAP_o, o_DEF]
    \\ conj_tac
    >- (
      simp [env_domain_eq_def]
      \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
      \\ simp [GSYM MAP_MAP_o, fst_alloc_defs]
      \\ simp [MAP_MAP_o, o_DEF, ELIM_UNCURRY, MAP_REVERSE]
    )
    \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
    \\ fs [MAP_MAP_o, o_DEF, ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
    \\ fs [compile_funs_dom2]
    \\ first_x_assum irule
    \\ simp [source_to_flatTheory.compile_funs_map, MAP_MAP_o]
    \\ simp [env_rel_LIST_REL, EVERY2_MAP]
    \\ irule EVERY2_refl
    \\ simp [FORALL_PROD]
    \\ simp [Once v_rel_cases]
    \\ rw [source_to_flatTheory.compile_funs_map, MAP_EQ_f, FORALL_PROD]
    \\ qexistsl_tac [`comp_map`, `env`, `nsEmpty`, `None`, `MAP (K None) funs`]
    \\ simp []
    \\ drule_then (fn t => simp [t]) global_env_inv_weak
    \\ rw []
    \\ simp [bind_locals_def, MAP2_MAP, ZIP_MAP, MAP_MAP_o, o_DEF, v_rel_rules]
  )

  >- ( (* Type definition *)

    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [`genv`, `idx`, `comp_map`, `env`, `s`, `s_i1`] >>
    Induct_on `tds`
    >- ( (* No tds *)
      rw [evaluate_def] >>
      simp [build_tdefs_def, v_rel_eqns, env_domain_eq_def] >>
      qexists_tac `genv` >>
      simp [subglobals_refl] >>
      fs [invariant_def, s_rel_cases] >>
      simp [Q.prove (`(n with tidx := n.tidx) = n`,
        simp [next_indices_component_equality])]
    ) >>
    strip_tac >>
    rename [`EVERY check_dup_ctors (td::tds)`] >>
    `?tvs tn ctors. td = (tvs, tn ,ctors)` by metis_tac [pair_CASES] >>
    rw [evaluate_def] >>
    pairarg_tac >>
    fs [] >>
    simp [evaluate_def] >>

    drule evaluate_alloc_tags >>
    disch_then drule >>
    simp [lookup_def] >>
    impl_tac
    >- (
      fs [terminationTheory.check_dup_ctors_thm] >>
      fs [invariant_def]) >>
    reverse (rw [])
    >- (
      fs [is_fresh_type_def, invariant_def] >>
      rw [] >>
      fs[s_rel_cases] >>
      metis_tac [DECIDE ``!x:num. x ≥ x``]) >>
    first_x_assum drule >>
    fs [local_c_rel_def] >>
    disch_then (first_assum o mp_then (Pat `global_env_inv`) mp_tac) >>
    impl_keep_tac
    >- (
      fs [SUBSET_DEF]
      \\ drule_then irule alloc_tags_local_c_rel1
      \\ fs [terminationTheory.check_dup_ctors_thm]
    ) >>
    rw [] >>
    qpat_x_assum `_ = FDOM _` (mp_tac o GSYM) >>
    rw [] >>
    fs [combinTheory.o_DEF, LAMBDA_PROD] >>
    fs [] >>
    `!x y. SUC x + y = x + SUC y` by decide_tac >>
    asm_simp_tac std_ss [] >>
    rw [] >>
    qmatch_goalsub_abbrev_tac`evaluate_decs xxx` >>
    qmatch_asmsub_abbrev_tac`evaluate_decs xxy` >>
    `xxx = xxy` by (
      simp[Abbr`xxx`,Abbr`xxy`,state_component_equality]
      \\ fs[invariant_def, s_rel_cases] )
    \\ fs[UNION_COMM] \\
    qexists_tac `genv'` >>
    rw []
    >- (
      irule funion_submap >>
      qexists_tac `genv_c` >>
      rw [DISJOINT_DEF, EXTENSION] >>
      CCONTR_TAC >>
      fs [] >>
      rw [] >>
      fs [FLOOKUP_DEF, invariant_def] >>
      metis_tac [DECIDE ``!x. x ≥ x:num``])
    >- (
      fs [env_domain_eq_def, build_tdefs_def, ADD1] >>
      ONCE_REWRITE_TAC [nsAppend_foldl] >>
      rw [build_tdefs_no_mod, nsDom_nsAppend_flat, nsDomMod_nsAppend_flat,
          o_DEF, build_constrs_def, MAP_REVERSE, MAP_MAP_o, EXTENSION] >>
      eq_tac >>
      rw [MEM_MAP, EXISTS_PROD] >>
      metis_tac [FST])
   >- (
      fs [build_tdefs_def, v_rel_eqns] >>
      rw [] >>
      fs [nsLookup_nsAppend_some, ADD1]
      >- (
        res_tac >>
        qexists_tac `cn` >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some])
      >- (
        fs [build_constrs_def, nsLookup_alist_to_ns_some, env_domain_eq_def] >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some] >>
        qmatch_goalsub_abbrev_tac `nsLookup rest _ = SOME _` >>
        `nsLookup rest (Short x') = NONE`
        by (
          fs [nsLookup_nsDom, EXTENSION] >>
          metis_tac [NOT_SOME_NONE, option_nchotomy]) >>
        simp [] >>
        res_tac >>
        fs [namespaceTheory.id_to_mods_def] >>
        metis_tac [flookup_funion_submap]))
    >- (
      simp [Once nsAppend_foldl, build_tdefs_def]
      \\ irule local_c_rel1_nsAppend
      \\ fs [env_domain_eq_def, ADD1]
      \\ drule_then irule local_c_rel1_SUBSET
      \\ simp []
    )
  )

  >- ( (* type abbreviation *)
    asm_exists_tac >>
    fs [v_rel_eqns, empty_env_def, env_domain_eq_def, subglobals_refl]
  )

  >- ( (* Denv *)
    cheat
  )

  >- ( (* exceptions *)
    reverse (rw [evaluate_def]) >>
    fs [v_rel_eqns, invariant_def, s_rel_cases, is_fresh_exn_def]
    >- (
      rfs [] >>
      rveq >> fs [] >>
      fs [idx_range_rel_def, ALL_DISJOINT_DEF] >>
      first_x_assum (qspecl_then [`0`, `3`] mp_tac) >>
      simp [EXTENSION] >>
      qexists_tac `(idx.eidx, Idx_Exn)` >>
      fs [idx_block_def, idx_prev_def] >>
      asm_exists_tac >>
      simp []
    ) >>
    qexists_tac `genv with c := FUNION genv.c
        (FEMPTY |+ (((idx.eidx,NONE),LENGTH ts), ExnStamp s.next_exn_stamp))` >>
    rfs [SUBMAP_FUNION_ID, subglobals_refl, env_domain_eq_def, UNION_COMM] >>
    rw []
    >- (
      drule_then irule genv_c_ok_extend >>
      simp [FLOOKUP_UPDATE] >>
      simp [semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
      simp [ctor_same_type_def] >>
      CCONTR_TAC >> fs [idx_range_rel_def] >>
      rfs [FRANGE_FLOOKUP]
    )
    >- (
      irule LIST_REL_mono >>
      goal_assum (first_assum o mp_then (Pat `LIST_REL`) mp_tac) >>
      rw [] >>
      irule sv_rel_weak >>
      goal_assum (first_assum o mp_then (Pat `sv_rel`) mp_tac) >>
      simp [subglobals_refl, SUBMAP_FUNION_ID]
    )
    >- (
      fs [idx_range_rel_def, FRANGE_FUNION] >>
      rw [] >>
      fs [FRANGE_FLOOKUP, FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE] >>
      drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE) >>
      simp [LUPDATE_compute] >>
      qexists_tac `{(idx.eidx, Idx_Exn)}` >>
      simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def] >>
      fs [idx_prev_def] >>
      metis_tac []
    )
    >- (
      simp [FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
      \\ CCONTR_TAC
      \\ fs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
      \\ rfs [FDOM_FLOOKUP]
      \\ res_tac \\ fs []
    )
  )

  >- ( (* Module *)
    pairarg_tac >>
    fs [] >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rw [] >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    `r1 ≠ Rerr (Rabort Rtype_error)` by (every_case_tac >> fs []) >>
    fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    rw [] >>
    qexists_tac `genv'` >>
    simp [case_eq_thms, PULL_EXISTS] >>
    rpt (gen_tac ORELSE disch_tac) >>
    rw []
    >- (
      fs [env_domain_eq_def, lift_env_def] >>
      rw [nsDom_nsLift, nsDomMod_nsLift])
    >- (
      rw [] >>
      fs [v_rel_eqns] >>
      rw [lift_env_def, nsLookup_nsLift] >>
      CASE_TAC >>
      rw [] >>
      fs [])
    >- (
      fs [lift_env_def]
      \\ simp [local_c_rel1_nsLift]
    ))
  >- ( (* local *)
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs [] >>
    rveq >>
    imp_res_tac compile_decs_num_bindings >>
    split_pair_case_tac >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    impl_tac >- (simp [] >> CCONTR_TAC >> fs []) >>
    rw [] >>
    reverse (fs [case_eq_thms])
    >- ( (* err case *)
      fs [] >>
      rveq >>
      fs [] >>
      rveq >>
      drule evaluate_decs_append_err >>
      rw [] >>
      asm_exists_tac >>
      fs [] >>
      fs [invariant_def]
    ) >>
    (* result case *)
    rveq >>
    fs [] >>
    first_x_assum (drule_then drule) >>
    impl_tac
    >- (
      rw []
      >- (
        fs [local_c_rel_def]
        \\ metis_tac [local_c_rel1_extend, local_c_rel1_SUBSET, SUBSET_TRANS]
      )
      >- metis_tac [global_env_inv_append, global_env_inv_weak]
      \\ fs [subglobals_def]
    ) >>
    rw [] >>
    imp_res_tac evaluate_decs_append >>
    fs [] >>
    qexists_tac `genv''` >> fs [] >>
    metis_tac [SUBMAP_TRANS, subglobals_trans, SUBSET_TRANS]
  )
  >- ( (* Denv, bind a new env *)
    simp [evaluate_def]
    (* false, because compile_decs doesn't do anything here, and
       the invariant requires *something* to get bound on the flat side *)
    \\ cheat
  )
  >- ( (* empty list *)
    simp [evaluate_def, env_domain_eq_def, empty_env_def, v_rel_eqns]
    \\ metis_tac [SUBMAP_REFL, subglobals_refl]
  )
  >- ( (* cons list *)
    rpt gen_tac >>
    simp [compile_decs_def] >>
    qspec_tac (`d2::ds`, `ds`) >>
    rw [] >>
    ntac 2 (pairarg_tac \\ fs[])
    \\ rveq
    \\ qpat_x_assum`_ = (_,r)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw [] >>
      fs [] >>
      first_x_assum drule >>
      simp [] >>
      disch_then drule >>
      impl_tac
      >- (
        imp_res_tac compile_decs_num_bindings >>
        rw []) >>
      rw [] >>
      simp [PULL_EXISTS] >>
      drule_then (fn t => CHANGED_TAC (simp [t])) evaluate_decs_append_err >>
      goal_assum (first_assum o mp_then (Pat `result_rel`) mp_tac) >>
      fs [invariant_def] >>
      drule compile_decs_num_bindings >>
      fs [] >>
      rw [] >>
      fs [subglobals_def, GREATER_EQ] >>
      rfs []
    ) >>
    BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[] >>
    first_x_assum drule >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      rw []) >>
    rw [] >>
    `r' ≠ Rerr (Rabort Rtype_error)`
    by (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs []) >>
    fs [] >>
    first_x_assum drule >>
    `global_env_inv genv' (extend_env new_env1 comp_map) {} (extend_dec_env a env)`
    by metis_tac [global_env_inv_append, global_env_inv_weak] >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      fs [subglobals_def, local_c_rel_def] >>
      metis_tac [local_c_rel1_extend, local_c_rel1_SUBSET, SUBSET_TRANS]) >>
    rw [] >>
    drule_then drule evaluate_decs_append >>
    rw [] >>
    qexists_tac `genv''` >>
    rw [UNION_ASSOC]
    >- metis_tac [SUBMAP_TRANS]
    >- metis_tac [subglobals_trans]
    >- metis_tac [SUBSET_TRANS]
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      rw [] >>
      fs [] >>
      imp_res_tac env_domain_eq_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      imp_res_tac global_env_inv_weak >>
      drule global_env_inv_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def, case_eq_thms] >>
      rveq >> fs [] >>
      simp [extend_env_def] >>
      irule local_c_rel1_nsAppend >>
      fs [env_domain_eq_def] >>
      drule_then irule local_c_rel1_SUBSET >>
      simp []
    )
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      MAP_EVERY qexists_tac [`small_idx`] >>
      fs []))
);



fun spectv v tt = disch_then(qspec_then tt mp_tac o CONV_RULE (RESORT_FORALL_CONV(sort_vars[v])))
val spect = spectv "t"

val lookup_inc_lookup = Q.prove (
  `lookup_inc t new_cids = (tag,new_cids')
   ⇒
   lookup t new_cids' = SOME (tag+1)`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw []);

val lookup_inc_lookup_unchanged = Q.prove (
  `!t1. lookup_inc t new_cids = (tag,new_cids') ∧
   t1 ≠ t
   ⇒
   lookup t1 new_cids = lookup t1 new_cids'`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw [lookup_insert]);

val lookup_inc_lookup_new = Q.prove (
  `lookup_inc t new_cids = (tag,new_cids')
   ⇒
   lookup t new_cids = NONE ∧ tag = 0 ∨ lookup t new_cids = SOME tag`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw []);

val alloc_tags_submap = Q.prove (
  `!idx new_cids ctors ns cids.
    alloc_tags idx new_cids ctors = (ns, cids)
    ⇒
    !arity max_tag. lookup arity new_cids = SOME max_tag ⇒
      ?max_tag'. lookup arity cids = SOME max_tag' ∧ max_tag ≤ max_tag'`,
  Induct_on `ctors` >>
  rw [alloc_tags_def] >>
  PairCases_on `h` >>
  fs [alloc_tags_def] >>
  rpt (pairarg_tac >> fs []) >>
  fs [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  res_tac >>
  rw [] >>
  fs [lookup_insert]
  >- (
    first_x_assum irule >>
    rw [] >>
    fs []) >>
  Cases_on `LENGTH h1 = arity` >>
  fs [] >>
  pop_assum kall_tac >>
  rw [] >>
  pop_assum (qspecl_then [`max_tag + 1`, `arity`] mp_tac) >>
  rw [] >>
  rw []);

val evaluate_alloc_tags = Q.prove (
  `!idx (ctors :(tvarN, ast_t list) alist) ns cids genv s s' new_cids env_c.
   invariant genv idx s s' env_c ∧
   alloc_tags idx.tidx new_cids ctors = (ns, cids) ∧
   (!tag arity. ((tag,SOME idx.tidx),arity) ∈ FDOM genv.c ⇒
     (?max_tag. lookup arity new_cids = SOME max_tag ∧ tag < max_tag)) ∧
   ALL_DISTINCT (MAP FST ctors)
   ⇒
   ?genv_c.
     {((t,SOME idx.tidx),arity) | ?t'. lookup arity cids = SOME t' ∧ t < t' }
     DIFF
     {((t,SOME idx.tidx),arity) | ?t'. lookup arity new_cids = SOME t' ∧ t < t' } = FDOM genv_c ∧
     (!tag typ arity stamp.
       FLOOKUP genv_c ((tag,typ),arity) = SOME stamp ⇒
       typ = SOME idx.tidx ∧
       (lookup arity new_cids ≠ NONE ⇒
         ?max_tag. lookup arity new_cids = SOME max_tag ∧ tag ≥ max_tag) ∧
       ?cn. cn ∈ set (MAP FST ctors) ∧
         stamp = TypeStamp cn s.next_type_stamp) ∧
     nsDom ns = IMAGE Short (set (MAP FST ctors)) ∧
     nsDomMod ns = { [] } ∧
     invariant
       (genv with c := FUNION genv_c genv.c)
       (idx with tidx updated_by SUC)
       (s with next_type_stamp updated_by SUC)
       (s' with c := FDOM genv_c ∪ FDOM genv.c)
       (FDOM genv_c ∪ env_c) ∧
      global_env_inv (genv with c := FUNION genv_c genv.c)
        <| c := ns; v := nsEmpty |>
        {}
        <| v := nsEmpty; c := alist_to_ns (REVERSE (build_constrs s.next_type_stamp ctors)) |>`,

  Induct_on `ctors` >>
  rw [alloc_tags_def, build_constrs_def, extend_env_def, extend_dec_env_def] >>
  rw []
  >- (
    qexists_tac `FEMPTY` >>
    fs [invariant_def, v_rel_eqns, s_rel_cases] >>
    `genv with c := genv.c = genv` by rw [theorem "global_env_component_equality"] >>
    metis_tac []) >>

  rename [`alloc_tags _ _ (c::_) = _`] >>
  `?cn ts. c = (cn,ts)` by metis_tac [pair_CASES] >>
  fs [alloc_tags_def] >>
  rpt (pairarg_tac >> fs []) >>
  rw [] >>
  first_x_assum drule >>
  disch_then drule >>

  impl_keep_tac
  >- (
    rw [] >>
    res_tac >>
    fs [lookup_inc_def] >>
    every_case_tac >>
    fs [] >>
    rw [lookup_insert] >>
    fs []) >>
  simp [invariant_def, v_rel_eqns, s_rel_cases, extend_env_def, extend_dec_env_def] >>
  rw [] >>
  qexists_tac `genv_c |+ (((tag, SOME idx.tidx), LENGTH ts),
                          TypeStamp cn s.next_type_stamp)` >>
  `((tag, SOME idx.tidx), LENGTH ts) ∉ FDOM (FUNION genv_c genv.c)`
  by (
    CCONTR_TAC >>
    fs [FLOOKUP_DEF] >>
    res_tac >>
    fs [lookup_inc_def] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    fs [lookup_insert]) >>
  rw []
  >- (
    qpat_x_assum `_ DIFF _ = FDOM _` (assume_tac o GSYM) >>
    rw [] >>
    qmatch_goalsub_abbrev_tac `S1 DIFF S2 = x INSERT _ DIFF S3` >>
    `x ∈ S1`
    by (
      simp [Abbr`x`, Abbr`S1`] >>
      drule alloc_tags_submap >>
      disch_then (qspecl_then [`LENGTH ts`, `tag + 1`] mp_tac) >>
      simp [DECIDE ``!x:num y. x +1 ≤ y ⇔ x < y``] >>
      disch_then irule >>
      metis_tac [lookup_inc_lookup]) >>
    `x ∉ S2`
    by (
      simp [Abbr`x`, Abbr`S2`] >>
      drule lookup_inc_lookup_new >>
      rw [] >>
      rw []) >>
    `S3 = x INSERT S2`
    by (
      simp [Abbr`x`, Abbr`S2`, Abbr`S3`] >>
      rw [EXTENSION] >>
      eq_tac >>
      rw []
      >- (
        rw [PROVE [] ``!x y. x ∨ y ⇔ ~x ⇒ y``] >>
        drule lookup_inc_lookup_new >>
        drule lookup_inc_lookup >>
        drule lookup_inc_lookup_unchanged >>
        rw [] >>
        fs [] >>
        Cases_on `arity = LENGTH ts` >>
        fs [])
      >- (
        drule lookup_inc_lookup >>
        rw [])
      >- (
        Cases_on `arity = LENGTH ts` >>
        fs [] >>
        drule lookup_inc_lookup_unchanged >>
        rw [] >>
        metis_tac [])) >>
    rw [EXTENSION] >>
    eq_tac >>
    rw [] >>
    CCONTR_TAC >>
    fs [SUBSET_DEF])
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs []
    >- (
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert])
    >- (
      res_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert]
      >- metis_tac [] >>
      every_case_tac >>
      fs [])
    >- metis_tac []
    >- (
      res_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert]
      >- metis_tac [] >>
      every_case_tac >>
      fs []))
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    simp [FUNION_FUPDATE_1] >>
    simp [genv_c_ok_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- (
      fs [has_bools_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      fs [has_exns_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      fs [has_lists_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      rw []
      >- fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def]
      >- (
        pop_assum mp_tac >>
        simp [FLOOKUP_FUNION] >>
        every_case_tac >>
        rw [] >>
        PairCases_on `cn2`
        >- (
          Cases_on `stamp2` >>
          fs [invariant_def] >>
          fs [FLOOKUP_DEF] >>
          `cn21 ≠ SOME idx.tidx` by metis_tac [PAIR_EQ, DECIDE ``x ≥ x : num``] >>
          rw [] >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          fs [FRANGE_DEF] >>
          metis_tac [DECIDE ``!x:num. x ≥ x``])
        >- (
          Cases_on `stamp2` >>
          res_tac >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          res_tac >>
          fs [invariant_def, FLOOKUP_DEF, genv_c_ok_def]))
      >- (
        pop_assum mp_tac >>
        simp [FLOOKUP_FUNION] >>
        every_case_tac >>
        rw [] >>
        PairCases_on `cn1`
        >- (
          Cases_on `stamp1` >>
          fs [invariant_def] >>
          fs [FLOOKUP_DEF] >>
          `cn11 ≠ SOME idx.tidx` by metis_tac [PAIR_EQ, DECIDE ``x ≥ x : num``] >>
          rw [] >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          fs [FRANGE_DEF] >>
          metis_tac [DECIDE ``!x:num. x ≥ x``])
        >- (
          Cases_on `stamp1` >>
          res_tac >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          res_tac >>
          fs [invariant_def, FLOOKUP_DEF, genv_c_ok_def]))
      >- metis_tac [genv_c_ok_def])
    >- (
      rpt gen_tac >>
      strip_tac >>
      every_case_tac
      >- (
        fs [FLOOKUP_FUNION] >>
        every_case_tac >>
        fs [invariant_def, FLOOKUP_DEF, FRANGE_DEF] >>
        rw [] >>
        metis_tac [DECIDE ``x ≥ x : num``, stamp_11, pair_CASES])
      >- (
        fs [FLOOKUP_FUNION] >>
        every_case_tac >>
        fs [invariant_def, FLOOKUP_DEF, FRANGE_DEF] >>
        rw [] >>
        metis_tac [DECIDE ``x ≥ x : num``, stamp_11, pair_CASES])
      >- metis_tac [genv_c_ok_def]))
  >- (
    simp [FRANGE_FUPDATE, FUNION_FUPDATE_1] >>
    fs [] >>
    res_tac >>
    fs [IN_FRANGE, FDOM_DRESTRICT] >>
    rw [DRESTRICT_DEF] >>
    metis_tac [])
  >- (
    simp [Once FUPDATE_EQ_FUNION] >>
    fs [s_rel_cases] >>
    res_tac >>
    simp [GSYM FUNION_ASSOC] >>
    qabbrev_tac `g = genv_c ⊌ genv.c` >>
    fs [IN_FRANGE] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    rfs [FAPPLY_FUPDATE, FUNION_DEF] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    simp [Once FUPDATE_EQ_FUNION] >>
    simp [GSYM FUNION_ASSOC] >>
    rfs [] >>
    res_tac >>
    irule sv_rel_weak >>
    simp [] >>
    qexists_tac `<|v := s'.globals; c := genv_c ⊌ genv.c|>` >>
    rw [SUBMAP_DEF, FAPPLY_FUPDATE, FUNION_DEF, subglobals_refl] >>
    rw [] >>
    metis_tac [])
  >- (
    pop_assum mp_tac >>
    rw [nsLookup_alist_to_ns_some]
    >- (
       fs [ALOOKUP_APPEND, nsLookup_nsAppend_some, nsLookup_alist_to_ns_some] >>
       every_case_tac >>
       fs [] >>
       rw [] >>
       fs [FLOOKUP_UPDATE, FUNION_FUPDATE_1]
       >- (
         drule ALOOKUP_MEM >>
         simp [MEM_MAP, EXISTS_PROD] >>
         rw [] >>
         fs [MEM_MAP] >>
         metis_tac [FST]) >>
       rw [nsLookup_nsAppend_some] >>
       first_x_assum (qspecl_then [`Short x'`, `arity`, `stamp`] mp_tac) >>
       rw [build_constrs_def] >>
       rw [] >>
       fs [FLOOKUP_DEF] >>
       fs [])));

val nsAppend_foldl' = Q.prove (
  `!l ns ns'.
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) ns' l) ns
   =
   FOLDL (λns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  Induct_on `l` >>
  rw [] >>
  PairCases_on `h` >>
  rw []);

val nsAppend_foldl = Q.prove (
  `!l ns.
   FOLDL (λns (l,cids). nsAppend l ns) ns l
   =
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) nsEmpty l) ns`,
  metis_tac [nsAppend_foldl', nsAppend_nsEmpty]);

val build_tdefs_no_mod = Q.prove (
  `!idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}`,
  Induct_on `tdefs` >>
  rw [build_tdefs_def] >>
  PairCases_on `h` >>
  rw [build_tdefs_def] >>
  pop_assum (qspec_then `idx+1` mp_tac) >>
  rw [nsDomMod_nsAppend_flat]);

val LUPDATE_EACH_def = Define `
  LUPDATE_EACH i xs [] = xs /\
  LUPDATE_EACH i xs (y::ys) = LUPDATE (SOME y) i (LUPDATE_EACH (i+1) xs ys)`;

Theorem compile_exps_MAP_Var[simp]:
  compile_exps t env (MAP Var vs) =
  MAP (λv. case nsLookup env.v v of NONE => Var_local t "" | SOME x => compile_var t x) vs
Proof Induct_on`vs` \\ rw[compile_exp_def]
QED

val LENGTH_LUPDATE_EACH = prove(
  ``!zs i xs. LENGTH (LUPDATE_EACH i xs zs) = LENGTH xs``,
  Induct \\ fs [LUPDATE_EACH_def]);

val EL_LUPDATE_EACH = prove(
  ``!zs n i xs. n < i ==> EL n (LUPDATE_EACH i xs zs) = EL n xs``,
  Induct \\ fs [LUPDATE_EACH_def,EL_LUPDATE]);

val EL_LUPDATE_EACH_PAST = prove(
  ``!zs n i xs. i + LENGTH zs <= n ==> EL n (LUPDATE_EACH i xs zs) = EL n xs``,
  Induct \\ fs [LUPDATE_EACH_def,EL_LUPDATE]);

val EL_LUPDATE_EACH_HIT = prove(
  ``!l i n xs. i < LENGTH l /\ LENGTH l + n <= LENGTH xs ==>
               EL (i + n) (LUPDATE_EACH n xs l) = SOME (EL i l)``,
  Induct_on `l` \\ fs [LUPDATE_EACH_def] \\ Cases_on `i` \\ fs []
  \\ fs [EL_LUPDATE,LENGTH_LUPDATE_EACH] \\ rw []
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`n'+1`,`xs`] mp_tac) \\ fs [ADD1]);

val nsLookup_FOLDR_SOME_IMP = prove(
  ``nsLookup
      (FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env funs f) env')
        nsEmpty funs) x = SOME (v:semanticPrimitives$v) ==>
    ?i f y e. i < LENGTH funs /\ v = Recclosure env funs f /\ EL i funs = (f,y,e) /\
              x = Short f``,
  qspec_tac (`Recclosure env funs`,`rr`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ Cases_on `x` \\ fs [nsLookup_nsBind]
  \\ rw [] \\ Cases_on `p_1 = n` \\ fs []
  \\ fs [nsLookup_nsBind]
  THEN1 (qexists_tac `0` \\ fs [])
  \\ res_tac \\ fs []
  \\ fs [] \\ qexists_tac `SUC i` \\ fs []);

Theorem evaluate_Letrec_Var:
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ==>
  evaluate s env [Letrec funs (Con NONE (MAP (λ(f,_). Var (Short f)) funs))] =
    (s, Rval [Conv NONE (MAP (\(f,x,e). Recclosure env funs f) funs)])
Proof
  fs [terminationTheory.evaluate_def,do_con_check_def,build_conv_def,
      pair_case_eq,result_case_eq,PULL_EXISTS,listTheory.SWAP_REVERSE_SYM]
  \\ fs [semanticPrimitivesTheory.build_rec_env_def]
  \\ qspec_tac (`Recclosure env funs`,`h`)
  \\ qid_spec_tac `env`  \\ qid_spec_tac `funs`
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ fs [MAP_SNOC,REVERSE_SNOC,FOLDR_SNOC,FORALL_PROD,ALL_DISTINCT_SNOC]
  \\ once_rewrite_tac [evaluatePropsTheory.evaluate_cons]
  \\ fs [terminationTheory.evaluate_def] \\ rw []
  \\ qpat_abbrev_tac `pat = nsLookup _ _`
  \\ qsuff_tac `pat = SOME (h p_1)`
  THEN1
   (first_x_assum (qspecl_then [`env with v := nsBind p_1 (h p_1) env.v`,`h`] mp_tac)
    \\ fs [])
  \\ unabbrev_all_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on `funs` \\ fs []
  \\ rw [FORALL_PROD]
  \\ rename [`_ <> _ h6`] \\ PairCases_on `h6` \\ fs []
QED

Theorem UNCURRY_EQ_comp_FST:
  (\(x, y). f x) = (f o FST)
Proof
  fs [FUN_EQ_THM, FORALL_PROD]
QED

Theorem pmatch_list_vars_eq_Match:
  !vnames vals bindings. pmatch_list env st (MAP Pvar vnames) vals bindings
    = if LENGTH vnames = LENGTH vals
        then Match (REVERSE (ZIP (vnames, vals)) ++ bindings)
        else Match_type_error
Proof
  Induct
  >- (
    Cases
    \\ simp [pmatch_def]
  )
  \\ gen_tac
  \\ Cases
  \\ simp [pmatch_def]
  \\ CASE_TAC
  \\ simp []
QED

Theorem LUPDATE_EACH_LUPDATE:
  !xs ys i j.
    j < i /\ i + LENGTH ys <= LENGTH xs ==>
    LUPDATE_EACH i (LUPDATE x j xs) ys = LUPDATE x j (LUPDATE_EACH i xs ys)
Proof
  Induct_on `ys` \\ fs [LUPDATE_EACH_def] \\ rw []
  \\ `i <> j` by fs []
  \\ metis_tac [miscTheory.LUPDATE_commutes]
QED

Theorem evaluate_let_none_list_MAPi:
  !exps env st n. ALL_DISTINCT (MAP FST env.v) /\
    IMAGE g (set exps) ⊆ IMAGE FST (set env.v) /\
    (!i. i < LENGTH exps ==> i + n < LENGTH st.globals /\ EL (i + n) st.globals = NONE)
  ==>
  evaluate env st [let_none_list (MAPi (\i x.
    App None (GlobalVarInit (i + n)) [Var_local None (g x)]) exps)]
  = (st with globals := LUPDATE_EACH n st.globals
        (MAP (\exp. THE (ALOOKUP env.v (g exp))) exps),
      Rval [flatSem$Conv NONE []])
Proof
  Induct
  \\ simp [let_none_list_def, evaluate_def, LUPDATE_EACH_def]
  >- simp [flatSemTheory.state_component_equality]
  \\ Cases_on `exps`
  \\ simp [let_none_list_def, evaluate_def]
  \\ simp [EXISTS_PROD]
  \\ rw []
  \\ rfs [miscTheory.MEM_ALOOKUP]
  \\ rveq \\ fs []
  \\ simp [do_app_def, LUPDATE_EACH_def, Unitv_def]
  \\ first_assum (qspecl_then [`0`] mp_tac)
  \\ simp_tac (srw_ss ()) []
  \\ rw []
  \\ fs [o_DEF]
  \\ first_assum (qspecl_then [`env_x`, `st_x`, `SUC n`] (assume_tac o GEN_ALL))
  \\ fs [ADD1]
  \\ first_x_assum (fn t => CHANGED_TAC (DEP_REWRITE_TAC [t]))
  \\ simp [libTheory.opt_bind_def, EXISTS_PROD, listTheory.EL_LUPDATE,
        miscTheory.MEM_ALOOKUP]
  \\ simp [LUPDATE_EACH_LUPDATE, LUPDATE_EACH_def]
  \\ simp [flatSemTheory.state_component_equality, miscTheory.LUPDATE_commutes]
  \\ DEP_REWRITE_TAC [LUPDATE_EACH_LUPDATE]
  \\ simp [flatSemTheory.state_component_equality, miscTheory.LUPDATE_commutes]
  \\ rw []
  \\ TRY (first_x_assum (qspecl_then [`SUC i`] mp_tac)
    \\ simp [ADD1] \\ NO_TAC)
  \\ first_x_assum (qspec_then `LENGTH t + 1` mp_tac) \\ fs []
QED

Theorem extend_env_nsEmpty_c:
  (new_comp_map.c = nsEmpty ==>
    (extend_env new_comp_map comp_map).c = comp_map.c) /\
  (new_env.c = nsEmpty ==>
    (extend_dec_env new_env env).c = env.c)
Proof
  simp [extend_env_def, extend_dec_env_def]
QED

Theorem global_env_inv_map_mono:
  !comp_map comp_map'. global_env_inv genv comp_map shadowers env /\
  comp_map'.v = comp_map.v /\
  (!x cn. nsLookup comp_map.c x = SOME cn ==> nsLookup comp_map'.c x = SOME cn)
  ==>
  global_env_inv genv comp_map' shadowers env
Proof
  simp [v_rel_cases |> CONJUNCTS |> last]
  \\ metis_tac []
QED

Theorem nsLookup_nsBind_If:
  nsLookup (nsBind n v e) nm = (if nm = Short n then SOME v else nsLookup e nm)
Proof
  Cases_on `e`
  \\ Cases_on `nm`
  \\ simp [namespaceTheory.nsBind_def, namespaceTheory.nsLookup_def]
  \\ simp [EQ_SYM_EQ]
QED

Theorem lookup_inc_lookup_NONE:
  lookup_inc n cids = (tag, cids1) /\
  lookup y cids1 = NONE ==> lookup y cids = NONE
Proof
  simp [lookup_inc_def]
  \\ every_case_tac
  \\ rw []
  \\ fs [lookup_insert, bool_case_eq]
QED

Theorem alloc_tags_local_c_rel1:
  !tidx cids ctors ns cids1 new_c.
  alloc_tags tidx cids ctors = (ns,cids1) /\
  ALL_DISTINCT (MAP FST ctors) /\
  {((t,SOME tidx),arity) |
    ∃t'. lookup arity cids1 = SOME t' /\ t < t'} = new_c
  ==>
  local_c_rel1 ns
    (alist_to_ns (REVERSE (build_constrs s.next_type_stamp ctors)))
    (new_c ∪ flat_c)
Proof
  ho_match_mp_tac alloc_tags_ind
  \\ csimp [alloc_tags_def, local_c_rel1_def, build_constrs_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ full_simp_tac bool_ss [GSYM nsAppend_alist_to_ns, nsLookup_nsAppend_some]
  >- (
    fs []
    \\ qsuff_tac `Short cn <> x`
    >- (
      simp [nsLookup_nsBind_If]
      \\ metis_tac [lookup_inc_lookup_NONE]
    )
    \\ fs [nsLookup_alist_to_ns_some]
    \\ drule ALOOKUP_MEM
    \\ fs [MEM_MAP, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac []
  )
  \\ fs [nsLookup_nsBind_If]
  \\ drule alloc_tags_submap
  \\ disch_then (qspec_then `arity` mp_tac)
  \\ fs [lookup_inc_def]
  \\ every_case_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rw [] \\ simp []
QED

Theorem nsDomMod_single_nsLookupMod:
  nsDomMod ns = {x} /\ nsLookupMod ns y = SOME z ==>
  y = x
Proof
  rw [namespaceTheory.nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD]
  \\ metis_tac []
QED

Theorem local_c_rel1_nsAppend:
  local_c_rel1 a b flat_c /\ local_c_rel1 c d flat_c /\
  nsDom a = nsDom b /\ nsDomMod a = nsDomMod b ==>
  local_c_rel1 (nsAppend a c) (nsAppend b d) flat_c
Proof
  rw [local_c_rel1_def, nsLookup_nsAppend_some]
  \\ first_assum (drule_then assume_tac)
  \\ fs []
  \\ Cases_on `nsLookup a x`
  >- (
    fs []
    \\ rw []
    \\ first_x_assum (drule_then drule)
    \\ fs [namespaceTheory.nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD]
    \\ metis_tac [NOT_SOME_NONE, option_nchotomy]
  )
  >- (
    fs [namespaceTheory.nsDom_def, EXTENSION, GSPECIFICATION, EXISTS_PROD]
    \\ metis_tac [NOT_SOME_NONE, option_nchotomy]
  )
QED

Theorem local_c_rel1_extend:
  local_c_rel1 comp_map.c env.c flat_c /\
  local_c_rel1 comp_map1.c env1.c flat_c /\
  env_domain_eq comp_map1 env1 ==>
  local_c_rel1 (extend_env comp_map1 comp_map).c (extend_dec_env env1 env).c
    flat_c
Proof
  rw [extend_env_def, extend_dec_env_def]
  \\ drule_then irule local_c_rel1_nsAppend
  \\ fs [env_domain_eq_def]
QED

Theorem local_c_rel1_SUBSET:
  local_c_rel1 comp_map_c env_c flat_c /\
  flat_c ⊆ flat_c1 ==>
  local_c_rel1 comp_map_c env_c flat_c1
Proof
  simp [local_c_rel1_def, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem local_c_rel1_nsEmpty[simp]:
  local_c_rel1 comp_map_c nsEmpty flat_c
Proof
  simp [local_c_rel1_def]
QED

Theorem local_c_rel1_nsLift:
  local_c_rel1 comp_map_c env_c flat_c ==>
  local_c_rel1 (nsLift mn comp_map_c) (nsLift mn env_c) flat_c
Proof
  rw [local_c_rel1_def, nsLookup_nsLift, CaseEq "id"]
QED

val compile_decs_correct' = Q.prove (
  `! t idx comp_map ds ^s env s' r s_i1 idx' comp_map' flat_c ds_i1 t' genv.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    invariant genv idx s s_i1 flat_c ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    local_c_rel comp_map.c env.c flat_c ∧
    source_to_flat$compile_decs t idx comp_map ds = (t', idx', comp_map', ds_i1) ∧
    global_env_inv genv comp_map {} env ∧
    idx'.vidx ≤ LENGTH genv.v
    ⇒
    ? ^s1_i1 flat_c1 genv' r_i1.
      flatSem$evaluate_decs s_i1 flat_c ds_i1 = (s1_i1,flat_c1,r_i1) ∧
      genv.c SUBMAP genv'.c ∧
      subglobals genv.v genv'.v ∧
      flat_c ⊆ flat_c1 ∧
      (*FDOM genv'.c = cenv' ∪ FDOM genv.c ∧*)
      invariant genv' idx' s' s1_i1 flat_c1 ∧
      (!env'.
        r = Rval env'
        ⇒
        r_i1 = NONE ∧
        env_domain_eq comp_map' env' ∧
        global_env_inv genv' comp_map' {} env' ∧
        local_c_rel1 comp_map'.c env'.c flat_c1) ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = SOME err_i1 ∧
          result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))`,
  ho_match_mp_tac compile_decs_ind >>
  simp [terminationTheory.evaluate_decs_def] >>
  rw [compile_decs_def]
  >- ( (* Let *)
    split_pair_case_tac >>
    fs [] >>
    qmatch_assum_rename_tac `evaluate _ _ _ = (st', res)` >>
    drule compile_exp_correct >>
    `res ≠ Rerr (Rabort Rtype_error)`
    by (Cases_on `res` >> rfs [] >> rw []) >>
    rveq >>
    fs [invariant_def] >>
    rpt (disch_then drule) >>
    spect`(om_tra ▷ t)`>>
    `<|v := s_i1.globals; c := genv.c|> = genv` by rw [theorem "global_env_component_equality"] >>
    simp [] >>
    imp_res_tac evaluatePropsTheory.evaluate_next_type_stamp_mono >>
    imp_res_tac evaluatePropsTheory.evaluate_next_exn_stamp_mono >>
    reverse (rw [flatSemTheory.evaluate_def,
        compile_exp_def, result_rel_cases, pmatch_rows_def]) >>
    fs [] >> rveq >> fs []
    >- ( (* Expression abort *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_nsEmpty_c])
    >- ( (* Expression exception *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_def, extend_dec_env_def] >>
      fs [v_rel_eqns] >>
      metis_tac [s_rel_cases]) >>
    (* Expression evaluates *)
    qmatch_assum_rename_tac `evaluate _ _ [e] = (st', Rval answer')` >>
    `?answer. answer' = [answer]`
    by (
      imp_res_tac evaluate_sing >>
      fs []) >>
    fs [] >>
    rveq >>
    qmatch_asmsub_abbrev_tac `evaluate mk_env _ [compile_exp _ comp_map e] = (st1', Rval [answer1])` >>
    `match_result_rel genv [] (pmatch env.c st'.refs p answer ([]++[]))
           (pmatch mk_env st1' (compile_pat comp_map p) answer1 [])`
    by (
      match_mp_tac (GEN_ALL pmatch_lem) >>
      simp [] >>
      fs [s_rel_cases, markerTheory.Abbrev_def] >>
      fs [v_rel_eqns] >>
      rfs []) >>
    fs [pmatch_ignore_env_v, Abbr `mk_env`] >>
    fs [pmatch_rows_def,CaseEq"match_result"] >>
    Cases_on `pmatch env.c st'.refs p answer [] ` >>
    fs []
    >- ( (* No match *)
      rw [PULL_EXISTS] >>
      every_case_tac >>
      fs [match_result_rel_def] >>
      qexists_tac `genv` >>
      rw [subglobals_refl] >>
      rw [v_rel_lems, extend_env_def, extend_dec_env_def] >>
      fs [v_rel_eqns] >>
      fs [s_rel_cases]) >>
    (* Match *)
    qmatch_asmsub_abbrev_tac `match_result_rel _ _ (Match _) r` >>
    Cases_on `r` >>
    fs [match_result_rel_def] >>
    rename [`evaluate <| v := env; c := _ |> s [make_varls _ _ _ _]`] >>
    `?g1 g2.
      LENGTH g1 = idx.vidx ∧
      s.globals = g1++REPLICATE (LENGTH (REVERSE (pat_bindings p []))) NONE++g2`
    by (
      qexists_tac `TAKE idx.vidx s.globals` >>
      qexists_tac `DROP (idx.vidx + LENGTH (pat_bindings p [])) s.globals` >>
      simp [] >>
      `idx.vidx ≤ LENGTH genv.v` by decide_tac >>
      rw [] >>
      rfs [] >>
      irule LIST_EQ >>
      rw [EL_APPEND_EQN, EL_TAKE, EL_REPLICATE, EL_DROP]) >>
    drule_then drule evaluate_make_varls >>
    disch_then (qspecl_then [`0`, `om_tra ▷ t + 3`,
       `<|v := env; c := flat_c |>`, `MAP SND (REVERSE env)`] mp_tac) >>
    fs [markerTheory.Abbrev_def] >>
    qpat_x_assum `Match _ = pmatch _ _ _ _ _` (assume_tac o GSYM) >>
    drule (CONJUNCT1 pmatch_bindings) >>
    simp [] >>
    strip_tac >>
    impl_tac
    >- metis_tac [EL_MAP, alookup_distinct_reverse, ALOOKUP_ALL_DISTINCT_EL,
                  LENGTH_MAP, LENGTH_REVERSE, MAP_REVERSE,
                  ALL_DISTINCT_REVERSE, s_rel_cases] >>
    simp[Unitv_def] >>
    strip_tac >>
    qmatch_goalsub_abbrev_tac`_.v = g1 ++ ggg ++ g2` >>
    qexists_tac`genv with v := g1 ++ ggg ++ g2` \\ simp[] >>
    conj_asm1_tac
    >- (
      rw [Abbr`ggg`] >>
      simp_tac std_ss [subglobals_refl_append, GSYM APPEND_ASSOC] >>
      `LENGTH (REPLICATE (LENGTH (pat_bindings p [])) (NONE:flatSem$v option)) =
       LENGTH (MAP SOME (MAP SND (REVERSE env)))`
      by (
        rw [LENGTH_REPLICATE] >>
        metis_tac [LENGTH_MAP]) >>
      imp_res_tac subglobals_refl_append >>
      rw [] >>
      rw [subglobals_def] >>
      `n < LENGTH (pat_bindings p [])` by metis_tac [LENGTH_MAP] >>
      fs [EL_REPLICATE]) >>
    simp [extend_env_def, extend_dec_env_def] >>
    rw [Abbr`ggg`]
    >- (
      `LENGTH (pat_bindings p []) = LENGTH env` by metis_tac [LENGTH_MAP] >>
      rw [EL_APPEND_EQN] >>
      last_x_assum (qspec_then `n` mp_tac) >>
      simp [EL_APPEND_EQN])
    >- (
      fs [s_rel_cases] >>
      irule LIST_REL_mono >>
      qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
      rw []
      >- (
        irule sv_rel_weak >>
        qexists_tac `genv` >>
        rw []) >>
      metis_tac [])
    >- (
      fs [env_domain_eq_def] >>
      drule (CONJUNCT1 pmatch_bindings) >>
      simp [GSYM MAP_MAP_o, fst_alloc_defs, EXTENSION] >>
      rw [MEM_MAP] >>
      imp_res_tac env_rel_dom >>
      fs [] >>
      metis_tac [FST, MEM_MAP])
    >- (
      fs [] >>
      qspecl_then [`a`, `genv with v := g1 ⧺ MAP SOME (MAP SND (REVERSE env)) ⧺ g2`,
                   `env`, `t+4`, `g1`, `g2`] mp_tac global_env_inv_extend >>
      simp [MAP_REVERSE] >>
      impl_tac
      >- (
        imp_res_tac env_rel_dom >>
        fs [] >>
        irule env_rel_weak >>
        qexists_tac `genv` >>
        rw [] >>
        simp [subglobals_def] >>
        rw [EL_APPEND_EQN] >>
        rfs [EL_REPLICATE] >>
        metis_tac [LENGTH_MAP, LESS_EQ_REFL, ADD_COMM, ADD_ASSOC]) >>
      qmatch_goalsub_abbrev_tac`global_env_inv genv1` >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac`global_env_inv genv2` >>
      `genv1 = genv2` by simp[Abbr`genv1`,Abbr`genv2`,theorem"global_env_component_equality"] >>
      fs[])
  )
  >- ( (* Letrec *)
    Cases_on `funs = []`
    >- ( (* No functions *)
      fs [compile_decs_def] >>
      rw [evaluate_def, compile_exp_def, alloc_defs_def,
          extend_env_def, extend_dec_env_def, let_none_list_def,
          semanticPrimitivesTheory.build_rec_env_def,flatSemTheory.Unitv_def] >>
      TRY (qexists_tac `genv`) >>
      rw [] >>
      fs [invariant_def, v_rel_eqns, s_rel_cases, env_domain_eq_def] >>
      metis_tac [subglobals_refl]) >>
    (* Multiple functions *)
    full_simp_tac std_ss [compile_decs_def] >>
    fs [] >>
    rveq >> fs [] >>
    qpat_abbrev_tac `stores = let_none_list _` >>
    qpat_abbrev_tac `e1 = evaluate_decs s_i1 _ prog` >>
    qabbrev_tac `c1 = compile_exp None comp_map
      (Letrec funs (Con NONE (MAP (λ(f,_). Var (Short f)) funs)))` >>
    `ALL_DISTINCT (pat_bindings (Pcon NONE (MAP (λ(f,_). Pvar f) funs)) [])` by (
      rw[pat_bindings_def, pats_bindings_FLAT_MAP, MAP_MAP_o, o_DEF, UNCURRY, FLAT_MAP_SING]
      \\ fs[FST_triple] ) \\
    `e1 = evaluate_decs s_i1 flat_c
       [Dlet (Mat None c1
          [(Pcon NONE (MAP (\(f,_). Pvar f) funs), stores)])]` by
     (
      fs [Abbr `e1`] \\ fs [compile_exp_def,Abbr `c1`]
      \\ simp [evaluate_def]
      \\ qpat_abbrev_tac `mf = MAP FST`
      \\ `mf = MAP (\(x,y,z). x)`
           by (fs [Abbr `mf`] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM,FORALL_PROD])
      \\ fs [GSYM compile_funs_dom,Abbr `mf`]
      \\ qmatch_goalsub_abbrev_tac `evaluate bc`
      \\ qmatch_goalsub_abbrev_tac`compile_exps None cenv mvf`
      \\ `mvf = MAP Var (MAP (Short o FST) funs)`
      by ( simp[Abbr`mvf`, MAP_EQ_f, MAP_MAP_o, FORALL_PROD] )
      \\ fs[Abbr`mvf`]
      \\ simp[MAP_MAP_o, o_DEF, Abbr`cenv`]
      \\ qmatch_goalsub_abbrev_tac`REVERSE (MAP f funs)`
      \\ `MAP f funs = MAP (Var_local None o FST) funs`
      by (
        simp[compile_var_def,MAP_EQ_f, Abbr`f`, FORALL_PROD]
        \\ rpt strip_tac
        \\ simp[compile_var_def,GSYM nsAppend_to_nsBindList]
        \\ CASE_TAC
        \\ fs[nsLookup_nsAppend_some, nsLookup_nsAppend_none,
              compile_var_def, namespaceTheory.id_to_mods_def]
        \\ fs[nsLookup_alist_to_ns_none, nsLookup_alist_to_ns_some]
        \\ TRY(fs[ALOOKUP_FAILS, MEM_MAP, FORALL_PROD] \\ NO_TAC)
        \\ imp_res_tac ALOOKUP_MEM \\ fs[compile_var_def,MEM_MAP] )
      \\ fs[Abbr`f`,pmatch_rows_def]
      \\ pop_assum kall_tac
      \\ pop_assum kall_tac
      \\ simp[GSYM MAP_REVERSE]
      \\ simp[GSYM MAP_MAP_o]
      \\ qmatch_asmsub_abbrev_tac`build_rec_env funs' emp_env []`
      \\ `MAP (ALOOKUP bc.v) (MAP FST (REVERSE funs)) =
          MAP SOME (MAP (Recclosure emp_env funs' o FST) (REVERSE funs))`
      by (
        simp[MAP_MAP_o, MAP_REVERSE, MAP_EQ_f, FORALL_PROD]
        \\ simp[Abbr`bc`, build_rec_env_merge] \\ rw[]
        \\ irule ALOOKUP_ALL_DISTINCT_MEM
        \\ simp[MAP_MAP_o, MEM_MAP, EXISTS_PROD, o_DEF, Abbr`funs'`, UNCURRY, ETA_AX]
        \\ simp[compile_funs_map, MAP_MAP_o, o_DEF, UNCURRY, ETA_AX] \\ fs[FST_triple]
        \\ simp[MEM_MAP, EXISTS_PROD]
        \\ metis_tac[])
      \\ drule_then (fn t => CHANGED_TAC (DEP_REWRITE_TAC [t]))
            evaluate_MAP_Var_local
      \\ simp[pmatch_def, pmatch_stamps_ok_def]
      \\ qmatch_goalsub_abbrev_tac`MAP f funs`
      \\ `MAP f funs = MAP Pvar (MAP FST funs)`
        by simp[Abbr`f`, MAP_MAP_o, o_DEF, UNCURRY, LAMBDA_PROD]
      \\ fs[Abbr`f`, pmatch_list_MAP_Pvar]
      \\ simp[Abbr`bc`, build_rec_env_merge]
      \\ simp[REVERSE_ZIP, MAP_REVERSE]
      \\ qmatch_goalsub_abbrev_tac`evaluate <| v := bc; c := _ |>`
      \\ qmatch_goalsub_abbrev_tac`ZIP zz`
      \\ `bc = REVERSE (ZIP zz)`
      by (
        simp[Abbr`bc`, Abbr`zz`, Abbr`funs'`, compile_funs_map, REVERSE_ZIP]
        \\ simp[MAP_MAP_o, o_DEF, UNCURRY]
        \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] )
      \\ fs[Once SWAP_REVERSE]
      \\ ntac 2 (pop_assum kall_tac) (* remove zz *)
      \\ `evaluate <|v := bc; c := flat_c |> s_i1 [stores] =
          evaluate <|v := REVERSE bc; c := flat_c |> s_i1 [stores]` suffices_by rw[]
      \\ `ALL_DISTINCT (MAP FST bc)` by (
        simp[Abbr`bc`, MAP_MAP_o, o_DEF, UNCURRY, ETA_AX]
        \\ simp[Abbr`funs'`, GSYM compile_funs_dom] )
      \\ pop_assum mp_tac
      \\ qunabbrev_tac`stores`
      (*
      \\ `MAP FST bc = MAP FST funs`
      by (
        simp[Abbr`bc`, MAP_MAP_o, GSYM compile_funs_dom, Abbr`funs'`, o_DEF, UNCURRY, ETA_AX]
        \\ simp[FST_triple] )
      \\ pop_assum mp_tac
      *)
      \\ rpt (pop_assum kall_tac)
      \\ qid_spec_tac`bc` \\ qid_spec_tac`s_i1`
      \\ qspec_tac(`idx.vidx`,`n`)
      \\ Induct_on`funs` \\ simp[FORALL_PROD, let_none_list_def]
      >- ( simp[evaluate_def] )
      \\ Cases_on`funs` \\ fs[let_none_list_def]
      >- (
        simp[evaluate_def, PULL_EXISTS]
        \\ rw[alookup_distinct_reverse] )
      \\ PairCases_on`h` \\ fs[]
      \\ rw[evaluate_def, alookup_distinct_reverse, opt_bind_lem]
      \\ CASE_TAC \\ fs[]
      \\ CASE_TAC \\ fs[]
      \\ CASE_TAC \\ fs[]
      \\ CASE_TAC \\ fs[]
      \\ fs[o_DEF, ADD1]
      \\ first_x_assum(qspec_then`n+1`mp_tac)
      \\ simp[]) >>
    pop_assum (fn th => rewrite_tac [th]) >>
    qpat_x_assum `Abbrev (e1 = _)` kall_tac >>
    simp [evaluate_def] >>
    Cases_on `evaluate s env [Letrec funs (Con NONE (MAP (λ(f,_). Var (Short f)) funs))]` >>
    rename [`_ = (s_i2,res)`] >>
    drule compile_exp_correct >>
    disch_then (qspecl_then [`comp_map`,`s_i1`,`None`,`genv.c`,`flat_c`] mp_tac) >>
    impl_tac THEN1
     (rfs [invariant_def,evaluate_Letrec_Var] \\ rveq \\ fs [] \\ fs []
      \\ match_mp_tac global_env_inv_weak
      \\ asm_exists_tac \\ fs [] \\ fs [subglobals_def])
    \\ strip_tac \\ fs [] >> rfs [] \\ fs []
    \\ fs [compile_exp_def, extend_env_nsEmpty_c] \\ rfs []
    \\ rfs [evaluate_Letrec_Var] \\ rveq \\ fs []
    \\ qabbrev_tac `vs = MAP (λ(f,x,e). Recclosure env funs f) funs`
    \\ `LENGTH vs = LENGTH funs` by fs [Abbr `vs`]
    \\ rveq \\ Cases_on `r_i1` \\ fs [result_rel_cases] \\ rveq \\ fs []
    \\ qpat_x_assum `v_rel _ (Conv NONE vs) _` mp_tac
    \\ Cases_on `y` \\ simp [Once v_rel_cases]
    \\ strip_tac \\ rveq
    \\ fs [pmatch_def,pmatch_rows_def]
    \\ `LENGTH funs = LENGTH l` by
          (imp_res_tac LIST_REL_LENGTH \\ fs [])
    \\ fs [pmatch_def, pmatch_stamps_ok_def]
    \\ qexists_tac `s1_i1 with globals := LUPDATE_EACH idx.vidx s_i1.globals l` \\ fs []
    \\ qexists_tac `flat_c`
    \\ qexists_tac `<| v := LUPDATE_EACH idx.vidx s_i1.globals l; c := genv.c |>`
    \\ fs []
    \\ conj_tac >- (
      simp [UNCURRY_EQ_comp_FST, GSYM MAP_MAP_o, pmatch_list_vars_eq_Match]
      \\ qunabbrev_tac `stores`
      \\ simp [pairTheory.ELIM_UNCURRY]
      \\ DEP_REWRITE_TAC [evaluate_let_none_list_MAPi]
      \\ `MAP (λ(f,_). Pvar f) funs =
          MAP (λx. Pvar (FST x)) funs` by
            (qid_spec_tac `funs` \\ Induct \\ fs [FORALL_PROD]) \\ fs []
      \\ fs [MAP_MAP_o,o_DEF]
      \\ simp [rich_listTheory.MAP_REVERSE, listTheory.MAP_ZIP]
      \\ fs [FST_triple, GSYM listTheory.LIST_TO_SET_MAP, listTheory.MAP_ZIP]
      \\ conj_tac THEN1
       (fs [invariant_def,s_rel_cases]
        \\ reverse (rpt strip_tac) \\ rfs []
        \\ TRY (first_x_assum match_mp_tac)
        \\ fs [] \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
      \\ simp [flatSemTheory.state_component_equality, Unitv_def]
      \\ AP_TERM_TAC
      \\ rw [LIST_EQ_REWRITE, EL_MAP]
      \\ DEP_REWRITE_TAC [alistTheory.alookup_distinct_reverse]
      \\ conj_asm1_tac >- simp [MAP_ZIP]
      \\ drule (REWRITE_RULE [Once CONJ_COMM] alistTheory.ALOOKUP_ALL_DISTINCT_EL)
      \\ simp []
      \\ disch_then drule
      \\ simp [EL_ZIP, EL_MAP])
    \\ unabbrev_all_tac
    \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
    \\ fs [invariant_def] \\ fs []
    \\ rw [] \\ fs [subglobals_def,LENGTH_LUPDATE_EACH]
    THEN1
     (rw [] \\ irule (GSYM EL_LUPDATE_EACH) \\ CCONTR_TAC \\ fs [NOT_LESS]
      \\ res_tac \\ fs [])
    THEN1
     (`idx.vidx <= n` by fs [] \\ res_tac \\ pop_assum (fn th => fs [GSYM th])
      \\ match_mp_tac EL_LUPDATE_EACH_PAST \\ fs [])
    THEN1
     (fs [s_rel_cases]
      \\ irule LIST_REL_mono
      \\ qexists_tac `sv_rel <|v := s1_i1.globals; c := genv.c|>`
      \\ rw []
      \\ irule sv_rel_weak
      \\ rw []
      \\ qexists_tac `<|v := s_i1.globals; c := genv.c|>`
      \\ rw [subglobals_def,LENGTH_LUPDATE_EACH]
      \\ rw [] \\ irule (GSYM EL_LUPDATE_EACH) \\ CCONTR_TAC \\ fs [NOT_LESS]
      \\ res_tac \\ fs [])
    THEN1
     (rw [env_domain_eq_def, semanticPrimitivesTheory.build_rec_env_def,alloc_defs_def]
      \\ qspec_tac (`Recclosure env funs`,`h`)
      \\ qspec_tac (`idx.vidx`,`x`)
      \\ qid_spec_tac `t`
      \\ qid_spec_tac `funs`
      \\ Induct \\ fs [alloc_defs_def,FORALL_PROD] \\ fs []
      \\ fs [EXTENSION] \\ metis_tac [])
    \\ rw [v_rel_eqns, nsLookup_alist_to_ns_some,
           semanticPrimitivesTheory.build_rec_env_def, EL_LUPDATE]
    \\ simp [alloc_defs_def,PULL_EXISTS,LENGTH_LUPDATE_EACH]
    \\ drule nsLookup_FOLDR_SOME_IMP \\ strip_tac
    \\ rveq \\ fs []
    \\ qexists_tac `idx.vidx + i` \\ fs [] \\ rfs [EL_LUPDATE_EACH_HIT]
    \\ simp [GSYM PULL_EXISTS]
    \\ conj_tac
    THEN1
     (ntac 2 (pop_assum mp_tac)
      \\ qpat_x_assum `ALL_DISTINCT (MAP (λ(x,y,z). x) funs)` mp_tac
      \\ qspec_tac (`idx.vidx`,`x`)
      \\ qid_spec_tac `t`
      \\ qid_spec_tac `i`
      \\ qpat_x_assum `LENGTH funs = LENGTH l` (assume_tac o GSYM) \\ fs []
      \\ qid_spec_tac `funs`
      \\ Induct \\ fs [FORALL_PROD]
      \\ Cases_on `i` \\ fs [] \\ fs [alloc_defs_def] \\ fs []
      \\ fs [MEM_MAP,FORALL_PROD]
      \\ rpt strip_tac
      \\ IF_CASES_TAC
      THEN1 (imp_res_tac EL_MEM \\ rfs [] \\ metis_tac [])
      \\ metis_tac [ADD_COMM, ADD_ASSOC,ADD1])
    \\ drule LIST_REL_IMP_EL \\ fs []
    \\ disch_then drule
    \\ strip_tac
    \\ irule v_rel_weak
    \\ qpat_x_assum `LENGTH funs = LENGTH l` (assume_tac o GSYM)
    \\ fs [EL_MEM] \\ rfs [EL_MAP]
    \\ fs [] \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [subglobals_def,LENGTH_LUPDATE_EACH]
    \\ rw [] \\ irule (GSYM EL_LUPDATE_EACH) \\ CCONTR_TAC \\ fs [NOT_LESS]
    \\ res_tac \\ fs [])
  >- ( (* Type definition *)
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [`genv`, `idx`, `comp_map`, `env`, `s`, `s_i1`, `flat_c`] >>
    Induct_on `type_def`
    >- ( (* No tds *)
      rw [evaluate_def] >>
      simp [extend_env_def, extend_dec_env_def, build_tdefs_def] >>
      fs [invariant_def] >>
      qexists_tac `genv` >>
      simp [] >>
      fs [v_rel_eqns, s_rel_cases] >>
      rw [env_domain_eq_def, subglobals_refl]) >>
    strip_tac >>
    rename [`EVERY check_dup_ctors (td::tds)`] >>
    `?tvs tn ctors. td = (tvs, tn ,ctors)` by metis_tac [pair_CASES] >>
    rw [evaluate_def] >>
    pairarg_tac >>
    fs [] >>
    simp [evaluate_def] >>
    drule evaluate_alloc_tags >>
    disch_then drule >>
    simp [lookup_def] >>
    impl_tac
    >- (
      fs [terminationTheory.check_dup_ctors_thm] >>
      fs [invariant_def]) >>
    reverse (rw [])
    >- (
      fs [is_fresh_type_def, invariant_def] >>
      rw [] >>
      fs[s_rel_cases] >>
      metis_tac [DECIDE ``!x:num. x ≥ x``]) >>
    first_x_assum drule >>
    fs [local_c_rel_def] >>
    disch_then (first_assum o mp_then (Pat `global_env_inv`) mp_tac) >>
    impl_keep_tac
    >- (
      fs [SUBSET_DEF]
      \\ drule_then irule alloc_tags_local_c_rel1
      \\ fs [terminationTheory.check_dup_ctors_thm]
    ) >>
    rw [] >>
    qpat_x_assum `_ = FDOM _` (mp_tac o GSYM) >>
    rw [] >>
    fs [combinTheory.o_DEF, LAMBDA_PROD] >>
    fs [] >>
    `!x y. SUC x + y = x + SUC y` by decide_tac >>
    asm_simp_tac std_ss [] >>
    rw [] >>
    qmatch_goalsub_abbrev_tac`evaluate_decs xxx` >>
    qmatch_asmsub_abbrev_tac`evaluate_decs xxy` >>
    `xxx = xxy` by (
      simp[Abbr`xxx`,Abbr`xxy`,state_component_equality]
      \\ fs[invariant_def, s_rel_cases] )
    \\ fs[UNION_COMM] \\
    qexists_tac `genv'` >>
    rw []
    >- (
      irule funion_submap >>
      qexists_tac `genv_c` >>
      rw [DISJOINT_DEF, EXTENSION] >>
      CCONTR_TAC >>
      fs [] >>
      rw [] >>
      fs [FLOOKUP_DEF, invariant_def] >>
      metis_tac [DECIDE ``!x. x ≥ x:num``])
    >- (
      fs [env_domain_eq_def, build_tdefs_def, ADD1] >>
      ONCE_REWRITE_TAC [nsAppend_foldl] >>
      rw [build_tdefs_no_mod, nsDom_nsAppend_flat, nsDomMod_nsAppend_flat,
          o_DEF, build_constrs_def, MAP_REVERSE, MAP_MAP_o, EXTENSION] >>
      eq_tac >>
      rw [MEM_MAP, EXISTS_PROD] >>
      metis_tac [FST])
   >- (
      fs [build_tdefs_def, v_rel_eqns] >>
      rw [] >>
      fs [nsLookup_nsAppend_some, ADD1]
      >- (
        res_tac >>
        qexists_tac `cn` >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some])
      >- (
        fs [build_constrs_def, nsLookup_alist_to_ns_some, env_domain_eq_def] >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some] >>
        qmatch_goalsub_abbrev_tac `nsLookup rest _ = SOME _` >>
        `nsLookup rest (Short x') = NONE`
        by (
          fs [nsLookup_nsDom, EXTENSION] >>
          metis_tac [NOT_SOME_NONE, option_nchotomy]) >>
        simp [] >>
        res_tac >>
        fs [namespaceTheory.id_to_mods_def] >>
        metis_tac [flookup_funion_submap]))
    >- (
      simp [Once nsAppend_foldl, build_tdefs_def]
      \\ irule local_c_rel1_nsAppend
      \\ fs [env_domain_eq_def, ADD1]
      \\ drule_then irule local_c_rel1_SUBSET
      \\ simp []
    )
  )
  >- ( (* type abbreviation *)
    fs [evaluate_def] >>
    qexists_tac `genv` >>
    fs [invariant_def, s_rel_cases, v_rel_eqns, extend_dec_env_def, extend_env_def,
        empty_env_def, env_domain_eq_def] >>
    metis_tac [subglobals_refl])
  >- ( (* exceptions *)
    reverse (rw [evaluate_def]) >>
    fs [invariant_def, s_rel_cases, v_rel_eqns]
    >- (
      fs [is_fresh_exn_def] >>
      rw [] >>
      metis_tac [DECIDE ``!x:num.x ≥ x``])
    >- (
      fs [is_fresh_exn_def] >>
      rw [] >>
      metis_tac [DECIDE ``!x:num.x ≥ x``]) >>
    qexists_tac `genv with c := genv.c |+ (((idx.eidx,NONE),LENGTH ts), ExnStamp s.next_exn_stamp)` >>
    rw []
    >- metis_tac [subglobals_refl]
    >- (
      fs [genv_c_ok_def] >>
      rw []
      >- fs [has_bools_def, FLOOKUP_UPDATE]
      >- (
        fs [has_exns_def, FLOOKUP_UPDATE] >>
        rw [] >>
        fs [FLOOKUP_DEF, is_fresh_exn_def])
      >- fs [has_lists_def, FLOOKUP_UPDATE]
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        rw []
        >- rw [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def]
        >- (
          fs [has_exns_def, div_stamp_def] >>
          res_tac >>
          Cases_on `stamp1` >>
          Cases_on `cn1` >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def])
        >- (
          fs [has_exns_def, div_stamp_def] >>
          res_tac >>
          Cases_on `stamp2` >>
          Cases_on `cn2` >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def])
        >- metis_tac [])
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        fs [FLOOKUP_DEF, FRANGE_DEF, s_rel_cases] >>
        rw [] >>
        metis_tac [DECIDE ``!x.x≥x:num``])
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        fs [FLOOKUP_DEF, FRANGE_DEF, s_rel_cases] >>
        rw [] >>
        metis_tac [DECIDE ``!x.x≥x:num``]))
    >- metis_tac [DECIDE ``x ≤ x:num``]
    >- (
      fs [IN_FRANGE] >>
      rw [DOMSUB_FAPPLY_THM])
    >- (
      fs [IN_FRANGE] >>
      rw [DOMSUB_FAPPLY_THM])
    >- (
      irule LIST_REL_mono >>
      qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
      rw [] >>
      irule sv_rel_weak >>
      rw [] >>
      qexists_tac `genv` >>
      rw [subglobals_refl] >>
      `genv = <|v := s_i1.globals; c := genv.c|>` by rw [theorem "global_env_component_equality"] >>
      metis_tac [])
    >- fs [EXTENSION]
    >- rw [env_domain_eq_def]
    >- rw [FLOOKUP_DEF]
    >- (
      simp [extend_env_def, extend_dec_env_def]
      \\ fs [local_c_rel_def, local_c_rel1_def]
      \\ fs [SUBSET_DEF]
      \\ rw [nsLookup_nsBind_If]
      \\ metis_tac []
    ))
  >- ( (* Module *)
    pairarg_tac >>
    fs [] >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rw [] >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    `r1 ≠ Rerr (Rabort Rtype_error)` by (every_case_tac >> fs []) >>
    fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    rw [] >>
    qexists_tac `genv'` >>
    simp [case_eq_thms, PULL_EXISTS] >>
    rpt (gen_tac ORELSE disch_tac) >>
    rw []
    >- (
      fs [env_domain_eq_def, lift_env_def] >>
      rw [nsDom_nsLift, nsDomMod_nsLift])
    >- (
      rw [] >>
      fs [v_rel_eqns] >>
      rw [lift_env_def, nsLookup_nsLift] >>
      CASE_TAC >>
      rw [] >>
      fs [])
    >- (
      fs [lift_env_def]
      \\ simp [local_c_rel1_nsLift]
    ))
  >- ( (* local *)
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs [] >>
    rveq >>
    imp_res_tac compile_decs_num_bindings >>
    split_pair_case_tac >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    impl_tac >- (simp [] >> CCONTR_TAC >> fs []) >>
    rw [] >>
    reverse (fs [case_eq_thms])
    >- ( (* err case *)
      fs [] >>
      rveq >>
      fs [] >>
      rveq >>
      drule evaluate_decs_append_err >>
      rw [] >>
      asm_exists_tac >>
      fs [] >>
      fs [invariant_def]
    ) >>
    (* result case *)
    rveq >>
    fs [] >>
    first_x_assum (drule_then drule) >>
    impl_tac
    >- (
      rw []
      >- (
        fs [local_c_rel_def]
        \\ metis_tac [local_c_rel1_extend, local_c_rel1_SUBSET, SUBSET_TRANS]
      )
      >- metis_tac [global_env_inv_append, global_env_inv_weak]
      \\ fs [subglobals_def]
    ) >>
    rw [] >>
    imp_res_tac evaluate_decs_append >>
    fs [] >>
    qexists_tac `genv''` >> fs [] >>
    metis_tac [SUBMAP_TRANS, subglobals_trans, SUBSET_TRANS]
  )
  >- ( (* Denv, bind a new env *)
    simp [evaluate_def]
    (* false, because compile_decs doesn't do anything here, and
       the invariant requires *something* to get bound on the flat side *)
    \\ cheat
  )
  >- ( (* empty list *)
    simp [evaluate_def, env_domain_eq_def, empty_env_def, v_rel_eqns]
    \\ metis_tac [SUBMAP_REFL, subglobals_refl]
  )
  >- ( (* cons list *)
    rpt gen_tac >>
    simp [compile_decs_def] >>
    qspec_tac (`d2::ds`, `ds`) >>
    rw [] >>
    ntac 2 (pairarg_tac \\ fs[])
    \\ rveq
    \\ qpat_x_assum`_ = (_,r)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw [] >>
      fs [] >>
      first_x_assum drule >>
      simp [] >>
      disch_then drule >>
      impl_tac
      >- (
        imp_res_tac compile_decs_num_bindings >>
        rw []) >>
      rw [] >>
      simp [PULL_EXISTS] >>
      drule_then (fn t => CHANGED_TAC (simp [t])) evaluate_decs_append_err >>
      goal_assum (first_assum o mp_then (Pat `result_rel`) mp_tac) >>
      fs [invariant_def] >>
      drule compile_decs_num_bindings >>
      fs [] >>
      rw [] >>
      fs [subglobals_def, GREATER_EQ] >>
      rfs []
    ) >>
    BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[] >>
    first_x_assum drule >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      rw []) >>
    rw [] >>
    `r' ≠ Rerr (Rabort Rtype_error)`
    by (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs []) >>
    fs [] >>
    first_x_assum drule >>
    `global_env_inv genv' (extend_env new_env1 comp_map) {} (extend_dec_env a env)`
    by metis_tac [global_env_inv_append, global_env_inv_weak] >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      fs [subglobals_def, local_c_rel_def] >>
      metis_tac [local_c_rel1_extend, local_c_rel1_SUBSET, SUBSET_TRANS]) >>
    rw [] >>
    drule_then drule evaluate_decs_append >>
    rw [] >>
    qexists_tac `genv''` >>
    rw [UNION_ASSOC]
    >- metis_tac [SUBMAP_TRANS]
    >- metis_tac [subglobals_trans]
    >- metis_tac [SUBSET_TRANS]
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      rw [] >>
      fs [] >>
      imp_res_tac env_domain_eq_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      imp_res_tac global_env_inv_weak >>
      drule global_env_inv_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def, case_eq_thms] >>
      rveq >> fs [] >>
      simp [extend_env_def] >>
      irule local_c_rel1_nsAppend >>
      fs [env_domain_eq_def] >>
      drule_then irule local_c_rel1_SUBSET >>
      simp []
    )
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      MAP_EVERY qexists_tac [`small_idx`] >>
      fs []))
);

Theorem compile_decs_correct:
   ! ^s env ds s' r s_i1 cfg ds_i1 next' genv flat_c.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    invariant genv cfg.next s s_i1 flat_c ∧
    local_c_rel cfg.mod_env.c env.c flat_c ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    source_to_flat$compile_prog cfg ds = (next', ds_i1) ∧
    global_env_inv genv cfg.mod_env {} env ∧
    cfg.next.vidx ≤ LENGTH genv.v
    ⇒
    ? ^s1_i1 genv' flat_c1 r_i1.
      flatSem$evaluate_decs s_i1 flat_c ds_i1 = (s1_i1,flat_c1,r_i1) ∧
      genv.c SUBMAP genv'.c ∧
      subglobals genv.v genv'.v ∧
      invariant genv' next'.next s' s1_i1 flat_c1 ∧
      (!env'.
        r = Rval env'
        ⇒
        r_i1 = NONE ∧
        env_domain_eq next'.mod_env env' ∧
        global_env_inv genv' next'.mod_env {} env' ∧
        local_c_rel1 next'.mod_env.c env'.c flat_c1) ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = SOME err_i1 ∧
          result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))
Proof
  rw [compile_prog_def, glob_alloc_def] >>
  pairarg_tac >>
  fs [] >>
  rveq >>
  fs [evaluate_def, do_app_def] >>
  qabbrev_tac `ext_glob = s_i1.globals ⧺ REPLICATE (next.vidx − cfg.next.vidx) NONE` >>
  drule compile_decs_correct' >>
  `invariant (genv with v := ext_glob) cfg.next s (s_i1 with globals := ext_glob) flat_c`
  by (
    fs [invariant_def, Abbr`ext_glob`] >>
    rw [EL_APPEND_EQN] >>
    fs []
    >- rw [EL_REPLICATE] >>
    fs [s_rel_cases] >>
    irule LIST_REL_mono >>
    qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
    rw [] >>
    irule sv_rel_weak >>
    rw [] >>
    qexists_tac `<|v := s_i1.globals; c := genv.c|>` >>
    rw [subglobals_def, EL_APPEND_EQN]) >>
  `global_env_inv (genv with v := ext_glob) cfg.mod_env {} env`
  by (
    irule global_env_inv_weak >>
    simp [] >>
    qexists_tac `genv` >>
    fs [invariant_def] >>
    rw [Abbr `ext_glob`, subglobals_def, EL_APPEND_EQN] >>
    rw []) >>
  rpt (disch_then drule) >>
  fs [] >>
  impl_tac
  >- (
    rw [Abbr`ext_glob`] >>
    fs [invariant_def] >>
    rfs []) >>
  strip_tac >>
  fs [Unitv_def] >>
  asm_exists_tac >> fs [] >>
  rw [Abbr`ext_glob`] >>
  fs [invariant_def] >>
  qpat_x_assum `subglobals _ _` mp_tac >>
  simp [subglobals_def, PULL_FORALL] >>
  strip_tac >>
  disch_then (qspec_then `n` mp_tac) >>
  simp [EL_APPEND_EQN] >>
  rw []
QED

(* TODO initial_ctors ⊆ FDOM genv.c could do and that follows
   from genv_c_ok *)
val precondition_def = Define`
  precondition s1 env1 conf ec ⇔
    ?genv.
      invariant genv conf.next s1 (initial_state s1.ffi s1.clock ec)
        initial_ctors ∧
      global_env_inv genv conf.mod_env {} env1 ∧
      conf.next.vidx ≤ LENGTH genv.v ∧
      FDOM genv.c = initial_ctors`;

Theorem precondition_local_c_rel:
  precondition s1 env1 conf ec ==>
  local_c_rel conf.mod_env.c env1.c initial_ctors
Proof
  rw [precondition_def, local_c_rel_def]
  \\ fs [local_c_rel1_def, Once v_rel_cases]
  \\ rw []
  \\ first_x_assum drule
  \\ rw []
  \\ simp []
  \\ metis_tac [FDOM_FLOOKUP]
QED

val SND_eq = Q.prove(
  `SND x = y ⇔ ∃a. x = (a,y)`,
  Cases_on`x`\\rw[]);

Theorem FST_SND_EQ_CASE:
  FST = (\(a, b). a) /\ SND = (\(a, b). b)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem compile_prog_correct:
   precondition s1 env1 c ec ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog
      (semantics ec s1.ffi (SND (compile_prog c prog)))
Proof
  rw[semantics_prog_def,SND_eq]
  \\ imp_res_tac precondition_local_c_rel
  \\ fs [precondition_def]
  \\ simp[flatSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[SND_eq]
  >- (
    fs[semantics_prog_def,SND_eq]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ fs [PAIR_FST_SND_EQ, FST_SND_EQ_CASE]
    \\ fs[evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ rveq \\ fs []
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ drule_then drule (GEN_ALL compile_decs_correct)
    \\ fs[initial_state_clock]
    \\ fs [result_rel_cases]
    \\ rename [`r <> Rerr _`]
    \\ Cases_on `r` \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ conj_tac
  >- (
    rw[] \\ rw[semantics_prog_def]
    \\ fs[evaluate_prog_with_clock_def]
    \\ qexists_tac`k`
    \\ pairarg_tac \\ fs[]
    \\ `r' ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ drule_then drule (GEN_ALL compile_decs_correct)
    \\ fs[FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ strip_tac
    \\ fs[invariant_def,s_rel_cases]
    \\ rveq \\ fs[]
    \\ fs [initial_state_def] \\ rfs []
    \\ every_case_tac \\ fs[]
    \\ rw[]
    \\ fs[result_rel_cases])
  \\ rw[]
  \\ simp[semantics_prog_def]
  \\ conj_tac
  >- (
    rw[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ drule_then drule (GEN_ALL compile_decs_correct)
    \\ fs[]
    \\ `r ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ fs [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [initial_state_clock]
    \\ strip_tac
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ rveq \\ fs[]
    \\ every_case_tac \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ fs[result_rel_cases]
    \\ Cases_on`r`\\fs[])
  \\ qmatch_abbrev_tac`lprefix_lub l1 (build_lprefix_lub l2)`
  \\ `l2 = l1`
  by (
    unabbrev_all_tac
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ fs[evaluate_prog_with_clock_def]
    \\ gen_tac
    \\ pairarg_tac \\ fs[]
    \\ AP_TERM_TAC
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ drule_then drule (GEN_ALL compile_decs_correct)
    \\ fs[]
    \\ `r ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ fs [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [initial_state_clock]
    \\ strip_tac
    \\ fs[]
    \\ rfs[invariant_def,s_rel_cases,initial_state_def])
  \\ fs[Abbr`l1`,Abbr`l2`]
  \\ match_mp_tac build_lprefix_lub_thm
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF]
  \\ REWRITE_TAC[IMAGE_COMPOSE]
  \\ match_mp_tac prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def,PULL_EXISTS]
  \\ simp[evaluate_prog_with_clock_def]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ metis_tac[evaluatePropsTheory.evaluate_decs_ffi_mono_clock,
               evaluatePropsTheory.io_events_mono_def,
               LESS_EQ_CASES,FST]
QED

(* - connect semantics theorems of flat-to-flat passes --------------------- *)

val _ = set_grammar_ancestry
  (["flat_elimProof", "flat_patternProof"]
   @ grammar_ancestry);

Theorem compile_flat_correct:
   compile_flat cfg prog = (cfg', prog') /\
   semantics (Eval ec) ffi prog <> Fail
   ==>
   semantics (Eval ec) ffi prog =
   semantics (extend_eval_config pat_cfg ec) ffi prog'
Proof
  rw [compile_flat_def]
  \\ metis_tac [flat_patternProofTheory.compile_decs_semantics,
        flat_elimProofTheory.flat_remove_semantics]
QED

Theorem compile_semantics:
   source_to_flatProof$precondition s env c (Eval ec) ⇒
   ¬semantics_prog s env prog Fail ⇒
   semantics_prog s env prog
      (semantics (extend_eval_config pat_cfg ec) s.ffi (SND (compile c prog)))
Proof
  rw [compile_def] \\ pairarg_tac \\ fs []
  \\ imp_res_tac compile_prog_correct \\ rfs []
  \\ `semantics (Eval ec) s.ffi p' <> Fail` by (CCONTR_TAC \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ drule_then drule compile_flat_correct
  \\ metis_tac []
QED

(* - esgc_free theorems for compile_exp ------------------------------------ *)

Theorem compile_exp_esgc_free:
   (!tra env exp.
      esgc_free (compile_exp tra env exp) /\
      set_globals (compile_exp tra env exp) = {||}) /\
   (!tra env exps.
      EVERY esgc_free (compile_exps tra env exps) /\
      elist_globals (compile_exps tra env exps) = {||}) /\
   (!tra env pes.
      EVERY esgc_free (MAP SND (compile_pes tra env pes)) /\
      elist_globals (MAP SND (compile_pes tra env pes)) = {||}) /\
   (!tra env funs.
      EVERY esgc_free (MAP (SND o SND) (compile_funs tra env funs)) /\
      elist_globals (MAP (SND o SND) (compile_funs tra env funs)) = {||})
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ fs [compile_exp_def]
  >-
   (PURE_FULL_CASE_TAC \\ fs []
    \\ rename [`compile_var _ x`] \\ Cases_on `x` \\ fs [compile_var_def]
    \\ EVAL_TAC )
  \\ fs [nsAll_nsBind]
  >-
   (IF_CASES_TAC \\ fs []
    \\ fs [elist_globals_eq_empty, EVERY_MEM]
    \\ fs [FOLDR_REVERSE, FOLDL_invariant, EVERY_MEM]
    >-
     (FOLDL_invariant |> Q.ISPECL [`\x. set_globals x = {||}`]
      |> BETA_RULE |> match_mp_tac
      \\ fs [op_gbag_def])
    \\ Cases_on `op` \\ fs [op_gbag_def, astOp_to_flatOp_def])
  >-
   (Cases_on `lop` \\ fs []
    \\ res_tac \\ fs []
    \\ EVAL_TAC)
QED

(* - esgc_free theorems for compile_decs ----------------------------------- *)

Theorem set_globals_make_varls:
   ∀a b c d. flatProps$set_globals (make_varls a b c d) =
             LIST_TO_BAG (MAP ((+)c) (COUNT_LIST (LENGTH d)))
Proof
  recInduct source_to_flatTheory.make_varls_ind
  \\ rw[source_to_flatTheory.make_varls_def]
  >- EVAL_TAC
  >- ( EVAL_TAC \\ rw[] \\ rw[EL_BAG] )
  \\ simp[COUNT_LIST_def, MAP_MAP_o, ADD1, o_DEF, LIST_TO_BAG_def]
  \\ EVAL_TAC
  \\ AP_THM_TAC
  \\ simp[FUN_EQ_THM]
  \\ simp[BAG_INSERT_UNION]
QED

Theorem make_varls_esgc_free:
   !n t idx xs.
     esgc_free (make_varls n t idx xs)
Proof
  ho_match_mp_tac make_varls_ind
  \\ rw [make_varls_def]
QED

Theorem nsAll_extend_env:
   nsAll P e1.v /\ nsAll P e2.v ==> nsAll P (extend_env e1 e2).v
Proof
  simp [extend_env_def, nsAll_nsAppend]
QED

Theorem let_none_list_esgc_free:
  ∀es. EVERY esgc_free es ⇒ esgc_free (let_none_list es)
Proof
  recInduct let_none_list_ind
  \\ rw[let_none_list_def]
QED

Theorem compile_decs_esgc_free:
   !n next env decs n1 next1 env1 decs1.
     compile_decs n next env decs = (n1, next1, env1, decs1)
     ==>
     EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet decs1))
Proof
  ho_match_mp_tac compile_decs_ind
  \\ rw [compile_decs_def]
  \\ fs [compile_exp_esgc_free, make_varls_esgc_free]
  \\ fs [EVERY_MAP, EVERY_FILTER, MAP_FILTER]
  \\ simp [EVERY_MEM, MEM_MAPi, PULL_EXISTS, UNCURRY]
  \\ TRY
   (irule nsAll_alist_to_ns
    \\ fs [ELIM_UNCURRY]
    \\ ho_match_mp_tac
      (EVERY_CONJ |> REWRITE_RULE [EQ_IMP_THM] |> SPEC_ALL |> CONJUNCT2)
    \\ conj_tac
    >- simp [GSYM EVERY_MAP]
    \\ qmatch_goalsub_abbrev_tac `EVERY _ xs`
    \\ `EVERY (\x. set_globals x = {||}) (MAP SND xs)`
        suffices_by rw [EVERY_MAP]
    \\ simp [EVERY_MEM, GSYM elist_globals_eq_empty, Abbr`xs`]
    \\ NO_TAC)
  >- (match_mp_tac let_none_list_esgc_free
      \\ rw[MAPi_enumerate_MAP, EVERY_MAP, UNCURRY] )
  \\ fs [empty_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [EVERY_MEM, lift_env_def]
  \\ last_x_assum mp_tac
  \\ impl_tac \\ rw []
QED

(* - the source_to_flat compiler produces things which are esgc_free ------- *)

Theorem compile_prog_esgc_free:
   compile_prog c p = (c1, p1)
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet p1))
Proof
  rw [compile_prog_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ fs [glob_alloc_def]
  \\ metis_tac [compile_decs_esgc_free]
QED

Theorem compile_flat_esgc_free:
   compile_flat cfg ds = (cfg', ds') /\
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds'))
Proof
  rw [compile_flat_def, compile_def]
  \\ drule_then irule flat_patternProofTheory.compile_decs_esgc_free
  \\ simp [flat_elimProofTheory.remove_flat_prog_esgc_free]
QED

Theorem compile_esgc_free:
   compile c p = (c1, p1)
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet p1))
Proof
  rw [compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ metis_tac [compile_prog_esgc_free, compile_flat_esgc_free]
QED

val mem_size_lemma = Q.prove ( `list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)`,
  Induct_on `xs` \\ rw [list_size_def] \\ fs []);

val num_bindings_def = tDefine"num_bindings"
  `(num_bindings (Dlet _ p _) = LENGTH (pat_bindings p [])) ∧
   (num_bindings (Dletrec _ f) = LENGTH f) ∧
   (num_bindings (Dmod _ ds) = SUM (MAP num_bindings ds)) ∧
   (num_bindings (Dlocal lds ds) = SUM (MAP num_bindings lds)
        + SUM (MAP num_bindings ds)) ∧
   (num_bindings _ = 0)`
(wf_rel_tac`measure dec_size`
  \\ fs [terminationTheory.dec1_size_eq]
  \\ rpt (match_mp_tac mem_size_lemma ORELSE strip_tac)
  \\ fs []);

val _ = export_rewrites["num_bindings_def"];

Theorem compile_decs_num_bindings:
   ∀n next env ds e f g p. compile_decs n next env ds = (e,f,g,p) ⇒
   next.vidx ≤ f.vidx ∧
   SUM (MAP num_bindings ds) = f.vidx - next.vidx
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[]
  \\ pairarg_tac \\ fsrw_tac[ETA_ss][]
  \\ pairarg_tac \\ fs[] \\ rw[]
QED

val COUNT_LIST_ADD_SYM = COUNT_LIST_ADD
  |> CONV_RULE (SIMP_CONV bool_ss [Once ADD_SYM]);

Theorem MAPi_SNOC: (* TODO: move *)
  !xs x f. MAPi f (SNOC x xs) = SNOC (f (LENGTH xs) x) (MAPi f xs)
Proof
  Induct \\ fs [SNOC]
QED

Theorem compile_decs_elist_globals:
  ∀n next env ds e f g p.
    compile_decs n next env ds = (e,f,g,p) ⇒
    elist_globals (MAP dest_Dlet (FILTER is_Dlet p)) =
      LIST_TO_BAG (MAP ((+) next.vidx) (COUNT_LIST (SUM (MAP num_bindings ds))))
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[set_globals_make_varls]
  \\ rw[compile_exp_esgc_free]
  \\ TRY ( EVAL_TAC \\ rw [EL_BAG] \\ NO_TAC )
  >-
   (qid_spec_tac `funs`
    \\ ho_match_mp_tac SNOC_INDUCT
    \\ fs [MAPi_SNOC,COUNT_LIST_SNOC]
    \\ fs [MAP_SNOC] \\ fs [SNOC_APPEND, LIST_TO_BAG_APPEND,FORALL_PROD]
    \\ fs [let_none_list_def,COUNT_LIST_def]
    \\ rw [] \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ qpat_abbrev_tac `xs = MAPi _ _`
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on `xs` \\ fs [let_none_list_def] THEN1 EVAL_TAC
    \\ Cases_on `xs` \\ fs [let_none_list_def,ASSOC_BAG_UNION])
  >- (
    simp[MAPi_enumerate_MAP, FILTER_MAP, o_DEF, UNCURRY]
    \\ EVAL_TAC )
  >- (
    pairarg_tac \\ fs[] \\ rveq
    \\ srw_tac[ETA_ss][] )
  >- (
    pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rveq
    \\ simp [flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ rw []
    \\ imp_res_tac compile_decs_num_bindings
    \\ rw [COUNT_LIST_ADD_SYM]
    \\ srw_tac [ETA_ss] [LIST_TO_BAG_APPEND, MAP_MAP_o, o_DEF]
    \\ AP_TERM_TAC
    \\ simp [MAP_EQ_f]
  )
  >- (
    pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rveq
    \\ simp[flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ rw[]
    \\ imp_res_tac compile_decs_num_bindings
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`a + (b + c)`
    \\ `a + (b + c) = b + (a + c)` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[Once COUNT_LIST_ADD,SimpRHS]
    \\ simp[LIST_TO_BAG_APPEND]
    \\ simp[MAP_MAP_o, o_DEF]
    \\ rw[]
    \\ AP_TERM_TAC
    \\ fs[MAP_EQ_f]
  )
QED

Theorem compile_flat_sub_bag:
  compile_flat cfg p = (cfg', p') ==>
  elist_globals (MAP dest_Dlet (FILTER is_Dlet p')) <=
  elist_globals (MAP dest_Dlet (FILTER is_Dlet p))
Proof
  fs [source_to_flatTheory.compile_flat_def]
  \\ metis_tac [
       flat_elimProofTheory.remove_flat_prog_sub_bag,
       flat_patternProofTheory.compile_decs_elist_globals]
QED

Theorem SUB_BAG_IMP:
  (B1 <= B2) ==> x ⋲ B1 ==> x ⋲ B2
Proof
  rw []
  \\ imp_res_tac bagTheory.SUB_BAG_SET
  \\ imp_res_tac SUBSET_IMP
  \\ fs []
QED

Theorem monotonic_globals_state_co_compile:
  source_to_flat$compile conf prog = (conf',p) ∧ FST (FST (orac 0)) = conf' ∧
  is_state_oracle source_to_flat$compile orac ⇒
  oracle_monotonic
    (SET_OF_BAG ∘ elist_globals ∘ MAP flatProps$dest_Dlet ∘
      FILTER flatProps$is_Dlet ∘ SND) $<
    (SET_OF_BAG (elist_globals (MAP flatProps$dest_Dlet
      (FILTER flatProps$is_Dlet p))))
    (state_co source_to_flat$compile orac)
Proof
  rw []
  \\ drule_then irule (Q.ISPEC `\c. c.next.vidx` oracle_monotonic_state_init)
  \\ fs []
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [source_to_flatTheory.compile_def,
        source_to_flatTheory.compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac compile_decs_num_bindings
  \\ imp_res_tac compile_decs_esgc_free
  \\ imp_res_tac compile_decs_elist_globals
  \\ fs []
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ imp_res_tac compile_flat_sub_bag
  \\ drule_then drule SUB_BAG_IMP
  \\ fs [source_to_flatTheory.glob_alloc_def, flatPropsTheory.op_gbag_def]
  \\ fs [IN_LIST_TO_BAG, MEM_MAP, MEM_COUNT_LIST]
QED

val _ = export_theory ();
