open preamble mlstringTheory

val _ = new_theory"mlint";

val toChar_def = Define`
  toChar digit = if digit < 10 then CHR (ORD #"0" + digit)
  else CHR (ORD #"A" + digit - 10)`;

val toChar_HEX = Q.store_thm("toChar_HEX",
  `d < 16 ⇒ (toChar d = HEX d)`,
  strip_tac \\ rpt(fs[Once NUMERAL_LESS_THM] >- EVAL_TAC));

(* This should be smaller than the maximum smallint supported by the compiler
(see bvl_to_bviTheory for that. 2**28-1?) Also it must be a power of the radix
*)
val maxSmall_DEC_def = Define`maxSmall_DEC = 100000000n`;
val padLen_DEC_def = Define`
  padLen_DEC = LOG 10 maxSmall_DEC`;
val padLen_DEC_eq = save_thm("padLen_DEC_eq",CONV_RULE(RAND_CONV EVAL)padLen_DEC_def);

(* TODO: this might all be faster (less allocation in particular) using byte
arrays (and therefore not in pure) Without a strcat primitive, though, this way
could still make sense. *)

val zero_pad_def = Define`
  (zero_pad 0 acc = acc) ∧
  (zero_pad (SUC n) acc = zero_pad n (#"0" :: acc))`;

val zero_pad_thm = Q.store_thm("zero_pad_thm",
  `∀n acc. zero_pad n acc = REPLICATE n #"0" ++ acc`,
  Induct \\ rw[GSYM SNOC_REPLICATE,zero_pad_def] \\ EVAL_TAC);

val simple_toChars_def = Define`
  simple_toChars pad i acc =
    if i < 10 then zero_pad (pad-1) (toChar i :: acc)
    else simple_toChars (pad-1) (i DIV 10) (toChar (i MOD 10) :: acc)`;
val simple_toChars_ind = theorem"simple_toChars_ind";

val simple_toChars_thm = Q.store_thm("simple_toChars_thm",
  `∀pad i acc. simple_toChars pad i acc =
    REPLICATE (pad - LENGTH (num_to_dec_string i)) #"0" ++ num_to_dec_string i ++ acc`,
  ho_match_mp_tac simple_toChars_ind \\
  rw[ASCIInumbersTheory.num_to_dec_string_def,
     ASCIInumbersTheory.n2s_def] \\
  rw[Once simple_toChars_def]
  >- ( fs[NUMERAL_LESS_THM,zero_pad_thm] \\ EVAL_TAC )
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS,ADD1]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ match_mp_tac toChar_HEX
  \\ `i MOD 10 < 10` by simp[MOD_LESS]
  \\ rw[]);

val toChars_def = tDefine"toChars"`
  toChars chunk rest acc =
    if rest = 0 then simple_toChars 0 chunk acc
    else if rest < maxSmall_DEC then
      simple_toChars 0 rest
        (simple_toChars padLen_DEC chunk acc)
    else
      toChars (rest MOD maxSmall_DEC) (rest DIV maxSmall_DEC)
        (simple_toChars padLen_DEC chunk acc)`
(wf_rel_tac`measure (FST o SND)`
 \\ rw[maxSmall_DEC_def,DIV_LT_X] \\ fs[maxSmall_DEC_def]);
val toChars_ind = theorem"toChars_ind";

val toChars_thm = Q.store_thm("toChars_thm",
  `∀chunk rest acc. chunk < maxSmall_DEC ⇒
    (toChars chunk rest acc =
      num_to_dec_string (rest * maxSmall_DEC + chunk) ++ acc)`,
  ho_match_mp_tac toChars_ind
  \\ rw[]
  \\ rw[Once toChars_def]
  \\ rw[simple_toChars_thm,REPLICATE]
  \\ TRY (
    qspec_then`maxSmall_DEC`mp_tac DIVISION
    \\ impl_tac >- EVAL_TAC
    \\ disch_then(qspec_then`rest`mp_tac)
    \\ disch_then(CHANGED_TAC o SUBST1_TAC o SYM o ONCE_REWRITE_RULE[MULT_COMM] o CONJUNCT1))
  \\ rw[ASCIInumbersTheory.num_to_dec_string_def,ASCIInumbersTheory.n2s_def]
  \\ qspecl_then[`10`,`chunk + rest * maxSmall_DEC`,`padLen_DEC`]mp_tac n2l_DIV_MOD
  \\ (impl_tac >- ( EVAL_TAC \\ simp[] ))
  \\ disch_then (SUBST1_TAC o SYM)
  \\ `10 ** padLen_DEC = maxSmall_DEC` by EVAL_TAC
  \\ pop_assum (SUBST_ALL_TAC)
  \\ simp[GSYM MAP_REVERSE,REVERSE_REPLICATE,map_replicate]
  \\ qspecl_then[`maxSmall_DEC`,`chunk`]mp_tac DIV_MULT
  \\ simp[]);

val toString_def = Define`
  toString i =
    if 0i ≤ i ∧ i < 10 then
      str (toChar (Num (ABS i)))
    else
      implode ((if i < 0i then "~" else "")++
               (toChars (Num (ABS i) MOD maxSmall_DEC) (Num (ABS i) DIV maxSmall_DEC) ""))`;

val toString_thm = Q.store_thm("toString_thm",
  `toString i = implode ((if i < 0i then "~" else "") ++ num_to_dec_string (Num (ABS i)))`,
  rw[toString_def]
  >- (`F` by intLib.COOPER_TAC)
  >- (
    rw[str_def]
    \\ AP_TERM_TAC
    \\ `Num (ABS i) < 10` by intLib.COOPER_TAC
    \\ simp[toChar_HEX]
    \\ simp[ASCIInumbersTheory.num_to_dec_string_def]
    \\ simp[ASCIInumbersTheory.n2s_def]
    \\ simp[Once numposrepTheory.n2l_def])
  \\ (
    AP_TERM_TAC \\ simp[]
    \\ `0 < maxSmall_DEC` by EVAL_TAC
    \\ simp[toChars_thm]
    \\ qspec_then`maxSmall_DEC`mp_tac DIVISION
    \\ simp[] ));


(* fromString Definitions *)
val fromChar_def = Define`
  fromChar char = ORD char - ORD #"0"`;

val fromChar_safe_def = Define`
  fromChar_safe char =
    case char of
      | #"0" => SOME 0n
      | #"1" => SOME 1n
      | #"2" => SOME 2n
      | #"3" => SOME 3n
      | #"4" => SOME 4n
      | #"5" => SOME 5n
      | #"6" => SOME 6n
      | #"7" => SOME 7n
      | #"8" => SOME 8n
      | #"9" => SOME 9n
      | _    => NONE`;

(* Equivalence between the safe and unsafe versions of fromChar *)
val fromChar_eq_safe = Q.store_thm("fromChar_eq_safe",
  `∀char. isDigit char ⇒ fromChar_safe char = SOME (fromChar char)`,
  Cases_on `char` \\ rw [isDigit_def,fromChar_safe_def,fromChar_def]
  \\ rpt (pop_assum (ASSUME_TAC o CONV_RULE (BINOP_CONV (TRY_CONV numLib.num_CONV)))
  \\ fs [LE]));

val fromChars_range_def = Define`
  fromChars_range l 0       str = 0 ∧
  fromChars_range l (SUC n) str =
    fromChars_range l n str * 10 + fromChar (strsub str (l + n))`;

val fromChars_range_safe_def = Define`
  fromChars_range_safe l 0       str = SOME 0 ∧
  fromChars_range_safe l (SUC n) str =
    let rest = OPTION_MAP ($* 10n) (fromChars_range_safe l n str) and
        head = fromChar_safe (strsub str (l + n))
    in OPTION_MAP2 $+ rest head`;

val fromChars_range_eq_safe = Q.store_thm("fromChars_range_eq_safe",
  `∀str l r. EVERY isDigit str ∧ l + r <= STRLEN str ⇒
     fromChars_range_safe l r (strlit str) =
     SOME (fromChars_range l r (strlit str))`,
  Induct_on `r`
  \\ rw [fromChars_range_safe_def
        , fromChars_range_def
        , fromChar_eq_safe
        , EVERY_EL]);

val fromChars_def = tDefine "fromChars" `
  fromChars 0 str = 0n ∧ (* Shouldn't happend *)
  fromChars n str =
    if n ≤ padLen_DEC
    then fromChars_range 0 n str
    (* TODO: This let issue is annoying *)
    else let n'    = n - padLen_DEC;
             front = fromChars n' str * maxSmall_DEC;
             back  = fromChars_range n' padLen_DEC str
         in front + back`
(wf_rel_tac `measure FST` \\ rw [padLen_DEC_eq]);
val fromChars_ind = theorem"fromChars_ind"

val fromChars_safe_def = tDefine "fromChars_safe" `
  fromChars_safe 0 str = SOME 0n ∧ (* Shouldn't happend *)
  fromChars_safe n str =
    if n ≤ padLen_DEC
    then fromChars_range_safe 0 n str
    (* TODO: This let issue is annoying *)
    else let n'    = n - padLen_DEC
         in let front = OPTION_MAP ($* maxSmall_DEC) (fromChars_safe n' str) and
                back  = fromChars_range_safe n' padLen_DEC str
            in OPTION_MAP2 $+ front back`
(wf_rel_tac `measure FST` \\ rw [padLen_DEC_eq]);
val fromChars_safe_ind = theorem"fromChars_safe_ind"

val fromChars_eq_safe = Q.store_thm("fromChars_eq_safe",
  `∀n s. EVERY isDigit (explode s) ∧ n ≤ strlen s ⇒
    fromChars_safe n s = SOME (fromChars n s)`,
  let val tactics = [fromChars_safe_def
                    , fromChars_def
                    , fromChars_range_eq_safe
                    , strlen_def
                    , explode_def]
  in recInduct fromChars_safe_ind
  \\ CONJ_TAC >- rw tactics
  \\ rw [] \\ Cases_on `str'`
  \\ rw tactics
  \\ fs tactics
  end);

val fromString_def = Define`
  fromString str = fromChars (strlen str) str`;

val fromString_safe_def = Define`
  fromString_safe str = fromChars_safe (strlen str) str`;

val fromString_eq_safe = Q.store_thm("fromString_eq_safe",
  `∀s. EVERY isDigit (explode s) ⇒ fromString_safe s = SOME (fromString s)`,
  simp [fromString_def, fromString_safe_def, fromChars_eq_safe]);

(* fromString auxiliar lemmas *)

val strsub_substring_0_thm = Q.store_thm("str_substring_0_thm",
  `∀m n l. m < n ⇒ strsub (substring l 0 n) m = strsub l m`,
  Cases_on `l` \\ Cases_on `s = ""`
      >- rw [strsub_def,substring_thm,substring_def,implode_def,explode_aux_def]
      >- (rw [strsub_def]
          \\ `0 < strlen (strlit s)` by (Cases_on `s` \\ rw [strlen_def,STRLEN_DEF])
          \\ rw [substring_thm]
          \\ Cases_on `n ≤ STRLEN s`
          \\ fs [MIN_DEF,strsub_def, implode_def,GSYM TAKE_SEG, EL_TAKE,SEG_LENGTH_ID]));

val fromChars_range_0_substring_thm = Q.store_thm("fromChars_range_0_substring_thm",
  `∀m r s. r ≤ m ⇒ fromChars_range 0 r s = fromChars_range 0 r (substring s 0 m)`,
  Induct_on `r` \\ rw [fromChars_range_def,strsub_substring_0_thm]);

val fromChars_range_split = Q.store_thm("fromChars_range_split",
  `∀m n s. m ≠ 0 ∧ m < n
    ⇒ fromChars_range 0 n s = 10 ** m * fromChars_range 0 (n - m) s + fromChars_range (n - m) m s`,
  Induct_on `m`
  >- rw []
  >- (`∀m k w. 10**SUC m*k + 10*w = 10*(10**m*k + w)` by simp [EXP]
      \\ Cases_on `n`
      \\ rw [fromChars_range_def]
      \\ Cases_on `m`
      \\ rw [fromChars_range_def]));

val MAP_REVERSE_thm = Q.store_thm("MAP_REVERSE_thm",
  `∀x f. x ≠ [] ⇒ MAP f (REVERSE x) = f (LAST x) :: MAP f (REVERSE (FRONT x))`,
  recInduct SNOC_INDUCT
  \\ rw [FRONT_APPEND]);

(* fromString proofs *)
val fromChar_thm = Q.store_thm("fromChar_thm",
  `∀ h. isDigit h ⇒ fromChar h = num_from_dec_string [h]`,
  Cases_on `h`
  \\ rw [isDigit_def]
  \\ rpt (pop_assum (ASSUME_TAC o CONV_RULE (BINOP_CONV (TRY_CONV numLib.num_CONV)))
          \\ fs [LE,fromChar_def]));

val fromChars_range_thm = Q.store_thm("fromChars_range_thm",
  `∀ str. EVERY isDigit str ⇒
          fromChars_range 0 (STRLEN str) (strlit str) = num_from_dec_string str`,
  recInduct SNOC_INDUCT
  \\ rw [fromChars_range_def
        ,ASCIInumbersTheory.num_from_dec_string_def]
  \\ `isDigit x` by fs [EVERY_SNOC]
  \\ rw [ASCIInumbersTheory.s2n_def
        , numposrepTheory.l2n_def
        , MAP_REVERSE_thm
        , substring_thm
        , MIN_DEF, implode_def
        , EL_LENGTH_SNOC
        , fromChar_thm |> computeLib.RESTR_EVAL_RULE [``fromChar``,``isDigit``]
        , fromChars_range_0_substring_thm  |> SPEC_ALL
                                           |> INST [``m : num`` |->  ``r : num``]
                                           |> SIMP_RULE std_ss []
                                           |> Once
        , SEG_0_SNOC |> SPEC ``LENGTH l``
                     |> SPEC ``l : 'a list``
                     |> SIMP_RULE std_ss [SEG_LENGTH_ID]]
  \\ fs [ASCIInumbersTheory.s2n_def,EVERY_SNOC]
  \\  Cases_on `l`
  \\ rw [fromChars_range_def,fromChar_def]);

val fromChars_range_eq = Q.store_thm("fromChars_range_eq",
  `∀n s. n ≤ (strlen s) ⇒ fromChars n s = fromChars_range 0 n s`,
  recInduct fromChars_ind
  \\ rw [fromChars_def
        , fromChars_range_def
        , padLen_DEC_eq
        , maxSmall_DEC_def
        , fromChars_range_split |> SPEC ``8n`` |> SIMP_RULE std_ss [] |> GSYM]);

val fromString_fromChars_range = Q.store_thm("fromString_fromChars_range",
  `∀str. fromString str = fromChars_range 0 (strlen str) str`,
  simp [fromString_def, fromChars_range_eq]);

val fromString_thm = Q.store_thm("fromString_thm",
  `∀str. EVERY isDigit str ⇒ fromString (strlit str) = num_from_dec_string str`,
  simp [fromString_fromChars_range,fromChars_range_thm]);

val fromString_safe_thm = Q.store_thm("fromString_safe_thm",
  `∀str. EVERY isDigit str ⇒
    fromString_safe (strlit str) = SOME (num_from_dec_string str)`,
  simp [fromString_eq_safe, fromString_thm]);

val _ = export_theory();
