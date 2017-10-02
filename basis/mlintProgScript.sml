open preamble
     ml_translatorLib ml_progLib mlintTheory
     mlbasicsProgTheory basisFunctionsLib

val _ = new_theory"mlintProg"

val _ = translation_extends "mlbasicsProg";

val _ = ml_prog_update (open_module "Int");

val _ = ml_prog_update (add_dec ``Dtabbrev unknown_loc [] "int" (Tapp [] TC_int)`` I);
val _ = trans "+" `(+):int->int->int`
val _ = trans "-" `(-):int->int->int`
val _ = trans "*" `int_mul`
val _ = trans "div" `(/):int->int->int`
val _ = trans "mod" `(%):int->int->int`
val _ = trans "<" `(<):int->int->bool`
val _ = trans ">" `(>):int->int->bool`
val _ = trans "<=" `(<=):int->int->bool`
val _ = trans ">=" `(>=):int->int->bool`
val _ = trans "~" `\i. - (i:int)`

val result = translate zero_pad_def

val result = translate toChar_def
val tochar_side_def = definition"tochar_side_def";
val tochar_side = Q.prove(
  `∀x. tochar_side x <=> (~(x < 10) ==> x < 201)`,
  rw[tochar_side_def])
  |> update_precondition;

val result = translate simple_toChars_def

val simple_toChars_side = Q.prove(
  `∀x y z. simple_tochars_side x y z = T`,
  ho_match_mp_tac simple_toChars_ind \\ rw[]
  \\ rw[Once (theorem"simple_tochars_side_def")])
  |> update_precondition;

val _ = save_thm("toChars_ind",
   toChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val result = translate
  (toChars_def |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val _ = next_ml_names := ["toString"];

val result = translate
  (toString_def |> REWRITE_RULE[maxSmall_DEC_def])
val tostring_side = Q.prove(
  `∀x. tostring_side x = T`,
  rw[definition"tostring_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val result = translate fromChar_def;
val result = translate fromChars_range_def;

val _ = save_thm("fromChars_ind",
  fromChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val result = translate (fromChars_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val result = translate fromString_def;

val fromString_side = Q.prove(
  `∀x. fromstring_side x = T`,
  rw [definition"fromstring_side_def"
     , Once (theorem"fromchars_side_def")
     , theorem"fromchars_range_side_def"]
  \\ `x1 ≤ strlen x` by rw []
  \\ qpat_x_assum `strlen _ = SUC _` (K ALL_TAC)
  \\ completeInduct_on `x1`
  \\ rw [Once (theorem"fromchars_side_def")
        , theorem"fromchars_range_side_def"])
  |> update_precondition;


val result = translate fromChar_safe_def;
val result = translate fromChars_range_safe_def;

val _ = save_thm("fromChars_safe_ind",
  fromChars_safe_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val result = translate (fromChars_safe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val result = translate fromString_safe_def;

val fromString_safe_side = Q.prove(
  `∀x. fromstring_safe_side x = T`,
  rw [definition"fromstring_safe_side_def"
     , Once (theorem"fromchars_safe_side_def")
     , theorem"fromchars_range_safe_side_def"]
  \\ `x1 ≤ strlen x` by rw []
  \\ qpat_x_assum `strlen _ = SUC _` (K ALL_TAC)
  \\ completeInduct_on `x1`
  \\ rw [Once (theorem"fromchars_safe_side_def")
        , theorem"fromchars_range_safe_side_def"])
  |> update_precondition;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
