theory SubsetSum_DTM_Bridge3
  imports "SubsetSum_DTM_Bridge2"
begin

context Coverage_TM
begin

lemma baseline_only_j_from_ex:
  assumes le:   "kk ≤ length as"
      and dss:  "distinct_subset_sums as"
      and SOL:  "∃S ⊆ {..<length as}. sum_over as S = s"
  shows "∃j0<length (enumL as s kk).
          (Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
           (∀j'<length (enumL as s kk).
               j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)))"
proof -
  have ex:
    "∃j0<length (enumL as s kk).
       (∀j'<length (enumL as s kk).
          j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
    using DSS_baseline_only_j_ex[OF le dss _ SOL]
    by (metis DSS_hit Good_char_encR SOL dss enumL_set le length_pos_if_in_set)
  then obtain j0 where j0L: "j0 < length (enumL as s kk)"
    and all_miss:
      "∀j'<length (enumL as s kk).
         j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
    by blast
  have imp:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumL as s kk).
        j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
    using all_miss by simp
  show ?thesis using j0L imp by blast
qed

lemma correct_T_drive:
  fixes L R :: "nat ⇒ bool"
  shows
  "final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0) L)
   = run L R (T as s)"
proof -
  have "final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0) L)
        = run L R (tm_to_dtr' head0 stepf final_acc
                       (steps M (enc as s kk)) (conf M (enc as s kk) 0))"
    by (simp add: run_tm_to_dtr'[symmetric])
  also have "... = run L R (T as s)"
    by (simp add: T_def)
  finally show ?thesis .
qed

lemma correct_T_drive_enc:
  "final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0)
                    ((!) (enc as s kk)))
   = good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  using correct_T_drive correct_T by simp

(* generic T0→T bridge for run only *)
lemma correct_T0_run_bridge:
  fixes L R :: "nat ⇒ bool"
  shows "run L R (T0 as s) = run L R (T as s)"
proof -
  have "run L R (T0 as s)
        = final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0) L)"
    by (simp add: run_tm_to_dtr' T0_def)
  also have "... = run L R (T as s)"
    by (rule correct_T_drive)
  finally show ?thesis .
qed

(* was named 'correct_T' before; rename to avoid shadowing *)
lemma correct_T_enc:
  "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
   = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
proof -
  have "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk))
             (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
                (conf M (enc as s kk) 0))"
    by (simp add: T_def)
  also have "… = accepts M (enc as s kk)"
    by (simp add: tm_to_dtr_accepts)
  also have "… = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
    by (simp add: correctness)
  finally show ?thesis .
qed

lemma correct_T_LR_enc:
  "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)
   = good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  by (simp add: correct_T_enc)

lemma correct_T0_enc:
  "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T0 as s)
   = Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  have "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T0 as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    by (rule correct_T0_run_bridge)
  also have "... = good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    by (rule correct_T_LR_enc)
  finally show ?thesis
    by (simp add: Good_def)   (* RHS = run enc enc (T as s) *)
qed

(*lemma correct_T:
  "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
   = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"*)

definition Good0 ::
  "int list ⇒ int ⇒ (nat ⇒ bool) ⇒ (nat ⇒ bool) ⇒ bool"
where
  "Good0 as s L R ≡ run L R (T0 as s)"

lemma Good0_eq_of_run_eq:
  assumes "run L R (T as s) = run L' R' (T as s)"
  shows   "Good0 as s L R = Good0 as s L' R'"
proof -
  have "run L R (T0 as s) = run L R (T as s)"
    by (rule correct_T0_run_bridge)
  also have "… = run L' R' (T as s)"
    by (rule assms)
  also have "… = run L' R' (T0 as s)"
    by (rule correct_T0_run_bridge[symmetric])
  finally show ?thesis
    by (simp add: Good0_def)
qed

(* When both sides are the encoding, you can relate Good0 back to Good *)
lemma Good0_eq_Good_on_enc:
  "Good0 as s ((!) (enc as s kk)) ((!) (enc as s kk))
   = Good  as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  by (simp add: Good0_def correct_T0_enc)

lemma run_is_drive_T:
  "run L R (T as s) =
   final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0) L)"
  unfolding T_def
  by (simp add: run_tm_to_dtr')

lemma good_is_drive_enc:
  "good as s ((!) (enc as s kk)) ((!) (enc as s kk)) =
   final_acc (drive (steps M (enc as s kk)) (conf M (enc as s kk) 0) 
                    ((!) (enc as s kk)))"
proof -
  have "good as s ((!) (enc as s kk)) ((!) (enc as s kk)) = accepts M (enc as s kk)"
    using correctness by simp
  also have "... = final_acc (conf M (enc as s kk) (steps M (enc as s kk)))"
    by (simp add: accepts_sem)
  also have "... = final_acc (drive (steps M (enc as s kk)) 
                                     (conf M (enc as s kk) 0) 
                                     ((!) (enc as s kk)))"
    by (simp add: drive_conf)
  finally show ?thesis .
qed

lemma Good_from_run_T_enc:
  assumes "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) = result"
  shows "Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) = result"
proof -
  have "Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) 
        = good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    by (simp add: Good_def)
  also have "... = accepts M (enc as s kk)"
    using correctness by simp
  also have "... = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    using correct_T_LR_enc ‹Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) = 
    good as s ((!) (enc as s kk)) ((!) (enc as s kk))› calculation by blast
  also have "... = result"
    by (rule assms)
  finally show ?thesis .
qed

(* Immediate consequences of T_decides_good *)
lemma Good_eq_run_T:
  "Good as s L R = run L R (T as s)"
  using Good_def T_def T_decides_good
  by metis

lemma Good_eq_of_run_eq:
  assumes "run L R (T as s) = run L' R' (T as s)"
  shows "Good as s L R = Good as s L' R'"
  using assms T_decides_good by (simp add: Good_def)

(* Now Good_eq_when_run_eq_enc becomes trivial *)
lemma Good_eq_when_run_eq_enc:
  assumes RUN_EQ: "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) = 
                   run ((!) y) ((!) (enc as s kk)) (T as s)"
  shows "Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) = 
         Good as s ((!) y) ((!) (enc as s kk))"
  using assms by (rule Good_eq_of_run_eq)

lemma Good_swap_left_param:
  fixes F G :: "nat ⇒ bool"
  assumes jL: "j < length (enumL as s kk)"
  assumes OFF: "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j
                ⟹ Lval_at as s F j' = Lval_at as s G j'"
  assumes AT:  "Lval_at as s F j = Lval_at as s G j"
  shows "Good as s F ((!) (enc as s kk)) = Good as s G ((!) (enc as s kk))"
proof -
  have EQ:
    "(∃j'<length (enumL as s kk). Lval_at as s F j' ∈ set (enumR as s kk)) =
     (∃j'<length (enumL as s kk). Lval_at as s G j' ∈ set (enumR as s kk))"
  proof
    assume H: "∃j'<length (enumL as s kk). Lval_at as s F j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                   and Hit:  "Lval_at as s F j' ∈ set (enumR as s kk)" by blast
    consider (J) "j' = j" | (OFFC) "j' ≠ j" by blast
    then show "∃j''<length (enumL as s kk). Lval_at as s G j'' ∈ set (enumR as s kk)"
    proof cases
      case J
      with AT Hit j'L show ?thesis by auto
    next
      case OFFC
      with OFF[OF j'L] Hit j'L show ?thesis by auto
    qed
  next
    assume H: "∃j'<length (enumL as s kk). Lval_at as s G j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                   and Hit:  "Lval_at as s G j' ∈ set (enumR as s kk)" by blast
    consider (J) "j' = j" | (OFFC) "j' ≠ j" by blast
    then show "∃j''<length (enumL as s kk). Lval_at as s F j'' ∈ set (enumR as s kk)"
    proof cases
      case J
      with AT Hit j'L show ?thesis by auto
    next
      case OFFC
      with OFF[OF j'L] Hit j'L show ?thesis by auto
    qed
  qed
  show ?thesis using EQ Good_char_encR by simp
qed

lemma bridge_oLpp_param:
  fixes j0 :: nat
  assumes j0L:  "j0 < length (enumL as s kk)"
  assumes OFF:  "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j0
                 ⟹ Lval_at as s oL'' j' = Lval_at as s oL' j'"
  assumes AT0:  "Lval_at as s oL'' j0 = Lval_at as s oL' j0"
  shows "Good as s oL'' ((!) (enc as s kk)) = Good as s oL' ((!) (enc as s kk))"
proof -
  have EQ:
    "(∃j'<length (enumL as s kk). Lval_at as s oL'' j' ∈ set (enumR as s kk)) =
     (∃j'<length (enumL as s kk). Lval_at as s oL'  j' ∈ set (enumR as s kk))"
  proof
    assume "∃j'<length (enumL as s kk). Lval_at as s oL'' j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                     and Hit: "Lval_at as s oL'' j' ∈ set (enumR as s kk)" by blast
    consider (J0) "j' = j0" | (OFFC) "j' ≠ j0" by blast
    then show "∃j'<length (enumL as s kk). Lval_at as s oL' j' ∈ set (enumR as s kk)"
    proof cases
      case J0
      with AT0 Hit j'L show ?thesis by auto
    next
      case OFFC
      with OFF[OF j'L] Hit j'L show ?thesis by auto
    qed
  next
    assume "∃j'<length (enumL as s kk). Lval_at as s oL' j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                     and Hit: "Lval_at as s oL' j' ∈ set (enumR as s kk)" by blast
    consider (J0) "j' = j0" | (OFFC) "j' ≠ j0" by blast
    then show "∃j'<length (enumL as s kk). Lval_at as s oL'' j' ∈ set (enumR as s kk)"
    proof cases
      case J0
      with AT0 Hit j'L show ?thesis by auto
    next
      case OFFC
      with OFF[OF j'L] Hit j'L show ?thesis by auto
    qed
  qed
  thus ?thesis using Good_char_encR by simp
qed

lemma bridge_oLpp:
  assumes j0L:  "j0 < length (enumL as s kk)"
  assumes OFF:  "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j0
                 ⟹ Lval_at as s oL'' j' = Lval_at as s oL' j'"
  assumes AT0:  "Lval_at as s oL'' j0 = Lval_at as s oL' j0"
  shows "Good as s oL'' ((!) (enc as s kk)) = Good as s oL' ((!) (enc as s kk))"
  using bridge_oLpp_param[OF j0L OFF AT0] .

lemma run_eq_when_blocks_agree:
  assumes "∀j<length (enumL as s kk). Lval_at as s L j = Lval_at as s L' j"
      and "∀j<length (enumR as s kk). Rval_at as s R j = Rval_at as s R' j"
  shows "run L R (T as s) = run L' R' (T as s)"
    using assms T_decides_good Good_char_encR Good_char_encL Good_def good_def
    by metis

lemma read0_hits_L:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
      and jL:    "j < length (enumL as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
  sorry (* Information-theoretic coverage: 
          For M to be correct on all instances, it must read all blocks.
          Proof requires reasoning about multiple instances simultaneously.
          See Abboud-Bringmann-Fischer Lemma 1. *)

lemma read0_hits_R:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
      and jR:    "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
  sorry (* Symmetric information-theoretic argument for R-blocks *)

lemma coverage_blocks:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
      and kkpos: "kk > 0"
  shows "card (Base.read0 M (enc as s kk)) ≥ 
         length (enumL as s kk) + length (enumR as s kk)"
proof -
  (* Get a witness from each block *)
  have "∀j<length (enumL as s kk). ∃i∈Base.read0 M (enc as s kk). 
         i ∈ blockL_abs enc0 as s j"
    by (simp add: SOL dss le read0_hits_L)
  
  hence "∀j<length (enumL as s kk). 
          Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s j ≠ {}"
    by blast

  (* Pick one element from each L-block *)
  define pickL where "pickL j = (SOME i. i ∈ Base.read0 M (enc as s kk) ∧ 
                                           i ∈ blockL_abs enc0 as s j)" for j
  
  have pickL_props: "∀j<length (enumL as s kk). 
                      pickL j ∈ Base.read0 M (enc as s kk) ∧ 
                      pickL j ∈ blockL_abs enc0 as s j"
    using `∀j<length (enumL as s kk). ∃i∈Base.read0 M (enc as s kk). 
                                        i ∈ blockL_abs enc0 as s j`
          pickL_def
    by (metis (mono_tags, lifting) someI_ex)

  (* Similarly for R *)
  have "∀j<length (enumR as s kk). ∃i∈Base.read0 M (enc as s kk). 
         i ∈ blockR_abs enc0 as s kk j"
    by (simp add: SOL dss le read0_hits_R)

  define pickR where "pickR j = (SOME i. i ∈ Base.read0 M (enc as s kk) ∧ 
                                           i ∈ blockR_abs enc0 as s kk j)" for j

  have pickR_props: "∀j<length (enumR as s kk). 
                      pickR j ∈ Base.read0 M (enc as s kk) ∧ 
                      pickR j ∈ blockR_abs enc0 as s kk j"
    using `∀j<length (enumR as s kk). ∃i∈Base.read0 M (enc as s kk). 
                                        i ∈ blockR_abs enc0 as s kk j`
          pickR_def
    by (metis (mono_tags, lifting) someI_ex)

  (* All picked elements are distinct *)
  define picked where "picked = (pickL ` {..<length (enumL as s kk)}) ∪ 
                                 (pickR ` {..<length (enumR as s kk)})"

  have "card picked = length (enumL as s kk) + length (enumR as s kk)"
  proof -
    have L_inj: "inj_on pickL {..<length (enumL as s kk)}"
    proof (rule inj_onI)
      fix j1 j2 assume j1: "j1 ∈ {..<length (enumL as s kk)}" 
                   and j2: "j2 ∈ {..<length (enumL as s kk)}"
                   and eq: "pickL j1 = pickL j2"
      from j1 have "pickL j1 ∈ blockL_abs enc0 as s j1" 
        using pickL_props by simp
      from j2 have "pickL j2 ∈ blockL_abs enc0 as s j2" 
        using pickL_props by simp
      show "j1 = j2"
      proof (rule ccontr)
        assume "j1 ≠ j2"
        hence "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 = {}"
          using blockL_abs_disjoint j1 j2 by auto
        with `pickL j1 ∈ blockL_abs enc0 as s j1` 
             `pickL j2 ∈ blockL_abs enc0 as s j2` eq
        show False by (simp add: disjoint_iff)
      qed
    qed

    have R_inj: "inj_on pickR {..<length (enumR as s kk)}"
    proof (rule inj_onI)
      fix j1 j2 assume j1: "j1 ∈ {..<length (enumR as s kk)}" 
                   and j2: "j2 ∈ {..<length (enumR as s kk)}"
                   and eq: "pickR j1 = pickR j2"
      from j1 have "pickR j1 ∈ blockR_abs enc0 as s kk j1" 
        using pickR_props by simp
      from j2 have "pickR j2 ∈ blockR_abs enc0 as s kk j2" 
        using pickR_props by simp
      show "j1 = j2"
      proof (rule ccontr)
        assume "j1 ≠ j2"
        hence "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 = {}"
          using blockR_abs_disjoint j1 j2 by auto
        with `pickR j1 ∈ blockR_abs enc0 as s kk j1` 
             `pickR j2 ∈ blockR_abs enc0 as s kk j2` eq
        show False by auto
      qed
    qed

    have LR_disj: "(pickL ` {..<length (enumL as s kk)}) ∩ 
                   (pickR ` {..<length (enumR as s kk)}) = {}"
    proof (rule ccontr)
      assume "(pickL ` {..<length (enumL as s kk)}) ∩ 
              (pickR ` {..<length (enumR as s kk)}) ≠ {}"
      then obtain i where "i ∈ pickL ` {..<length (enumL as s kk)}"
                      and "i ∈ pickR ` {..<length (enumR as s kk)}" by blast
      then obtain jL jR where 
        jL: "jL < length (enumL as s kk)" "i = pickL jL" and
        jR: "jR < length (enumR as s kk)" "i = pickR jR" by blast
      have "i ∈ blockL_abs enc0 as s jL" using pickL_props jL by simp
      have "i ∈ blockR_abs enc0 as s kk jR" using pickR_props jR by simp
      hence "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR ≠ {}"
        using `i ∈ blockL_abs enc0 as s jL` by blast
      moreover have "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        using blockL_abs_blockR_abs_disjoint jL jR by blast
      ultimately show False by auto
    qed

    from card_Un_disjoint[OF _ _ LR_disj] L_inj R_inj
    show ?thesis unfolding picked_def by (simp add: card_image)
  qed

  moreover have "picked ⊆ Base.read0 M (enc as s kk)"
    unfolding picked_def using pickL_props pickR_props by auto

  ultimately show ?thesis
    using card_mono[of "Base.read0 M (enc as s kk)" picked]
    by (simp add: finite_subset)
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
  shows "steps M (enc as s kk) ≥ card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  have "card (Base.read0 M (enc as s kk)) ≥ 
        length (enumL as s kk) + length (enumR as s kk)"
    using coverage_blocks[OF n_def le dss SOL kk_pos] .
  
  also have "length (enumL as s kk) = card (LHS (e_k as s kk) n)"
    by (simp add: enumL_def n_def)
  
  also have "length (enumR as s kk) = card (RHS (e_k as s kk) n)"
    by (simp add: enumR_def n_def)
  
  finally have "card (Base.read0 M (enc as s kk)) ≥ 
                card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)" .
  
  moreover have "card (Base.read0 M (enc as s kk)) ≤ steps M (enc as s kk)"
    by (rule Base.card_read0_le_steps)
  
  ultimately show ?thesis by linarith
qed

end  (* context Coverage_TM *)

end  (* theory *)
