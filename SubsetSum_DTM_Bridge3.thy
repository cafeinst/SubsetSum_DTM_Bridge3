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

lemma read0_hits_L:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
      and jL:    "j < length (enumL as s kk)"
      and kkpos: "kk > 0"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockL_abs enc0 as s j)"
  hence DISJ: "Base.read0 M ?x ∩ blockL_abs enc0 as s j = {}" by auto

  (* 1) From DSS, get one hit and one miss between L and R, and deduce |enumL| ≥ 2 *)
  (* hit: there exists a value that appears in both LHS and RHS *)
  have hit: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
    using DSS_hit[OF le dss SOL] enumL_set enumR_set by blast

(* produce two distinct LHS values, then miss: an LHS value not in RHS *)
  have twoL: "∃u v. u ∈ LHS (e_k as s kk) (length as)
                 ∧ v ∈ LHS (e_k as s kk) (length as) ∧ u ≠ v"
    by (rule twoL_witness[OF le dss kkpos])

  have miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
    using DSS_miss[OF le dss twoL] enumL_set by auto

  have L2: "2 ≤ length (enumL as s kk)"
  proof -
    obtain vH where vH_L: "vH ∈ set (enumL as s kk)"
                 and vH_R: "vH ∈ set (enumR as s kk)" using hit by blast
    obtain vM where vM_L: "vM ∈ set (enumL as s kk)"
                 and vM_notR: "vM ∉ set (enumR as s kk)" using miss by blast
    have "vH ≠ vM" using vH_R vM_notR by auto
    have fin: "finite (set (enumL as s kk))" by simp
    have subs: "{vH, vM} ⊆ set (enumL as s kk)" using vH_L vM_L by auto
    have "card {vH, vM} = 2" using ‹vH ≠ vM› by simp
    hence "2 ≤ card (set (enumL as s kk))"
      using card_mono[OF fin subs] by simp
    also have "… ≤ length (enumL as s kk)" by (rule card_length)
    finally show ?thesis .
  qed

  (* 2) “baseline-unique j0”, packaged as an implication (so we can use it
      without committing to Good(enc,enc) yet).  We still pick a concrete j0. *)
  obtain j0 where j0L: "j0 < length (enumL as s kk)"
    and base_only_j0:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumL as s kk).
        j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
  proof -
    consider (G) "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
         | (NG) "¬ Good as s ((!) (x0 as s)) ((!) (x0 as s))" by blast
    then show ?thesis
    proof cases
      case G
      then obtain j0 where j0L:
           "j0 < length (enumL as s kk)"
         and uniq:
           "∀j'<length (enumL as s kk).
              j' ≠ j0 ⟶ Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
        using DSS_baseline_only_j_ex[OF le dss G SOL] by blast
      then show ?thesis
        by (intro that) auto
    next
      case NG
    (* pick any valid index; j works since we have jL *)
      show ?thesis
        by (intro that[of j]) (use jL NG in auto)
    qed
  qed

  (* from flipL0 we get: oL' equals x outside the j0-block *)
  obtain oL' where
    OUT0: "⋀i. i ∉ blockL_abs enc0 as s j0 ⟹ oL' i = ((!) ?x) i" and
    FLP:  "Good as s oL' ((!) ?x) ≠ Good as s ((!) ?x) ((!) ?x)"
    using flipL0[OF j0L L2 hit miss base_only_j0] by blast

 (* Build y by splicing the j-th L-block with the oL' bits *)
  define a where "a = length (enc0 as s) + offL as s j"
  define w where "w = W as s"
  have blk_repr: "blockL_abs enc0 as s j = {a ..< a + w}"
    by (simp add: a_def w_def blockL_abs_def offL_def)
  have BND: "a + w ≤ length ?x"
    using offL_window_in_enc[OF jL] by (simp add: a_def w_def)

  define y where
    "y = splice a w ?x (map oL' [a ..< a + w])"

  define oL'' where
    "oL'' i = (if i ∈ blockL_abs enc0 as s j then (!) y i else oL' i)"

  have oL''_outside_j:
      "⋀i. i ∉ blockL_abs enc0 as s j ⟹ oL'' i = oL' i"
    unfolding oL''_def
    by (simp add: ‹oL'' ≡ λi. if i ∈ blockL_abs enc0 as s j then y ! i else oL' i›)

  (* Outside the j-block, y agrees with x *)
  have outside_y:
    "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
  proof -
    fix i assume nin: "i ∉ blockL_abs enc0 as s j"
    from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
    show "y ! i = ?x ! i"
    proof (cases "i < a")
      case True
      thus ?thesis using y_def splice_nth_left BND by simp
    next
      case False
      with nin' have "¬ i < a + w" by simp
      thus ?thesis
        using y_def splice_nth_right w_def BND by simp
    qed
  qed

  (* On the j-block, y’s slice is exactly the oL' slice *)
  have slice_j:
    "map ((!) y) [a ..< a + w] = map oL' [a ..< a + w]"
  proof (rule nth_equalityI)
    show "length (map ((!) y) [a ..< a + w]) =
          length (map oL'      [a ..< a + w])" by simp
  next
    fix t assume tlt: "t < length (map ((!) y) [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    have yn: "y ! (a + t) = (map oL' [a ..< a + w]) ! t"
      using y_def splice_nth_inside inblk by (simp add: BND)
    show "map ((!) y) [a ..< a + w] ! t =
          map oL' [a ..< a + w] ! t"
      by (simp add: idx yn tw)
  qed

  (* Therefore Lval_at on j matches oL' on j *)
  have Lval_y_j: "Lval_at as s ((!) y) j = Lval_at as s oL' j"
    using Lval_at_def a_def w_def slice_j by presburger

  (* For any other j', both y and oL' coincide with x on that block *)
  have Lval_eq_all_off:
  "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹ j' ≠ j0 ⟹
        Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
  proof -
    fix j' assume j'L: "j' < length (enumL as s kk)"
    assume ne:  "j' ≠ j"
    assume ne0: "j' ≠ j0"
    define a' where "a' = length (enc0 as s) + offL as s j'"
    define w' where "w' = W as s"
    have blkj': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
      by (simp add: a'_def w'_def blockL_abs_def offL_def)

    have disj:
      "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j = {}"
      using ne by (simp add: blockL_abs_disjoint)

    have disj0:
      "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j0 = {}"
      using ne0 by (simp add: blockL_abs_disjoint)

  (* y matches x on j'-block (since j' ≠ j) *)
    have slice_y_x:
      "map ((!) y) [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
    proof (rule slice_eq_of_pointwise_outside)
      fix i assume "i ∈ {a' ..< a' + w'}"
      then have "i ∈ blockL_abs enc0 as s j'" by (simp add: blkj')
      hence "i ∉ blockL_abs enc0 as s j" using disj by auto
      thus "(!) y i = (!) ?x i" using outside_y by simp
    qed

  (* oL' matches x on j'-block (since j' ≠ j0) *)
    have slice_oL'_x:
      "map oL' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
    proof (rule slice_eq_of_pointwise_outside)
      fix i assume "i ∈ {a' ..< a' + w'}"
      then have "i ∈ blockL_abs enc0 as s j'" by (simp add: blkj')
      hence "i ∉ blockL_abs enc0 as s j0" using disj0 by auto
      thus "oL' i = ((!) ?x) i" by (rule OUT0)
    qed

    show "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
      by (simp add: Lval_eq_of_slice_eq[OF slice_y_x, unfolded a'_def w'_def]
                  Lval_eq_of_slice_eq[OF slice_oL'_x, unfolded a'_def w'_def])
  qed

  have Lval_y_eq_oL''_at_j:
    "Lval_at as s ((!) y) j = Lval_at as s oL'' j"
  proof -
    define a where "a = length (enc0 as s) + offL as s j"
    define w where "w = W as s"
    have blk: "blockL_abs enc0 as s j = {a ..< a + w}"
      by (simp add: a_def w_def blockL_abs_def offL_def)
    have slice:
      "map ((!) y) [a ..< a + w] = map oL'' [a ..< a + w]"
    proof (rule nth_equalityI)
      show "length (map ((!) y) [a ..< a + w]) = length (map oL'' [a ..< a + w])" by simp
    next
      fix t assume "t < length (map ((!) y) [a ..< a + w])"
      hence tw: "t < w" by simp
      have idx: "[a ..< a + w] ! t = a + t" using tw by simp
      have "a + t ∈ blockL_abs enc0 as s j" by (simp add: blk tw)
      hence "map ((!) y) [a ..< a + w] ! t
          = map oL'' [a ..< a + w] ! t"
        using idx tw oL''_def ‹oL'' ≡ λi. if i ∈ blockL_abs enc0 as s j 
              then y ! i else oL' i› by force
      thus "map ((!) y) [a ..< a + w] ! t = map oL'' [a ..< a + w] ! t" .
    qed
    show ?thesis
      using Lval_at_def a_def w_def slice by presburger
  qed

(* for any other block j' ≠ j, Lval_at agrees between oL'' and oL' *)
  have Lval_oL''_oL'_off_j:
    "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹
        Lval_at as s oL'' j' = Lval_at as s oL' j'"
  proof -
    fix j' assume j'L: "j' < length (enumL as s kk)" and ne: "j' ≠ j"
    define a' where "a' = length (enc0 as s) + offL as s j'"
    define w' where "w' = W as s"
    have blkj': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
      by (simp add: a'_def w'_def blockL_abs_def offL_def)
    have disj: "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j = {}"
      using ne by (simp add: blockL_abs_disjoint)
    have slice:
      "map oL'' [a' ..< a' + w'] = map oL' [a' ..< a' + w']"
    proof (rule nth_equalityI)
      show "length (map oL'' [a' ..< a' + w']) = length (map oL' [a' ..< a' + w'])" by simp
    next
      fix t assume "t < length (map oL'' [a' ..< a' + w'])"
      hence tw: "t < w'" by (simp add: w'_def)
      have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
      have mem: "a' + t ∈ blockL_abs enc0 as s j'" by (simp add: blkj' tw)
      hence nin: "a' + t ∉ blockL_abs enc0 as s j" using disj by blast
      show "map oL'' [a' ..< a' + w'] ! t = map oL' [a' ..< a' + w'] ! t"
        using idx tw oL''_def nin by (simp add: oL''_outside_j)
    qed
    show "Lval_at as s oL'' j' = Lval_at as s oL' j'"
      by (simp add: Lval_eq_of_slice_eq[OF slice, unfolded a'_def w'_def])
  qed

(* equality of L-values for all blocks except j0 *)
  have Lvals_y_eq_oL''_off_j0:
    "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j0 ⟹
        Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
  proof -
    fix j' assume j'L: "j' < length (enumL as s kk)" and ne0: "j' ≠ j0"
    consider (J) "j' = j" | (OFF) "j' ≠ j ∧ j' ≠ j0" using ne0 by auto
    then show "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
    proof cases
      case J
    (* equality on the flipped block j, proved earlier *)
      show ?thesis by (simp add: Lval_y_eq_oL''_at_j J)
    next
      case OFF
      then have nej: "j' ≠ j" and ne0': "j' ≠ j0" by auto
      have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (rule Lval_eq_all_off[OF j'L nej ne0'])
      have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        by (rule Lval_oL''_oL'_off_j[OF j'L nej])
      from Ay Ao show ?thesis by simp
    qed
  qed

  (* off–blocks helper: when j' is neither j nor j0 *)
  have Lval_eq_off:
    "⟦ j' < length (enumL as s kk); j' ≠ j; j' ≠ j0 ⟧
     ⟹ Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
  for j'
  proof -
    assume j'L: "j' < length (enumL as s kk)"
    assume nej: "j' ≠ j"
    assume ne0: "j' ≠ j0"
    have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
      by (rule Lval_eq_all_off[OF j'L nej ne0])
    have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
      by (rule Lval_oL''_oL'_off_j[OF j'L nej])
    from Ay Ao show "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'" by simp
  qed

  have Lval_oL''_eq_y_at_j:
    "Lval_at as s oL'' j = Lval_at as s ((!) y) j"
    using Lval_y_eq_oL''_at_j by simp

  (* the equivalence we need *)
  have lev_equiv:
    "(∃j'<length (enumL as s kk). Lval_at as s ((!) y)  j' ∈ set (enumR as s kk)) =
     (∃j'<length (enumL as s kk). Lval_at as s oL''    j' ∈ set (enumR as s kk))"
    if MISSy: "Lval_at as s ((!) y) j0 ∉ set (enumR as s kk)"
     and MISSo: "Lval_at as s oL''    j0 ∉ set (enumR as s kk)"
  proof
    assume H: "∃j'<length (enumL as s kk). Lval_at as s ((!) y) j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                    and Hy:  "Lval_at as s ((!) y) j' ∈ set (enumR as s kk)" by blast
    consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
    then show "∃j'<length (enumL as s kk). Lval_at as s oL'' j' ∈ set (enumR as s kk)"
    proof cases
      case J
      have "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
        using J Lval_y_eq_oL''_at_j by simp
      with Hy j'L show ?thesis by auto
    next
      case J0
      with MISSy Hy show ?thesis by simp
    next
      case OFF
      from OFF have nej: "j' ≠ j" and ne0: "j' ≠ j0" by auto
      have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (simp add: Lval_eq_all_off j'L nej ne0)
      have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        by (simp add: Lval_oL''_oL'_off_j j'L nej)
      from Hy Ay Ao have "Lval_at as s oL'' j' ∈ set (enumR as s kk)" by simp
      with j'L show ?thesis by blast
    qed
  next
    assume H: "∃j'<length (enumL as s kk). Lval_at as s oL'' j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                      and Ho:  "Lval_at as s oL'' j' ∈ set (enumR as s kk)" by blast
    consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
    then show "∃j'<length (enumL as s kk). Lval_at as s ((!) y) j' ∈ set (enumR as s kk)"
    proof cases
      case J
      have "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
        using J Lval_y_eq_oL''_at_j by simp
      with Ho j'L show ?thesis by auto
    next
      case J0
      with MISSo Ho show ?thesis by simp
    next
      case OFF
      from OFF have nej: "j' ≠ j" and ne0: "j' ≠ j0" by auto
      have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        by (simp add: Lval_oL''_oL'_off_j j'L nej)
      have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (simp add: Lval_eq_all_off j'L nej ne0)
      from Ho Ao Ay have "Lval_at as s ((!) y) j' ∈ set (enumR as s kk)" by simp
      with j'L show ?thesis by blast
    qed
  qed

  (* OFF premise for all other L-blocks (already proved above) *)
  have OFFj:
    "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹
          Lval_at as s oL'' j' = Lval_at as s oL' j'"
    by (rule Lval_oL''_oL'_off_j)

  (* AT premise on the flipped block j: oL'' and oL' give same Lval *)
  have ATj: "Lval_at as s oL'' j = Lval_at as s oL' j"
    using Lval_y_eq_oL''_at_j Lval_y_j by simp

  (* Bridge at j: no need to relate j0 and j anymore *)
  have Good_oL''_oL'_eq:
    "Good as s oL'' ((!) ?x) = Good as s oL' ((!) ?x)"
  proof -
    have jL': "j < length (enumL as s kk)" by (rule jL)
    from bridge_oLpp_param[of j, OF jL' OFFj ATj] show ?thesis .
  qed

(* equality of L-values for all blocks except j0 *)
  have Lvals_y_eq_oL''_off_j0:
    "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j0 ⟹
        Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
  proof -
    fix j' assume j'L: "j' < length (enumL as s kk)" and ne0: "j' ≠ j0"
    consider (J) "j' = j" | (OFF) "j' ≠ j ∧ j' ≠ j0" using ne0 by blast
    then show "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
    proof cases
      case J
      then show ?thesis by (simp add: Lval_y_eq_oL''_at_j)
    next
      case OFF
      then have nej: "j' ≠ j" and ne0': "j' ≠ j0" by auto
      have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (rule Lval_eq_all_off[OF j'L nej ne0'])
      have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        by (rule Lval_oL''_oL'_off_j[OF j'L nej])
      from Ay Ao show ?thesis by simp
    qed
  qed

(* existential equivalence guarded by “miss at j0” on both sides *)
  have ex_equiv:
    "(∃j'<length (enumL as s kk).
      Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)) ⟷
      (∃j'<length (enumL as s kk).
      Lval_at as s oL''   j' ∈ RHS (e_k as s kk) (length as))"
    if MISSy: "Lval_at as s ((!) y) j0 ∉ RHS (e_k as s kk) (length as)"
      and MISSo: "Lval_at as s oL''   j0 ∉ RHS (e_k as s kk) (length as)"
    proof
      assume "∃j'<length (enumL as s kk).
           Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)"
      then obtain j' where j'L: "j' < length (enumL as s kk)"
                    and Hy: "Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)"
        by blast
      consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
      then show "∃j'<length (enumL as s kk).
             Lval_at as s oL'' j' ∈ RHS (e_k as s kk) (length as)"
      proof cases
        case J
        have "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
          using J Lval_y_eq_oL''_at_j by simp
        with Hy j'L show ?thesis by metis
      next
        case J0
        with MISSy Hy show ?thesis by simp
      next
        case OFF
        from OFF have nej: "j' ≠ j" and ne0: "j' ≠ j0" by auto
        have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
          by (simp add: Lval_eq_all_off j'L nej ne0)
        have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
          by (simp add: Lval_oL''_oL'_off_j j'L nej)
        from Hy Ay Ao have "Lval_at as s oL'' j' ∈ RHS (e_k as s kk) (length as)" by simp
        with j'L show ?thesis by blast
      qed
    next
      assume "∃j'<length (enumL as s kk).
           Lval_at as s oL'' j' ∈ RHS (e_k as s kk) (length as)"
      then obtain j' where j'L: "j' < length (enumL as s kk)"
                    and Ho: "Lval_at as s oL'' j' ∈ RHS (e_k as s kk) (length as)"
        by blast
      consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
      then show "∃j'<length (enumL as s kk).
             Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)"
    proof cases
      case J
      have "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
       using J Lval_y_eq_oL''_at_j by simp
      with Ho j'L show ?thesis by metis
    next
      case J0
      with MISSo Ho show ?thesis by simp
    next
      case OFF
      from OFF have nej: "j' ≠ j" and ne0: "j' ≠ j0" by auto
      have Ao: "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        by (simp add: Lval_oL''_oL'_off_j j'L nej)
      have Ay: "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (simp add: Lval_eq_all_off j'L nej ne0)
      from Ho Ao Ay have "Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)" by simp
      with j'L show ?thesis by blast
    qed
  qed

(* now the Good equality is immediate *)
  have Good_y_oL''_eq:
    "Good as s ((!) y) ((!) (enc as s kk)) =
     Good as s oL''    ((!) (enc as s kk))"
      if MISSy: "Lval_at as s ((!) y) j0 ∉ RHS (e_k as s kk) (length as)"
        and MISSo: "Lval_at as s oL''   j0 ∉ RHS (e_k as s kk) (length as)"
  proof -
    have EX:
      "(∃j'<length (enumL as s kk).
        Lval_at as s ((!) y) j' ∈ RHS (e_k as s kk) (length as)) =
      (∃j'<length (enumL as s kk).
        Lval_at as s oL''    j' ∈ RHS (e_k as s kk) (length as))"
      by (rule ex_equiv[OF MISSy MISSo])
    show ?thesis
      unfolding Good_char_encR
      using EX enumR_set Good_char_encR by force
  qed

  have Good_y_oL'_eq:
    "Good as s ((!) y) ((!) ?x) = Good as s oL' ((!) ?x)"
    if MISSy: "Lval_at as s ((!) y) j0 ∉ RHS (e_k as s kk) (length as)"
      and MISSo: "Lval_at as s oL''   j0 ∉ RHS (e_k as s kk) (length as)"
  proof -
    from Good_y_oL''_eq[OF MISSy MISSo] Good_oL''_oL'_eq
    show ?thesis by simp
  qed

  have seenL_sub:
    "seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenL_T0_subset_read0[OF refl])
  have seenR_sub:
    "seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0[OF refl])

  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) y i"
  proof -
    fix i assume "i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s)"
    hence "i ∈ Base.read0 M ?x" using seenL_sub by blast
    with DISJ have "i ∉ blockL_abs enc0 as s j" by auto
    thus "(!) ?x i = (!) y i" using outside_y by simp
  qed

  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) ?x i"
    by simp

  have RUN_EQ:
    "run ((!) ?x) ((!) ?x) (T0 as s) = run ((!) y) ((!) ?x) (T0 as s)"
    by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])

(* First, lift RUN_EQ (which is for T0) up to T *)
  have RUN_EQ_T:
    "run ((!) y)  ((!) ?x) (T as s) =
    run ((!) ?x) ((!) ?x) (T as s)"
  proof -
    have "run ((!) y) ((!) ?x) (T as s)
        = run ((!) y) ((!) ?x) (T0 as s)"
      by (rule correct_T0_run_bridge[symmetric])
    also have "... = run ((!) ?x) ((!) ?x) (T0 as s)"
      using RUN_EQ by simp
    also have "... = run ((!) ?x) ((!) ?x) (T as s)"
      by (rule correct_T0_run_bridge)
    finally show ?thesis .
  qed

  (* replace the whole EX_EQ proof block with this *)
  have EX_EQ:
    "(∃j'<length (enumL as s kk). Lval_at as s ((!) y) j' ∈ set (enumR as s kk)) ⟷
     (∃j'<length (enumL as s kk). Lval_at as s ((!) ?x) j' ∈ set (enumR as s kk))"
  proof
  (* → direction: y-hit ⇒ enc-hit *)
    assume Hy: "∃j'<length (enumL as s kk). Lval_at as s ((!) y) j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                  and HitY: "Lval_at as s ((!) y) j' ∈ set (enumR as s kk)"
      by blast
    consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
    then show "∃j''<length (enumL as s kk). Lval_at as s ((!) ?x) j'' ∈ set (enumR as s kk)"
    proof cases
      case J
    (* On the flipped block j: y ↔ oL'' ↔ oL' and relate oL' to enc on j *)
      have Yeq:  "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
        using J Lval_y_eq_oL''_at_j by simp
      have OeqO': "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        using J ATj by simp
      have OeqX: "Lval_at as s oL' j' = Lval_at as s ((!) ?x) j'"
      proof (cases "j = j0")
        case False
        define a where "a = length (enc0 as s) + offL as s j"
        define w where "w = W as s"
        have blkj: "blockL_abs enc0 as s j = {a ..< a + w}"
          by (simp add: a_def w_def blockL_abs_def offL_def)
        have slice_oL'_x_j:
          "map oL' [a ..< a + w] = map ((!) ?x) [a ..< a + w]"
        proof (rule slice_eq_of_pointwise_outside)
          fix i assume "i ∈ {a ..< a + w}"
          then have "i ∈ blockL_abs enc0 as s j" by (simp add: blkj)
          moreover from False have "blockL_abs enc0 as s j ∩ blockL_abs enc0 as s j0 = {}"
            by (simp add: blockL_abs_disjoint)
          ultimately have "i ∉ blockL_abs enc0 as s j0" by blast
          thus "oL' i = (!) ?x i" by (rule OUT0)
        qed
        show ?thesis by (simp add: Lval_eq_of_slice_eq[OF slice_oL'_x_j] a_def w_def J)
      next
        case True
      (* when j = j0, relate x and y directly on j via the already proved equalities *)
        have "Lval_at as s ((!) ?x) j = Lval_at as s ((!) y) j"
          using True Lval_oL''_eq_y_at_j Lval_y_eq_oL''_at_j
          by (metis FLP Good_char_encR HitY J Lval_at_on_enc_block Lval_y_j hit 
              in_set_conv_nth jL x0_is_enc)
        thus ?thesis using True J Lval_y_j by simp
      qed
      from HitY Yeq OeqO' OeqX
      have "Lval_at as s ((!) ?x) j' ∈ set (enumR as s kk)" by simp
      with j'L show ?thesis by blast
    next
      case J0
    (* On j0: either it coincides with j, or it's off the flipped block *)
      show ?thesis
      proof (cases "j = j0")
        case True
        with J0 have JJ: "j' = j" by simp
        have "Lval_at as s ((!) ?x) j' = Lval_at as s ((!) y) j'"
          using True JJ Lval_oL''_eq_y_at_j Lval_y_eq_oL''_at_j
          by (metis FLP Good_char_encR HitY Lval_at_on_enc_block Lval_y_j 
              hit in_set_conv_nth jL x0_is_enc)
        with HitY j'L show ?thesis by metis
      next
        case False
        from J0 False have "j' ≠ j" by auto
        define a' where "a' = length (enc0 as s) + offL as s j'"
        define w' where "w' = W as s"
        have blkj': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
          by (simp add: a'_def w'_def blockL_abs_def offL_def)
        have slice_y_x_j':
          "map ((!) y) [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
        proof (rule slice_eq_of_pointwise_outside)
          fix i assume "i ∈ {a' ..< a' + w'}"
          then have "i ∈ blockL_abs enc0 as s j'" by (simp add: blkj')
          moreover have "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j = {}"
            using ‹j' ≠ j› by (simp add: blockL_abs_disjoint)
          ultimately have "i ∉ blockL_abs enc0 as s j" by blast
          thus "(!) y i = (!) ?x i" by (rule outside_y)
        qed
        have YeqX: "Lval_at as s ((!) y) j' = Lval_at as s ((!) ?x) j'"
          by (simp add: Lval_eq_of_slice_eq[OF slice_y_x_j'] a'_def w'_def)
        from HitY YeqX j'L show ?thesis by metis
      qed
    next
      case OFF
    (* Off both j and j0: y ↔ oL' and enc ↔ oL' *)
      have YeqO': "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (simp add: Lval_eq_all_off OFF j'L)
      define a' where "a' = length (enc0 as s) + offL as s j'"
      define w' where "w' = W as s"
      have blkj': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
        by (simp add: a'_def w'_def blockL_abs_def offL_def)
      have slice_oL'_x_j':
        "map oL' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule slice_eq_of_pointwise_outside)
        fix i assume "i ∈ {a' ..< a' + w'}"
        then have "i ∈ blockL_abs enc0 as s j'" by (simp add: blkj')
        moreover have "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j0 = {}"
          using OFF by (simp add: blockL_abs_disjoint)
        ultimately have "i ∉ blockL_abs enc0 as s j0" by blast
        thus "oL' i = (!) ?x i" by (rule OUT0)
      qed
      have OeqX': "Lval_at as s oL' j' = Lval_at as s ((!) ?x) j'"
        by (simp add: Lval_eq_of_slice_eq[OF slice_oL'_x_j'] a'_def w'_def)
      from HitY YeqO' OeqX' j'L show ?thesis by metis
    qed
  next
  (* ← direction: enc-hit ⇒ y-hit *)
    assume Hx: "∃j'<length (enumL as s kk). Lval_at as s ((!) ?x) j' ∈ set (enumR as s kk)"
    then obtain j' where j'L: "j' < length (enumL as s kk)"
                  and HitX: "Lval_at as s ((!) ?x) j' ∈ set (enumR as s kk)"
      by blast
    consider (J) "j' = j" | (J0) "j' = j0" | (OFF) "j' ≠ j ∧ j' ≠ j0" by blast
    then show "∃j''<length (enumL as s kk). Lval_at as s ((!) y) j'' ∈ set (enumR as s kk)"
    proof cases
      case J
(* We need to show the existential for y (or for x, depending on direction).
   Do a sub-case split on whether the flipped block is the baseline block. *)
      show ?thesis
      proof (cases "j = j0")
        case False
  (* Here we *can* relate oL' and x on block j, so use the slice argument. *)
        define a where "a = length (enc0 as s) + offL as s j"
        define w where "w = W as s"
        have blkj: "blockL_abs enc0 as s j = {a ..< a + w}"
          by (simp add: a_def w_def blockL_abs_def offL_def)
        have slice_oL'_x_j:
          "map oL' [a ..< a + w] = map ((!) ?x) [a ..< a + w]"
        proof (rule slice_eq_of_pointwise_outside)
          fix i assume "i ∈ {a ..< a + w}"
          then have "i ∈ blockL_abs enc0 as s j" by (simp add: blkj)
          moreover from False
          have "blockL_abs enc0 as s j ∩ blockL_abs enc0 as s j0 = {}"
            by (simp add: blockL_abs_disjoint)
          ultimately have "i ∉ blockL_abs enc0 as s j0" by blast
          thus "oL' i = (!) ?x i" by (rule OUT0)
        qed
        have OeqX: "Lval_at as s oL' j = Lval_at as s ((!) ?x) j"
          by (simp add: Lval_eq_of_slice_eq[OF slice_oL'_x_j] a_def w_def)
        have OeqO': "Lval_at as s oL'' j = Lval_at as s oL' j" using ATj by simp
        have Yeq:   "Lval_at as s ((!) y) j = Lval_at as s oL'' j"
          by (simp add: Lval_y_eq_oL''_at_j)
  (* Chain the equalities and carry the hit/existential on index j *)
        from HitX OeqX OeqO' Yeq
        have "Lval_at as s ((!) y) j ∈ set (enumR as s kk)"
          using J by argo
        with j'L show ?thesis
          using jL by auto
      next
        case True
        have Genc: "Good as s ((!) ?x) ((!) ?x)"
          using HitX Good_char_encR[of as s "(!) ?x"] Hx by auto
        have Geq: "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
          by (simp add: Good_def RUN_EQ_T)
        have Gy: "Good as s ((!) y) ((!) ?x)"
          using Genc Geq by simp
        show ?thesis
          using Gy Good_char_encR[of as s "(!) y"] by auto
      qed
      have OeqO' : "Lval_at as s oL'' j' = Lval_at as s oL' j'"
        using J ATj by simp
      have Yeq   : "Lval_at as s ((!) y) j' = Lval_at as s oL'' j'"
        using J Lval_y_eq_oL''_at_j by simp
      from HitX OeqX OeqO' Yeq j'L show ?thesis by simp
    next
      case J0
      have "j' ≠ j" using J0 by (cases "j=j0") auto
      have YeqX: "Lval_at as s ((!) y) j' = Lval_at as s ((!) ?x) j'"
        by (simp add: Lval_eq_all_off j'L ‹j' ≠ j› J0)
      from HitX YeqX j'L show ?thesis by metis
    next
      case OFF
      define a' where "a' = length (enc0 as s) + offL as s j'"
      define w' where "w' = W as s"
      have blkj': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
        by (simp add: a'_def w'_def blockL_abs_def offL_def)
      have slice_oL'_x_j':
        "map oL' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule slice_eq_of_pointwise_outside)
        fix i assume "i ∈ {a' ..< a' + w'}"
        then have "i ∈ blockL_abs enc0 as s j'" by (simp add: blkj')
        moreover have "blockL_abs enc0 as s j' ∩ blockL_abs enc0 as s j0 = {}"
          using OFF by (simp add: blockL_abs_disjoint)
        ultimately have "i ∉ blockL_abs enc0 as s j0" by blast
        thus "oL' i = (!) ?x i" by (rule OUT0)
      qed
      have OeqX': "Lval_at as s oL' j' = Lval_at as s ((!) ?x) j'"
        by (simp add: Lval_eq_of_slice_eq[OF slice_oL'_x_j'] a'_def w'_def)
      have YeqO': "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
        by (simp add: Lval_eq_all_off OFF j'L)
      from HitX OeqX' YeqO' j'L show ?thesis by metis
    qed
  qed

(* 2) Now equate the 'Good' predicates via Good_char_encR + EX_EQ *)
  have Good_eq:
    "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
    using Good_char_encR EX_EQ by simp

(* 3) If you need the lowercase version afterwards, derive it from Good_eq *)
  have good_eq:
    "good as s ((!) y) ((!) ?x) = good as s ((!) ?x) ((!) ?x)"
    using Good_eq Good_def by simp

  (* Final contradiction with the flip lemma *)
  have "Good as s oL' ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
    using Good_y_oL'_eq Good_eq by simp
  with FLP show False by simp
qed

lemma DSS_unique_L_witness:
  assumes le:   "kk ≤ length as"
      and dss:  "distinct_subset_sums as"
      and SOL:  "∃S ⊆ {..<length as}. sum_over as S = s"
      and j'L:  "j' < length (enumL as s kk)"
      and j''L: "j'' < length (enumL as s kk)"
      and inR':  "enumL as s kk ! j'  ∈ RHS (e_k as s kk) (length as)"
      and inR'': "enumL as s kk ! j'' ∈ RHS (e_k as s kk) (length as)"
  shows "j' = j''"
proof -
  have inL':  "enumL as s kk ! j'  ∈ LHS (e_k as s kk) (length as)"
    using j'L enumL_set nth_mem by blast
  have inL'': "enumL as s kk ! j'' ∈ LHS (e_k as s kk) (length as)"
    using j''L enumL_set nth_mem by blast

  obtain v where v_def:
      "v = enumL as s kk ! j'"
    and v_unique:
      "∀w. (w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as)) ⟶ w = v"
    using DSS_unique_value[OF le dss SOL] inL' inR'
    by blast

  have "enumL as s kk ! j' = enumL as s kk ! j''"
    using v_unique inL'' inR'' v_def by presburger

  moreover have "distinct (enumL as s kk)" by (simp add: enumL_def)
  ultimately show ?thesis
    using distinct_conv_nth[THEN iffD1] j'L j''L by blast
qed

lemma Run_unread_L:
  fixes x y :: "bool list"
  assumes DISJ:  "Base.read0 M x ∩ blockL_abs enc0 as s j = {}"
  assumes AGREE: "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = x ! i"
  assumes X:     "x = enc as s kk"
  shows "run ((!) y) ((!) x) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
proof -
  (* bound the seen-sets using the pair (x,x) so they sit inside read0 M x *)
  have SLsub: "seenL_run ((!) x) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenL_T0_subset_read0[OF X])
  have SRsub: "seenR_run ((!) x) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenR_T0_subset_read0[OF X])

  (* agree with y on everything seen on the left; right oracles are identical anyway *)
  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) x) ((!) x) (T0 as s) ⟹ (!) x i = (!) y i"
  proof -
    fix i assume "i ∈ seenL_run ((!) x) ((!) x) (T0 as s)"
    with SLsub have "i ∈ Base.read0 M x" by blast
    with DISJ have "i ∉ blockL_abs enc0 as s j" by auto
    with AGREE show "(!) x i = (!) y i" by simp
  qed
  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) x) ((!) x) (T0 as s) ⟹ (!) x i = (!) x i"
    by simp

  (* apply run_agrees_on_seen with (oL,oR)=((!) x, (! ) x) and (oL',oR')=((!) y, (! ) x) *)
  have "run ((!) x) ((!) x) (T0 as s) = run ((!) y) ((!) x) (T0 as s)"
    by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])
  thus ?thesis by simp
qed

(* -- R blocks are touched --------------------------------------------------- *)
lemma read0_hits_R:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
      and jR:    "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockR_abs enc0 as s kk j)"
  hence DISJ: "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}" by auto

  (* 1) From DSS, get one hit and one miss between R and L, and deduce |enumR| ≥ 2 *)
  have hitR:
    "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)"
    using DSS_hit[OF le dss SOL] enumL_set enumR_set by blast

  have missR:
    "∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)"
    using DSS_missR[OF le dss twoR_witness[OF le dss _]] enumL_set enumR_set
    by (cases "kk < length as"; simp_all)

  have R2: "2 ≤ length (enumR as s kk)"
  proof -
    obtain vH where vH_R: "vH ∈ set (enumR as s kk)"
                 and vH_L: "vH ∈ set (enumL as s kk)" using hitR by blast
    obtain vM where vM_R: "vM ∈ set (enumR as s kk)"
                 and vM_notL: "vM ∉ set (enumL as s kk)" using missR by blast
    have "vH ≠ vM" using vH_L vM_notL by auto
    have fin: "finite (set (enumR as s kk))" by simp
    have subs: "{vH, vM} ⊆ set (enumR as s kk)" using vH_R vM_R by auto
    have "card {vH, vM} = 2" using ‹vH ≠ vM› by simp
    hence "2 ≤ card (set (enumR as s kk))" using card_mono[OF fin subs] by simp
    also have "… ≤ length (enumR as s kk)" by (rule card_length)
    finally show ?thesis .
  qed

  (* 2) The “baseline-unique j” condition on the R side *)
  have baseline_only_jR:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumR as s kk). j' ≠ j ⟶
        Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
    by (rule DSS_baseline_only_jR_ex[OF le dss _ SOL], insert jR, blast)

  (* 3) Flip only this R block while leaving others identical *)
  obtain oR' where
    OUT: "∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = ((!) ?x) i" and
    FLP: "Good as s ((!) ?x) oR' ≠ Good as s ((!) ?x) ((!) ?x)"
    using DSS_baseline_only_jR Good_char_encR Lval_at_on_enc_block 
        Rval_at_on_enc_block dss hitR in_set_conv_nth missR by metis

  (* Build y by splicing the j-th R-block with the oR' bits *)
  define a where "a = offR as s kk j"
  define w where "w = W as s"
  have blk_repr: "blockR_abs enc0 as s kk j = {a ..< a + w}"
    using a_def w_def blockR_abs_def offR_def DSS_baseline_only_jR Good_char_encR 
     Lval_at_on_enc_block Rval_at_on_enc_block dss hitR in_set_conv_nth missR
     by metis
  have BND: "a + w ≤ length ?x"
    using offR_window_in_enc[OF jR] by (simp add: a_def w_def)
  define y where
    "y = splice a w ?x (map oR' [a ..< a + w])"

  (* Outside the j-block, y agrees with x *)
  have outside_y:
    "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
  proof -
    fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
    from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
    show "y ! i = ?x ! i"
    proof (cases "i < a")
      case True
      thus ?thesis using y_def splice_nth_left BND by simp
    next
      case False
      with nin' have "¬ i < a + w" by simp
      thus ?thesis using y_def splice_nth_right w_def BND by simp
    qed
  qed

  (* On the j-block, y’s slice is exactly the oR' slice *)
  have slice_j:
    "map ((!) y) [a ..< a + w] = map oR' [a ..< a + w]"
  proof (rule nth_equalityI)
    show "length (map ((!) y) [a ..< a + w]) =
          length (map oR'      [a ..< a + w])" by simp
  next
    fix t assume tlt: "t < length (map ((!) y) [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    have yn: "y ! (a + t) = (map oR' [a ..< a + w]) ! t"
      using y_def splice_nth_inside inblk by (simp add: BND)
    show "map ((!) y) [a ..< a + w] ! t =
          map oR' [a ..< a + w] ! t"
      by (simp add: idx yn tw)
  qed

  (* Therefore Rval_at on j matches oR' on j *)
  have Rval_y_j: "Rval_at as s ((!) y) j = Rval_at as s oR' j"
    using Rval_at_def a_def w_def slice_j DSS_baseline_only_jR 
          Good_char_encL Rval_at_on_enc_block dss hitR in_set_conv_nth missR
    by metis

  (* For any other j', both y and oR' coincide with x on that block *)
  have Rval_eq_all:
    "⋀j'. j' < length (enumR as s kk) ⟹
          Rval_at as s ((!) y) j' = Rval_at as s oR' j'"
  proof -
    fix j' assume j'R: "j' < length (enumR as s kk)"
    consider (eq) "j' = j" | (ne) "j' ≠ j" by blast
    then show "Rval_at as s ((!) y) j' = Rval_at as s oR' j'"
    proof cases
      case eq
      thus ?thesis by (simp add: Rval_y_j)
    next
      case ne
      define a' where "a' = offR as s kk j'"
      define w' where "w' = W as s"
      have blk': "blockR_abs enc0 as s kk j' = {a' ..< a' + w'}"
        using a'_def w'_def blockR_abs_def offR_def DSS_baseline_only_jR 
          Good_char_encL Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by (metis)
      have agree_y_x:
        "map ((!) y)  [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map ((!) y) [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockR_abs enc0 as s kk j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockR_abs enc0 as s kk j"
          using blockR_abs_disjoint[OF ne] mem by blast
        have "map ((!) y) [a' ..< a' + w'] ! t = (!) y (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using outside_y nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map ((!) y) [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have agree_oR_x:
        "map oR' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map oR' [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map oR' [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockR_abs enc0 as s kk j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockR_abs enc0 as s kk j"
          using blockR_abs_disjoint[OF ne] mem by blast
        have "map oR' [a' ..< a' + w'] ! t = oR' (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using OUT nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map oR' [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have "Rval_at as s ((!) y) j'
            = from_bits (map ((!) y) [a' ..< a' + w'])"
        using Rval_at_def a'_def w'_def DSS_baseline_only_jR Good_char_encL 
              Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by metis
      also have "... = from_bits (map ((!) ?x) [a' ..< a' + w'])"
        by (simp add: agree_y_x)
      also have "... = from_bits (map oR' [a' ..< a' + w'])"
        by (simp add: agree_oR_x)
      also have "... = Rval_at as s oR' j'"
        using Rval_at_def a'_def w'_def DSS_baseline_only_jR Good_char_encL 
              Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by metis 
      finally show ?thesis .
    qed
  qed

  (* With L fixed to enc, Good(enc,y) = Good(enc,oR') *)
  have Good_y_oR'_eq:
    "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) oR'"
  proof -
    have "Good as s ((!) ?x) ((!) y)
          ⟷ (∃j'<length (enumR as s kk). Rval_at as s ((!) y) j' ∈ set (enumL as s kk))"
      using Good_char_encL by simp
    also have "... ⟷ (∃j'<length (enumR as s kk). Rval_at as s oR' j' ∈ set (enumL as s kk))"
      by (metis Rval_eq_all)
    also have "... ⟷ Good as s ((!) ?x) oR'"
      using Good_char_encL[symmetric] by simp
    finally show ?thesis .
  qed

  from Good_y_oR'_eq FLP have
    "Good as s ((!) ?x) ((!) y) ≠ Good as s ((!) ?x) ((!) ?x)" by simp

  (* Changing only inside the R-block j cannot change the run of T0 *)
  have seenL_sub:
    "seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenL_T0_subset_read0[OF refl])
  have seenR_sub:
    "seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0[OF refl])

  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) y i"
  proof -
    fix i assume "i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s)"
    hence "i ∈ Base.read0 M ?x" using seenR_sub by blast
    with DISJ have "i ∉ blockR_abs enc0 as s kk j" by auto
    thus "(!) ?x i = (!) y i" using outside_y by simp
  qed

  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) ?x i" by simp

  have RUN_EQ:
    "run ((!) ?x) ((!) ?x) (T0 as s) = run ((!) ?x) ((!) y) (T0 as s)"
    by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])

  (* Tie run to Good via correctness of T0 only on the baseline side *)
  have Good_eq_baseline:
    "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
  proof -
    have "run ((!) ?x) ((!) y) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
      using RUN_EQ[symmetric] by simp
    moreover have "run ((!) ?x) ((!) ?x) (T0 as s)
                 = Good as s ((!) ?x) ((!) ?x)"
      by (simp add: correct_T0)
    ultimately show ?thesis
      using Good_char_encL Rval_eq_all
      by (metis DSS_baseline_only_jR Rval_at_on_enc_block dss hitR in_set_conv_nth missR)
  qed

  (* Contradiction to FLP *)
  from Good_y_oR'_eq Good_eq_baseline have
    "Good as s ((!) ?x) oR' = Good as s ((!) ?x) ((!) ?x)" by simp
  with FLP show False by simp
qed

(* 9) The coverage result you wanted, phrased on block families *)
lemma coverage_blocks:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and dss:   "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
    (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  fix j assume jL: "j < length (enumL as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
    by (rule read0_hits_L[OF n_def le dss SOL jL])
  thus "touches (enc as s kk) (blockL_abs enc0 as s j)"
    using touches_def by auto
next
  fix j assume jR: "j < length (enumR as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
    by (rule read0_hits_R[OF n_def le dss SOL jR])
  thus "touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using touches_def by auto
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as"
      and le:    "kk ≤ length as"
      and distinct: "distinct_subset_sums as"
      and SOL:   "∃S ⊆ {..<length as}. sum_over as S = s"
  shows "steps M (enc as s kk) ≥
           card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
   from coverage_blocks[OF n_def le distinct SOL] obtain
    Lcov_ALL: "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)" and
    Rcov_ALL: "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    by blast

  have Lcov:
    "⋀j. j < length (enumL as s kk) ⟹ touches (enc as s kk) (blockL_abs enc0 as s j)"
    using Lcov_ALL by blast
  have Rcov:
    "⋀j. j < length (enumR as s kk) ⟹ touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov_ALL by blast

  define x0 where "x0 = enc as s kk"
  define R0 :: "nat set" where "R0 = Base.read0 M x0"

  define IL where "IL = {0..<length (enumL as s kk)}"
  define IR where "IR = {0..<length (enumR as s kk)}"

  (* pick one read index from each touched absolute block *)
  define pickL where "pickL j = (SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j)" for j
  define pickR where "pickR j = (SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j)" for j

  (* existence: each touched block contributes one read index *)
  have exL:
    "⋀j. j ∈ IL ⟹ ∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    hence jlt: "j < length (enumL as s kk)" by (simp add: IL_def)
    from Lcov[OF jlt] obtain i where
      "i ∈ Base.read0 M (enc as s kk)" "i ∈ blockL_abs enc0 as s j"
      by (auto simp: touches_def)
    hence "i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
      by (simp add: R0_def x0_def)
    thus "∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j" ..
  qed

  have exR:
    "⋀j. j ∈ IR ⟹ ∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    hence jlt: "j < length (enumR as s kk)" by (simp add: IR_def)
    from Rcov[OF jlt] obtain i where
      "i ∈ Base.read0 M (enc as s kk)" "i ∈ blockR_abs enc0 as s kk j"
      by (auto simp: touches_def)
    hence "i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
      by (simp add: R0_def x0_def)
    thus "∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j" ..
  qed

  have pickL_in:
    "⋀j. j ∈ IL ⟹ pickL j ∈ R0"
    "⋀j. j ∈ IL ⟹ pickL j ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    have conj: "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      using exL[OF jIL] unfolding pickL_def by (rule someI_ex)
    thus "pickL j ∈ R0" by (rule conjunct1)
  next
    fix j assume jIL: "j ∈ IL"
    have conj: "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      using exL[OF jIL] unfolding pickL_def by (rule someI_ex)
    thus "pickL j ∈ blockL_abs enc0 as s j" by (rule conjunct2)
  qed

  have pickR_in:
    "⋀j. j ∈ IR ⟹ pickR j ∈ R0"
    "⋀j. j ∈ IR ⟹ pickR j ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    have conj: "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      using exR[OF jIR] unfolding pickR_def by (rule someI_ex)
    thus "pickR j ∈ R0" by (rule conjunct1)
  next
    fix j assume jIR: "j ∈ IR"
    have conj: "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      using exR[OF jIR] unfolding pickR_def by (rule someI_ex)
    thus "pickR j ∈ blockR_abs enc0 as s kk j" by (rule conjunct2)
  qed

  have subL: "pickL ` IL ⊆ R0"
    by (auto dest: pickL_in)

  have subR: "pickR ` IR ⊆ R0"
    by (auto dest: pickR_in)

  have union_sub: "pickL ` IL ∪ pickR ` IR ⊆ R0"
    using subL subR by auto

  have injL: "inj_on pickL IL"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IL" and j2: "j2 ∈ IL" and eq: "pickL j1 = pickL j2"
    have in1: "pickL j1 ∈ blockL_abs enc0 as s j1" using pickL_in[OF j1] by blast
    have in2: "pickL j2 ∈ blockL_abs enc0 as s j2" using pickL_in[OF j2] by blast
    have "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 ≠ {}"
      using eq in1 in2 by auto
    then show "j1 = j2"
      using Int_emptyI blockL_abs_disjoint j1 j2 subsetI
      by meson
  qed

  have injR: "inj_on pickR IR"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IR" and j2: "j2 ∈ IR" and eq: "pickR j1 = pickR j2"
    have in1: "pickR j1 ∈ blockR_abs enc0 as s kk j1" using pickR_in[OF j1] by blast
    have in2: "pickR j2 ∈ blockR_abs enc0 as s kk j2" using pickR_in[OF j2] by blast
    have "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 ≠ {}"
      using eq in1 in2 by auto
    then show "j1 = j2"
      using Int_emptyI blockR_abs_disjoint j1 j2 subsetI 
      by meson
  qed

  have fin_R0:   "finite R0"             by (simp add: R0_def)
  have fin_imgL: "finite (pickL ` IL)"   by (intro finite_imageI) (simp add: IL_def)
  have fin_imgR: "finite (pickR ` IR)"   by (intro finite_imageI) (simp add: IR_def)

  have card_lower: "card (pickL ` IL ∪ pickR ` IR) ≤ card R0"
    by (rule card_mono[OF fin_R0 union_sub])

  have disj_images: "(pickL ` IL) ∩ (pickR ` IR) = {}"
  proof
    show "(pickL ` IL) ∩ (pickR ` IR) ⊆ {}"
    proof
      fix i assume "i ∈ (pickL ` IL) ∩ (pickR ` IR)"
      then obtain jL jR where jL: "jL ∈ IL" "i = pickL jL"
                          and jR: "jR ∈ IR" "i = pickR jR" by blast
      have iL: "i ∈ blockL_abs enc0 as s jL" using jL pickL_in by auto
      have iR: "i ∈ blockR_abs enc0 as s kk jR" using jR pickR_in by auto
      have "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        using blockL_abs_blockR_abs_disjoint[OF _] IL_def jL(1) 
        by simp
      thus "i ∈ {}" using iL iR by auto
    qed
  qed simp

  have card_union:
    "card (pickL ` IL ∪ pickR ` IR) = card (pickL ` IL) + card (pickR ` IR)"
    by (subst card_Un_disjoint) (use disj_images fin_imgL fin_imgR in auto)

  have inj_cardL: "card (pickL ` IL) = card IL" by (rule card_image[OF injL])
  have inj_cardR: "card (pickR ` IR) = card IR" by (rule card_image[OF injR])

  from card_lower card_union inj_cardL inj_cardR
  have A: "card IL + card IR ≤ card R0" by simp

  have card_IL: "card IL = card (LHS (e_k as s kk) n)"
  proof -
    have "card IL = length (enumL as s kk)" by (simp add: IL_def)
    also have "... = card (LHS (e_k as s kk) n)"
      by (simp add: enumL_def n_def)      (* whichever equation you have for enumL *)
    finally show ?thesis .
  qed
  have card_IR: "card IR = card (RHS (e_k as s kk) n)"
  proof -
    have "card IR = length (enumR as s kk)" by (simp add: IR_def)
    also have "... = card (RHS (e_k as s kk) n)"
      by (simp add: enumR_def n_def)      (* likewise for enumR *)
    finally show ?thesis .
  qed

  have B:
   "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ card R0"
    using A by (simp add: card_IL card_IR)

  have "card R0 ≤ steps M x0"
    by (simp add: R0_def Base.card_read0_le_steps)
  from B this have "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ steps M x0"
    by (rule le_trans)
  thus ?thesis
    by (simp add: x0_def)
qed

end  (* context Coverage_TM *)

end  (* theory *)
