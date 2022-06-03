theory reg2nfa 
  imports AReg NFA
begin

section "definition of nondeterministic finite automaton"


fun ConcatRegexp::"'v regexp \<Rightarrow> 'v regexp\<Rightarrow> 'v regexp" where
  "ConcatRegexp r1 r2 = Concat r2 r1"

fun renameDelta1 :: "('v regexp * 'v set * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp *'v set *'v regexp) set" where 
    "renameDelta1 ss f = {(f q,v, f q')| q v q' . (q, v, q')\<in> ss}"

fun renameDelta2 :: "('v regexp * 'v regexp) set \<Rightarrow> ('v regexp => 'v regexp)  \<Rightarrow> ('v regexp  *'v regexp) set" where  
    "renameDelta2 ss f = {(f q, f q')| q q'.(q, q')\<in> ss}"

primrec trans2LTS :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> (('v regexp \<times> 'v set \<times> 'v regexp) set * ('v regexp * 'v regexp) set)" where 
    "trans2LTS (LChr v) alp_set= ({(LChr v,{v},\<epsilon>)},{})"|
    "trans2LTS (ESet) alp_set= ({(ESet,{},\<epsilon>)},{})"|
    "trans2LTS (\<epsilon>) alp_set = ({},{})"|
    "trans2LTS (Dot) alp_set = ({(Dot ,alp_set, \<epsilon>)},{})"|
    "trans2LTS (Concat r1 r2) alp_set =(renameDelta1 (fst (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> (fst (trans2LTS r2 alp_set)),
                                        (renameDelta2 (snd (trans2LTS r1 alp_set)) (ConcatRegexp r2) \<union> {(Concat r1 r2, Concat r1 r2),(Concat \<epsilon> r2, r2)}  \<union> snd (trans2LTS r2 alp_set)))"|
    "trans2LTS (Alter r1 r2) alp_set = (fst (trans2LTS r1 alp_set) \<union> fst (trans2LTS r2 alp_set), 
                                        snd (trans2LTS r1 alp_set) \<union> snd (trans2LTS r2 alp_set) \<union> {(Alter r1 r2, r1),(Alter r1 r2, r2),(Alter r1 r2, Alter r1 r2)})"|
    "trans2LTS (Star r) alp_set = (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)) \<union> fst (trans2LTS r alp_set), 
                                   (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> {(Star r, \<epsilon>),(Star r,Concat r (Star r))})"|
    "trans2LTS (Plus r) alp_set = (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)) \<union> (fst  (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)), 
                                   (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> {(Star r, \<epsilon>),(Star r,Concat r (Star r))})),
                                        (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r)) \<union> {(Concat r (Star r), Concat r (Star r)),(Concat \<epsilon> (Star r), Star r)}  \<union> snd (renameDelta1 (fst (trans2LTS r alp_set)) (ConcatRegexp (Star r)), 
                                   (renameDelta2 (snd (trans2LTS r alp_set)) (ConcatRegexp (Star r))) \<union> {(Star r, \<epsilon>),(Star r,Concat r (Star r))})))"|
    "trans2LTS (Ques r) alp_set = (fst (trans2LTS r alp_set),
                                   {(Ques r,\<epsilon>), (Ques r, r),(Ques r, Ques r)} \<union> snd (trans2LTS r alp_set))"

primrec reg2q :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v regexp) set" where
    "reg2q Dot a = {Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {(LChr p), \<epsilon>}"|
    "reg2q (Alter r1 r2) a = {(Alter r1 r2),\<epsilon>} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = {\<epsilon>, Star r} \<union> reg2q r a \<union> (\<lambda>x. ConcatRegexp x (Star r)) ` (reg2q r a)" |
    "reg2q (Plus r) a =  {Plus r, \<epsilon>} \<union> {Concat r (Star r), (Concat \<epsilon> (Star r))} \<union> {Star r} \<union> reg2q r a \<union> (\<lambda>x. ConcatRegexp x (Star r)) ` (reg2q r a)" |
    "reg2q (Ques r) a = {(Ques r), \<epsilon>} \<union> reg2q r a" |
    "reg2q ESet a = {ESet, \<epsilon>}"|
    "reg2q \<epsilon> a = {\<epsilon>}"|
    "reg2q (Concat r1 r2) a = {Concat r1 r2, r2, \<epsilon>, (Concat \<epsilon> r2)}"

fun reg2nfa :: "'v regexp \<Rightarrow> 'v set\<Rightarrow> ('v regexp,'v) NFA_rec" where 
    "reg2nfa r a= \<lparr>  \<Q> = reg2q r a,
                  \<Sigma> = alp_reg  r a,
                  \<Delta> = fst (trans2LTS  r a),
                  \<Delta>' = snd (trans2LTS  r a),
                  \<I> ={r}, 
                  \<F> ={\<epsilon>}\<rparr> " 

section "function correctness of transition from regexp expression to  nondeterministic finite automaton"

theorem uniqueInitalState:"\<I> (reg2nfa r v) = {r}"
  apply (induct r)
  apply auto
  done

theorem uniqueFinalState:"\<F> (reg2nfa r v) = {\<epsilon>}"
  apply(induct r)
  apply auto
  done

theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    apply auto
    by (rule LTS_is_reachable.cases) auto
next
    case (LChr x)
    then show ?case     
      apply( unfold \<L>_def NFA_accept_def)
      apply auto
      apply(rule LTS_is_reachable.cases)
      apply auto
      subgoal for w
      proof -
        assume a1:" LTS_is_reachable ({(LChr x, {x}, \<epsilon>)}, {}) \<epsilon> w \<epsilon>"
        from a1 have "w = []" 
          by(rule LTS_is_reachable.cases)auto
        then show "w=[]" .
      qed 
      done
    next
  case Dot
  then show ?case 
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
    subgoal for x 
      apply(simp add:image_iff)
      apply(rule LTS_is_reachable.cases)
      apply auto
      subgoal for a w
      proof -
        assume a1:"LTS_is_reachable ({(Dot, v, \<epsilon>)}, {}) \<epsilon> w \<epsilon>"
        from a1 have "w=[]"       
          by (rule LTS_is_reachable.cases) auto
        then show "w=[]" .
      qed
      done
    done    
next
  case \<epsilon>
  then show ?case     
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
    subgoal for x
    by(rule LTS_is_reachable.cases) auto
  done
next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for x
    proof -
      assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w ε}"
      assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w ε}"
      assume a3:"LTS_is_reachable (trans2LTS r1 v) r1 x ε"
      then show "∃q''. (q'' = r1 ∨ q'' = r2 ∨ q'' = Alter r1 r2 ∨ (Alter r1 r2, q'') ∈ snd (trans2LTS r1 v) ∨ (Alter r1 r2, q'') ∈ snd (trans2LTS r2 v)) ∧
          LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))))
           q'' x ε"
     proof -
        have c1:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v),  insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) (Alter r1 r2) [] r1" 
          by (metis LTS_Empty LTS_Step1 insertI1 snd_conv)
        from a3 have c2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v),  insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) r1 x ε"
          by (metis Un_insert_right subLTSlemma)
        from c1 c2 have "LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v),  insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) (Alter r1 r2) x ε"
          by (metis LTS_Step1 insertI1 snd_eqD)
        then show ?thesis by auto
      qed
    qed
     subgoal for x
      proof -
      assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w ε} "
      assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w ε}"
      assume a3:"LTS_is_reachable (trans2LTS r2 v) r2 x ε"
      then show " ∃q''. (q'' = r1 ∨ q'' = r2 ∨ q'' = Alter r1 r2 ∨ (Alter r1 r2, q'') ∈ snd (trans2LTS r1 v) ∨ (Alter r1 r2, q'') ∈ snd (trans2LTS r2 v)) ∧
          LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v)))))
           q'' x ε"
      proof -
        have c1:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) (Alter r1 r2) [] r2" 
          by (metis LTS_Empty LTS_Step1 insertI1 insertI2 snd_eqD)
        have c2:"LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) r2 x ε"
          using a3 
          by (smt (z3) Un_commute Un_insert_right subLTSlemma)
        have "LTS_is_reachable (fst (trans2LTS r1 v) ∪ fst (trans2LTS r2 v), insert (Alter r1 r2, r1) (insert (Alter r1 r2, r2) (insert (Alter r1 r2, Alter r1 r2) (snd (trans2LTS r1 v) ∪ snd (trans2LTS r2 v))))) (Alter r1 r2) x ε"
          using c1 c2 
          by (metis LTS_Step1 insertI1 insertI2 snd_eqD)
        then show ?thesis by auto
       qed
     qed
     subgoal for x
       sorry
   done
 next
  case (Concat r1 r2)
  then show ?case 
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for q p
    proof -
    assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w ε}"
    assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w ε}"
    assume a3:"LTS_is_reachable (trans2LTS r1 v) r1 q ε"
    assume a4:"LTS_is_reachable (trans2LTS r2 v) r2 p ε"
    show "∃q''. (q'' = Concat r1 r2 ∨ r1 = ε ∧ q'' = r2 ∨ (∃q'. q'' = Concat q' r2 ∧ (r1, q') ∈ snd (trans2LTS r1 v)) ∨ (Concat r1 r2, q'') ∈ snd (trans2LTS r2 v)) ∧
          LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
           q'' (q @ p) ε"
    proof-
      have c1:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)},({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)})) (Concat r1 r2) q (Concat ε r2)"
        using a3   
        apply (induction rule: LTS_is_reachable.induct)  
        apply auto
        apply blast
        by blast
      then have c2:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)},
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)})))
             (Concat r1 r2) q (Concat ε r2)"
        apply (induction rule: LTS_is_reachable.cases) 
        apply auto
        apply (metis (no_types, lifting) Un_insert_right prod.sel(1) snd_eqD subLTSlemma sup_idem)
        by (metis (no_types, lifting) Un_insert_right eq_snd_iff prod.sel(1) subLTSlemma sup_idem)
      then have c3:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))) (Concat r1 r2) q (Concat ε r2)"
        apply auto
        by (metis (no_types, lifting) Un_insert_left fst_conv snd_eqD subLTSlemma)
      have c4:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))) (Concat ε r2) [] r2"
        by auto
      have c5:"LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v)))) r2 p ε"
        using a4 
        by (smt (z3) insert_def subLTSlemma sup.commute sup_left_commute)
      have "LTS_is_reachable
           ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
            insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
           (Concat r1 r2) (q @ p) ε" using c3 c4 c5 
        by (smt (z3) append.right_neutral joinLTSlemma)
      thus ?thesis by auto
    qed
  qed
  subgoal for x 
  proof -
    assume a1:"sem_reg r1 v = {w. LTS_is_reachable (trans2LTS r1 v) r1 w ε}"
    assume a2:"sem_reg r2 v = {w. LTS_is_reachable (trans2LTS r2 v) r2 w ε}"
    assume a3:"LTS_is_reachable
     ({(Concat q r2, va, Concat q' r2) |q va q'. (q, va, q') ∈ fst (trans2LTS r1 v)} ∪ fst (trans2LTS r2 v),
      insert (Concat r1 r2, Concat r1 r2) (insert (Concat ε r2, r2) ({(Concat q r2, Concat q' r2) |q q'. (q, q') ∈ snd (trans2LTS r1 v)} ∪ snd (trans2LTS r2 v))))
     (Concat r1 r2) x ε"
    show  "∃q p. x = q @ p ∧ LTS_is_reachable (trans2LTS r1 v) r1 q ε ∧ LTS_is_reachable (trans2LTS r2 v) r2 p ε"
      sorry
qed
  done
next
  case (Star r)
  then show ?case 
     apply(unfold \<L>_def NFA_accept_def)
     apply auto 
    subgoal for x 
      sorry
    sorry
next
  case (Plus r)
  then show ?case  
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal for x 
    
    sorry 
    subgoal for x 
    
    sorry
    subgoal for x 
     sorry
    done
next
  case (Ques r)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto 
    subgoal for x
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w ε}"
      assume a2:"LTS_is_reachable (trans2LTS r v) r x ε"
      show "∃q''. (q'' = ε ∨ q'' = r ∨ q'' = Ques r ∨ (Ques r, q'') ∈ snd (trans2LTS r v)) ∧
          LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, ε) (insert (Ques r, r) (insert (Ques r, Ques r) (snd (trans2LTS r v))))) q'' x ε"
      proof -
        from a2 have c1:"LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, ε) (insert (Ques r, r) (insert (Ques r, Ques r) (snd (trans2LTS r v))))) r x ε"
          apply(rule LTS_is_reachable.cases)
          apply auto
          apply (metis Un_insert_right boolean_algebra_cancel.sup0 fst_conv snd_conv subLTSlemma)
          by (smt (z3) Un_commute Un_insert_left fst_conv snd_conv subLTSlemma sup_idem)
        have "LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, ε) (insert (Ques r, r) (insert (Ques r, Ques r) (snd (trans2LTS r v))))) (Ques r) x ε"
          using c1 by auto
        thus ?thesis by auto
      qed
    qed
    subgoal for x
    proof -
      assume a1:"sem_reg r v = {w. LTS_is_reachable (trans2LTS r v) r w ε}"
      assume a2:"LTS_is_reachable (fst (trans2LTS r v), insert (Ques r, ε) (insert (Ques r, r) (insert (Ques r, Ques r) (snd (trans2LTS r v))))) (Ques r) x ε"
      assume a3:"x ≠ []" 
      show "∃q''. (r, q'') ∈ snd (trans2LTS r v) ∧ LTS_is_reachable (trans2LTS r v) q'' x ε"
        sorry
    qed
    done
qed


end