(*  Author:     Hongjian Jiang
    Copyright   2023 TUK
*)

section "From regular expressions directly to nondeterministic automata"

theory RegExp2NA
imports Regular_Exp NA
begin

type_synonym 'a bitsNA = "('a, nat list)na"
(*Use nat to represent state where 2 equals True, 3 equals False and 4 equals Split*)

fun mapLR ::"nat list set \<Rightarrow> nat list set \<Rightarrow> nat list set" where 
"mapLR A B = {a @ [4] @ b|a b. a\<in>A \<and> b\<in>B}"

fun index_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"index_of x [] = 0"| 
"index_of x (y # ys) = (if x = y then 0 else 1 + index_of x ys)"

fun take_first_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"take_first_list a A = take (index_of a A) A"

fun take_second_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"take_second_list a A = drop ((index_of a A)+1) A"

definition
"atom"  :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where
"atom a vs = ([2],vs,
            \<lambda>b s. if s=[2] \<and> b=a then {[3]} else {},
            \<lambda>s. s=[3])"

definition 
  dot ::  "'a set \<Rightarrow> 'a bitsNA" where
"dot vs=([2], vs,
            \<lambda>b s. if s=[2] \<and> b \<in> vs then {[3]} else {},
            \<lambda>s. s=[3])"

definition
 or :: " 'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"or= (\<lambda>(ql,vlTrue,dl,fl)(qr,vlFalse,dr,fr).
   ([],vlTrue\<union>vlFalse,
    \<lambda>a s. case s of
            [] \<Rightarrow> (2 ## dl a ql) \<union> (3 ## dr a qr)
          | left#s \<Rightarrow> if left = 2 then 2 ## dl a s
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> (fl ql \<or> fr qr)             
                | left#s \<Rightarrow> if left = 2 then fl s else fr s))"

definition
 conc :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"conc = (\<lambda>(ql,vlTrue, dl,fl)(qr,vlFalse, dr,fr).
   (2#ql,vlTrue \<union> vlFalse,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left =2  then (2 ## dl a s) \<union>
                                   (if fl s then 3 ## dr a qr else {})
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | 
                  left#s \<Rightarrow> left = 2 \<and> fl s \<and> fr qr | left = 3 \<and> fr s))"

definition
 epsilon :: "'a set \<Rightarrow> 'a bitsNA" where
"epsilon vs= ([],vs,\<lambda>a s. {}, \<lambda>s. s=[])"

definition
 plus :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
"plus = (\<lambda>(q,vs,d,f). (q, vs, \<lambda>a s. d a s \<union> (if f s then d a q else {}), f))"

 
definition
 star :: "'a set \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"star vs A = or (epsilon vs) (plus A)"

definition
 range :: "'a set \<Rightarrow> 'a bitsNA \<Rightarrow> nat \<Rightarrow> 'a bitsNA" where
"range vs A m=  (if m = 0 then ([],vs,\<lambda>a s. {}, \<lambda>s. s=[]) else fold (conc) (replicate (m-1) A) A )"

definition
 inter :: " 'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"inter= (\<lambda>(ql,vlTrue,dl,fl)(qr,vlFalse,dr,fr).
   ([],vlTrue\<union>vlFalse,
      \<lambda>a s. case s of 
              [] \<Rightarrow> mapLR (dl a ql) (dr a qr)
          | left#s \<Rightarrow>  mapLR (dl a (take_first_list 4 (left #s))) (dr a (take_second_list 4 (left#s))),
    \<lambda>s.  fl (take_first_list 4 (s)) \<and> fr (take_second_list 4 (s))))"

primrec rexp2na :: " 'a rexp \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where
"rexp2na Zero  vs     = ([], vs ,\<lambda>a s. {}, \<lambda>s. False)" |
"rexp2na One   vs     = epsilon vs" |
"rexp2na (Atom a)  vs  = atom a vs" |
"rexp2na (Alter r s)  vs= or (rexp2na r vs) (rexp2na s vs)" |
"rexp2na (Times r s) vs= conc (rexp2na r vs) (rexp2na s vs)" |
"rexp2na (Star r)   vs = star vs (rexp2na r vs)" |
"rexp2na Dot vs= dot vs" | 
"rexp2na (Ques r) vs = or (rexp2na r vs) (epsilon vs)"|
"rexp2na (Plus r) vs = or (rexp2na r vs) (star vs (rexp2na r vs))"|
"rexp2na (Range r m) vs = range vs (rexp2na r vs) m" |
"rexp2na (Inter r s) vs = inter (rexp2na r vs) (rexp2na s vs) "

value "accepts (rexp2na (Inter (Atom (1::nat)) (Atom 1)) {1}) [1]"
value "accepts (rexp2na (Inter (Alter (Atom (1::nat)) (Atom 2)) (Alter (Atom 2) (Atom 1))) {1}) [2]"
value "accepts (rexp2na (Inter (Times (Atom (1::nat)) (Atom 2)) (Alter (Atom 2) (Atom 1))) {1}) [2]"

declare split_paired_all[simp]

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a vs) q) = (q = [3])"
by(simp add:atom_def)

lemma start_atom: "start (atom a vs) = [2]"
by(simp add:atom_def)


lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a vs) b = (p=[2] \<and> q=[3] \<and> b=a)"
by (simp add: atom_def step_def)

lemma False_False_in_steps_atom:
 "([3],[3]) : steps (atom a vs) w = (w = [])"
  apply (induct "w")
  apply simp
  apply (simp add: relcomp_unfold)
done

lemma start_fin_in_steps_atom:
 "(start (atom a vs), [3]) : steps (atom a vs) w = (w = [a])"
  apply (induct "w")
  apply (simp add: start_atom)
  apply (simp add: False_False_in_steps_atom relcomp_unfold start_atom)
done

lemma accepts_atom:
 "accepts (atom a vs) w = (w = [a])"
by (simp add: accepts_conv_steps start_fin_in_steps_atom fin_atom)

(******************************************************)
(*                       dot                          *)
(******************************************************)
lemma fin_dot: "(fin (dot vs) q) = (q = [3])"
  by (simp add: dot_def)
 
lemma start_dot: "start (dot vs) = [2]"
  by(simp add:dot_def)

lemma in_step_dot_Some[simp]:
 "(p,q) : step (dot vs) b= (p=[2] \<and> q=[3] \<and> b \<in> vs)"
by (simp add: dot_def step_def)


lemma False_False_in_steps_dot:
 "([3],[3]) : steps (dot vs) w = (w = [])"
  apply (induct "w")
  apply simp
  apply (simp add: relcomp_unfold)
done

lemma start_fin_in_steps_do:
 "(start (dot vs), [3]) : steps (dot vs) w = (w \<in> ((\<lambda>x. [x]) ` vs))"
  apply (induct "w")
  apply (simp add: start_dot)
  apply force
  apply (simp add: False_False_in_steps_dot relcomp_unfold start_dot) 
  apply auto
done

lemma accepts_dot:  "accepts (dot vs) w = (w \<in> ((\<lambda>x. [x]) ` vs))"
by (simp add: accepts_conv_steps fin_dot start_fin_in_steps_do)

(******************************************************)
(*                      or                            *)
(******************************************************)

(***** lift True/False over fin *****)

lemma fin_or_True[iff]:
 "\<And>L R. fin (or L R) (2#p) = fin L p"
by(simp add:or_def)

lemma fin_or_False[iff]:
 "\<And>L R. fin (or L R) (3#p) = fin R p"
by(simp add:or_def)

(***** lift True/False over step *****)

lemma True_in_step_or[iff]:
"\<And>L R. (2#p,q) : step (or L R) a = (\<exists>r. q = 2#r \<and> (p,r) \<in> step L a)"
  apply (simp add:or_def step_def)
  apply blast
done

lemma False_in_step_or[iff]:
"\<And>L R. (3#p,q) : step (or L R) a = (\<exists>r. q = 3#r \<and> (p,r) \<in> step R a)"
  apply (simp add:or_def step_def)
  apply blast
done


(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
 "\<And>p. (2#p,q)\<in>steps (or L R) w = (\<exists>r. q = 2#r \<and> (p,r) \<in> steps L w)"
  apply (induct "w")
  apply force  
  apply force
done

lemma lift_False_over_steps_or[iff]:
 "\<And>p. (3#p,q)\<in>steps (or L R) w = (\<exists>r. q = 3#r \<and> (p,r)\<in>steps R w)"
  apply (induct "w")
  apply force
  apply force
done

(** From the start  **)

lemma start_step_or[iff]:
 "\<And>L R. (start(or L R),q) : step(or L R) a = 
         (\<exists>p. (q = 2#p \<and> (start L,p) : step L a) | 
               (q = 3#p \<and> (start R,p) : step R a))"
  apply (simp add:or_def step_def)
  apply blast
done

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
  ( (w = [] \<and> q = start(or L R)) | 
    (w \<noteq> [] \<and> (\<exists>p.  q = 2  # p \<and> (start L,p) : steps L w | 
                      q = 3 # p \<and> (start R,p) : steps R w)))"
  apply (case_tac "w")
  apply (simp)
  apply blast
  apply (simp)
  apply blast
done

lemma fin_start_or[iff]:
 "\<And>L R. fin (or L R) (start(or L R)) = (fin L (start L) | fin R (start R))"
by (simp add:or_def)

lemma accepts_or[iff]:
 "accepts (or L R) w = (accepts L w | accepts R w)"
  apply (simp add: accepts_conv_steps steps_or)
  (* get rid of case_tac: *)
  apply (case_tac "w = []")
by auto

(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

lemma fin_conc_True[iff]:
 "\<And>L R. fin (conc L R) (2#p) = (fin L p \<and> fin R (start R))"
by(simp add:conc_def)

lemma fin_conc_False[iff]:
 "\<And>L R. fin (conc L R) (3#p) = fin R p"
by(simp add:conc_def)


(** True/False in step **)

lemma True_step_conc[iff]:
 "\<And>L R. (2#p,q) : step (conc L R) a = 
        ((\<exists>r. q=2#r \<and> (p,r): step L a) | 
         (fin L p \<and> (\<exists>r. q=3#r \<and> (start R,r) : step R a)))"
  apply (simp add:conc_def step_def)
  apply blast
done

lemma False_step_conc[iff]:
 "\<And>L R. (3#p,q) : step (conc L R) a = 
       (\<exists>r. q = 3#r \<and> (p,r) : step R a)"
  apply (simp add:conc_def step_def)
  apply blast
done

(** False in steps **)

lemma False_steps_conc[iff]:
 "\<And>p. (3#p,q): steps (conc L R) w = (\<exists>r. q=3#r \<and> (p,r): steps R w)"
  apply (induct "w")
  apply fastforce
  apply force
done

(** True in steps **)

lemma True_True_steps_concI:
 "\<And>L R p. (p,q) : steps L w \<Longrightarrow> (2#p,2#q) : steps (conc L R) w"
  apply (induct "w")
  apply simp
  apply simp
  apply fast
done

lemma True_False_step_conc[iff]:
 "\<And>L R. (2#p,3#q) : step (conc L R) a = 
         (fin L p \<and> (start R,q) : step R a)"
by simp

lemma True_steps_concD[rule_format]:
 "\<forall>p. (2#p,q) : steps (conc L R) w \<longrightarrow> 
     ((\<exists>r. (p,r) : steps L w \<and> q = 2#r)  \<or> 
  (\<exists>u a v. w = u@a#v \<and> 
            (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) : steps R v \<and> q = 3#t)))))"
  apply (induct "w")
  apply simp
  apply simp
  apply (clarify del:disjCI)
  apply (erule disjE)
  apply (clarify del:disjCI)
  apply (erule allE, erule impE, assumption)
  apply (erule disjE)
  apply blast
  apply (rule disjI2)
  apply (clarify)
  apply simp
  apply (rule_tac x = "a#u" in exI)
  apply simp
  apply blast
  apply (rule disjI2)
  apply (clarify)
  apply simp
  apply (rule_tac x = "[]" in exI)
  apply simp
  apply blast
done

lemma True_steps_conc:
 "(2#p,q) : steps (conc L R) w = 
 ((\<exists>r. (p,r) : steps L w \<and> q = 2#r)  \<or>
  (\<exists>u a v. w = u@a#v \<and>
            (\<exists>r. (p,r) : steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) : steps R v \<and> q = 3#t)))))"
by(force dest!: True_steps_concD intro!: True_True_steps_concI)

(** starting from the start **)
lemma start_conc:
  "\<And>L R. start(conc L R) = 2#start L"
by (simp add:conc_def)

lemma final_conc:
 "\<And>L R. fin(conc L R) p = ((fin R (start R) \<and> (\<exists>s. p = 2#s \<and> fin L s)) \<or>
                           (\<exists>s. p = 3#s \<and> fin R s))"
  apply (simp add:conc_def split: list.split) 
  apply blast
done

lemma accepts_conc:
 "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
  apply (simp add: accepts_conv_steps True_steps_conc final_conc start_conc)
  apply (rule iffI)
  apply (clarify)
  apply (erule disjE)
  apply (clarify)
  apply (erule disjE)
  apply (rule_tac x = "w" in exI)
  apply simp
   apply blast
  apply auto[1]
  apply (erule disjE)
  apply force
  apply (clarify)
  apply (rule_tac x = "u" in exI)
  apply simp
  apply blast
  apply (clarify)
  apply (case_tac "v")
  apply simp
  apply blast
  apply simp
  apply blast
done

(******************************************************)
(*                     inter                          *)
(******************************************************)

lemma fin_inter[iff]:
 "\<And>L R. fin (inter L R) (p) = (fin L (take_first_list 4 p) \<and> fin R (take_second_list 4 p))"
by(simp add:inter_def)


(******************************************************)
(*                     range                          *)
(******************************************************)
lemma "accepts (range vs A 3) w = (\<exists>xs ys. accepts (conc A A) xs \<and> accepts (conc (conc A A) A) ys \<and> w = xs @ ys)"
  apply(unfold range_def) apply (simp add:conc_def) 
  apply (simp add: accepts_conv_steps True_steps_conc final_conc start_conc)
  sorry

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step (epsilon vs) a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) : steps (epsilon vs) w) = (w=[] \<and> p=q)"
by (induct "w") auto

lemma accepts_epsilon[iff]: "accepts (epsilon vs) w = (w = [])"
apply (simp add: steps_epsilon accepts_conv_steps)
apply (simp add: epsilon_def)
done

(******************************************************)
(*                       plus                         *)
(******************************************************)

lemma start_plus[simp]: "\<And>A. start (plus A) = start A"
by(simp add:plus_def)

lemma fin_plus[iff]: "\<And>A. fin (plus A) = fin A"
by(simp add:plus_def)

lemma step_plusI:
  "\<And>A. (p,q) : step A a \<Longrightarrow> (p,q) : step (plus A) a"
by(simp add:plus_def step_def)

lemma steps_plusI: "\<And>p. (p,q) : steps A w \<Longrightarrow> (p,q) \<in> steps (plus A) w"
apply (induct "w")
 apply simp
apply simp
apply (blast intro: step_plusI)
done

lemma step_plus_conv[iff]:
 "\<And>A. (p,r): step (plus A) a = 
       ( (p,r): step A a | fin A p \<and> (start A,r) : step A a )"
by(simp add:plus_def step_def)

lemma fin_steps_plusI:
 "[| (start A,q) : steps A u; u \<noteq> []; fin A p |] 
 ==> (p,q) : steps (plus A) u"
apply (case_tac "u")
 apply blast
apply simp
apply (blast intro: steps_plusI)
done

(* reverse list induction! Complicates matters for conc? *)
lemma start_steps_plusD[rule_format]:
 "\<forall>r. (start A,r) \<in> steps (plus A) w \<longrightarrow>
     (\<exists>us v. w = concat us @ v \<and> 
              (\<forall>u\<in>set us. accepts A u) \<and> 
              (start A,r) \<in> steps A v)"
apply (induct w rule: rev_induct)
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply simp
apply simp
apply (clarify)
apply (erule allE, erule impE, assumption)
apply (clarify)
apply (erule disjE)
 apply (rule_tac x = "us" in exI)
 apply (simp)
 apply blast
apply (rule_tac x = "us@[v]" in exI)
apply (simp add: accepts_conv_steps)
apply blast
done

lemma steps_star_cycle[rule_format]:
 "us \<noteq> [] \<longrightarrow> (\<forall>u \<in> set us. accepts A u) \<longrightarrow> accepts (plus A) (concat us)"
apply (simp add: accepts_conv_steps)
apply (induct us rule: rev_induct)
 apply simp
apply (rename_tac u us)
apply simp
apply (clarify)
apply (case_tac "us = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (clarify)
apply (case_tac "u = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (blast intro: steps_plusI fin_steps_plusI)
done

lemma accepts_plus[iff]:
 "accepts (plus A) w = 
 (\<exists>us. us \<noteq> [] \<and> w = concat us \<and> (\<forall>u \<in> set us. accepts A u))"
apply (rule iffI)
   apply (simp add: accepts_conv_steps)
 apply (clarify)
 apply (drule start_steps_plusD)
 apply (clarify)
 apply (rule_tac x = "us@[v]" in exI)
 apply (simp add: accepts_conv_steps)
 apply blast
apply (blast intro: steps_star_cycle)
  done


(******************************************************)
(*                       star                         *)
(******************************************************)

lemma accepts_star:
 "accepts (star vs A) w = (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us)"
apply(unfold star_def)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (rule_tac x = "[]" in exI)
  apply simp
 apply blast
apply force
  done

(******************************************************)
(*                       range                         *)
(******************************************************)


(***** Correctness of rFalsen *****)
lemma accepts_rexp2na:
 "\<And>w. accepts (rexp2na r v) w = (w : lang r v)"
apply (induct "r")
     apply (simp add: accepts_conv_steps)
          apply simp
        
         apply (simp add: accepts_atom)
  
  apply (simp)
       apply (simp add: accepts_conc Regular_Set.conc_def) 
   apply (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
   apply (simp add: accepts_dot)
  subgoal for r w apply auto done
  subgoal for r w  
    apply (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
    by auto 
  done
end