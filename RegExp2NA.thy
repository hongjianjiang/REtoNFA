(*  Author:     Hongjian Jiang
    Copyright   2023 RHEINLAND-PFÄLZISCHE TECHNISCHE UNIVERSITÄT KAISERSLAUTERN-LANDAU
*)

section "From regular expressions directly to nondeterministic automata"

theory RegExp2NA
imports Regular_Exp NA
begin

type_synonym 'a bitsNA = "('a, nat list)na"

(*Use nat to represent state where 2 equals to True, 3 equals to False*)


fun mapLR ::"nat list set \<Rightarrow> nat list set \<Rightarrow> nat list set" where 
"mapLR A B = {[length a] @ a @ b|a b. a \<in> A \<and> b \<in> B}" 

fun mapLR1 ::"nat list set  \<Rightarrow> nat list set" where 
"mapLR1 A = {[length a] @ a |a . a \<in> A}" 

definition
  "atom"  :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where
"atom a vs = ([2],vs,
            \<lambda>b s. if s=[2] \<and> b=a \<and> a : vs then {[3]} else {[1]},
            \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> (left#s) = [3])"

definition 
  dot ::  "'a set \<Rightarrow> 'a bitsNA" where
"dot vs=([2], vs,
            \<lambda>b s. if s=[2] \<and> b \<in> vs then {[3]} else {[1]},
            \<lambda>s. s=[3])"

definition
  or :: " 'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"or= (\<lambda>(ql,vl1,dl,fl)(qr,vl2,dr,fr).
   ([],vl1\<union>vl2,
    \<lambda>a s. case s of
            [] \<Rightarrow> (2 ## dl a ql) \<union> (3 ## dr a qr)
          | left#s \<Rightarrow> if left = 2 then 2 ## dl a s
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> (fl ql \<or> fr qr)             
                | left#s \<Rightarrow> if left = 2 then fl s else fr s))"

definition
  epsilon :: "'a set \<Rightarrow> 'a bitsNA" where
"epsilon vs= ([],vs,\<lambda>a s. {[1]}, \<lambda>s. s=[])"

definition
  inter :: " 'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"inter= (\<lambda>(ql,vl1,dl,fl)(qr,vl2,dr,fr).
   ([length ql] @ ql @ qr,vl1 \<inter> vl2,
    \<lambda>a s. mapLR (dl a (take (hd s) (tl s))) (dr a (drop (hd s) (tl s))),
    \<lambda>s. case s of [] \<Rightarrow> False | left # s \<Rightarrow> fl (take left s) \<and> fr (drop  left  s)))"

definition
  conc :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"conc = (\<lambda>(ql,vl1, dl,fl)(qr,vl2, dr,fr).
   (2#ql,vl1 \<union> vl2,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left =2  then (2 ## dl a s) \<union>
                                   (if fl s then 3 ## dr a qr else {})
                              else 3 ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | 
                  left#s \<Rightarrow> left = 2 \<and> fl s \<and> fr qr | left = 3 \<and> fr s))"

definition
plus :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
  "plus = (\<lambda>(q,vs,d,f). (q, vs, \<lambda>a s. d a s \<union> (if f s then d a q else {}), %s. f s))"

definition
star :: "'a set \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
  "star vs A = or (epsilon vs) (plus A)"

primrec multi ::"'a bitsNA \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where 
  "multi r 0 vs = epsilon vs"|
  "multi r (Suc n) vs = conc r (multi r n vs)"

definition range :: "'a bitsNA \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where
  "range A n m vs = (if n > m then ([], vs ,\<lambda>a s. {}, \<lambda>s. False) else fold (or) (map (\<lambda>a. multi A a vs) [n+1..<m+1]) (multi A n vs))"

definition
  neg :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"neg= (\<lambda>(ql,vl1,dl,fl) (qr,vl2,dr,fr).
   ([length ql] @ ql @ qr, vl2,
    \<lambda>a s. if dl a (take (hd s) (tl s)) = {} 
          then 0 ## (dr a (drop (hd s) (tl s))) 
          else mapLR (dl a (take (hd s) (tl s))) (dr a (drop (hd s) (tl s))),
    \<lambda>s. case s of [] \<Rightarrow> False | left # s \<Rightarrow> \<not> fl (take left s) \<and> fr (drop left s)))"

definition 
neg1 ::"'a bitsNA \<Rightarrow> 'a bitsNA" where
"neg1 = (\<lambda>(q,v,d,f). 
        (length q # q, v, 
        \<lambda>a s. case s of [] \<Rightarrow>  {[]} | 
                   left # s \<Rightarrow>  if d a s = {} then {[]} else mapLR1 (d a s), 
        \<lambda>s. case s of [] \<Rightarrow> True |
                      left # s \<Rightarrow> \<not> f s))"

primrec rexp2na :: " 'a rexp \<Rightarrow> 'a set \<Rightarrow> 'a bitsNA" where
  "rexp2na Zero          vs = ([], vs ,\<lambda>a s. {}, \<lambda>s. False)" |
  "rexp2na One           vs = epsilon vs" |
  "rexp2na (Atom a)      vs = atom a vs" |
  "rexp2na (Alter r s)   vs = or (rexp2na r vs) (rexp2na s vs)" |
  "rexp2na (Times r s)   vs = conc (rexp2na r vs) (rexp2na s vs)" |
  "rexp2na (Star r)      vs = star vs (rexp2na r vs)" |  
  "rexp2na Dot           vs = dot vs" | 
  "rexp2na (Ques r)      vs = or (rexp2na r vs) (epsilon vs)" |
  "rexp2na (Plus r)      vs = conc (rexp2na r vs) (star vs (rexp2na r vs))" |
  "rexp2na (Inter r s)   vs = inter (rexp2na r vs) (rexp2na s vs)" |
  "rexp2na (Range r n m) vs = range (rexp2na r vs) n m vs" |
  "rexp2na (Neg r)       vs = neg1 (rexp2na r vs)"|
  "rexp2na (Multi r n)   vs = multi (rexp2na r vs) n vs"
  
declare split_paired_all[simp] 

(******************************************************)
(*                       atom                         *)
(******************************************************)
lemma fin_atom: "(fin (atom a vs) q) = (if q = [] then False else q = [3])"
  apply(simp add:atom_def)
  by (simp add: list.case_eq_if)

lemma start_atom: "start (atom a vs) = [2]"
  by(simp add:atom_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a vs) b = (if p=[2] \<and> b=a \<and> a : vs then q=[3] else q = [1])"
  by (simp add: atom_def step_def)

lemma no_empty_atoms: "([Suc 0], [3]) \<notin> steps (atom a vs) w"
  apply(induct w)
  apply simp 
  apply simp 
  by force

lemma False_False_in_steps_atom:
 "([3],[3]) : steps (atom a vs) w = (w = [])"
  apply (induct "w")
  apply simp
  apply (simp add: relcomp_unfold)
  apply (simp add:no_empty_atoms)
done

lemma start_fin_in_steps_atom:
 "(start (atom a vs), [3]) : steps (atom a vs) w = (w = [a] \<and> a : vs)"
  apply (induct "w")
  apply (simp add: start_atom)
  apply (simp add: False_False_in_steps_atom relcomp_unfold start_atom) 
by (metis False_False_in_steps_atom no_empty_atoms)

lemma accepts_atom:
 "accepts (atom a vs) w = (w = [a] \<and> a : vs)"
  by (metis accepts_conv_steps fin_atom list.discI start_fin_in_steps_atom)

(******************************************************)
(*                       dot                          *)
(******************************************************)
lemma fin_dot: "(fin (dot vs) q) = (q = [3])"
  by (simp add: dot_def)
 
lemma start_dot: "start (dot vs) = [2]"
  by(simp add:dot_def)

lemma in_step_dot_Some[simp]:
 "(p,q) : step (dot vs) b= (if p=[2] \<and> b \<in> vs then q=[3] else q = [Suc 0])"
by (simp add: dot_def step_def)

lemma no_empty_dots:"([Suc 0], [3]) \<notin> steps (dot vs) w"
  apply(induct w)
  apply simp
  apply simp
  by force

lemma False_False_in_steps_dot:
 "([3],[3]) : steps (dot vs) w = (w = [])"
  apply (induct "w")
  apply simp
  apply (simp add: relcomp_unfold)
  apply (simp add:no_empty_dots)
done

lemma start_fin_in_steps_do:
 "(start (dot vs), [3]) : steps (dot vs) w = (w \<in> ((\<lambda>x. [x]) ` vs))"
  apply (induct "w")
  apply (simp add: start_dot)
  apply force
  apply (simp add: False_False_in_steps_dot relcomp_unfold start_dot) 
  by (smt (verit) False_False_in_steps_dot image_iff list.inject no_empty_dots)

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
  apply (simp add:or_def step_def) apply auto
done

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
  ( (w = [] \<and> q = start(or L R)) | 
    (w \<noteq> [] \<and> (\<exists>p.  q = 2 # p \<and> (start L,p) : steps L w | 
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
(*                     inter                          *)
(******************************************************)

lemma fin_inter[iff]:
 "\<And>L R q. fin (inter L R) q = (\<exists>m n. q = m # n \<and> fin  L (take m n) \<and> fin R (drop m n))"
  apply (simp add:inter_def) 
  apply (case_tac q) 
  apply auto 
  done
 
lemma start_inter[iff]:
  "\<And>L R. start(inter L R) = [length (start L)] @ start L @ start R"
  by (simp add:inter_def)


lemma step_inter[iff]:
"\<And>L R. (p,q) : step (inter L R) a = (\<exists>r1 r2. q = [length r1] @ r1 @ r2 
                                      \<and> (take (hd p) (tl p), r1) \<in> step L a 
                                      \<and> (drop (hd p) (tl p),r2) \<in> step R a)"
  apply (simp add:inter_def step_def) 
done

 

lemma inter_steps_left:"\<And>L R p. (p, q) \<in> steps (inter L R) w \<Longrightarrow> ((take (hd p) (tl p), take (hd q) (tl q))\<in> steps L w)"
  apply (induct w)
  apply simp 
  apply simp
  apply force
done

lemma inter_steps_right:"\<And>L R p. (p, q) \<in> steps (inter L R) w \<Longrightarrow> ((drop (hd p) (tl p), drop (hd q) (tl q))\<in> steps R w)"
  apply (induct w)
  apply simp  
  apply simp 
  apply force
done

lemma inter_steps_from_left_right :"\<And>L R p p1. (p, q) \<in> steps L w \<and> (p1, q1) \<in> steps R w \<Longrightarrow> ((length p # p @ p1, length q # q @ q1) \<in> steps (inter L R) w)"
  apply(induction w)
  apply simp 
  apply simp 
  apply force 
done

lemma inter_steps_to_left_right:"\<And>L R p. (p, q) \<in> steps (inter L R) w \<Longrightarrow> ((take (hd p) (tl p), take (hd q) (tl q))\<in> steps L w \<and> (drop (hd p) (tl p), drop (hd q) (tl q))\<in> steps R w)"
  apply (induct w) 
  apply simp 
  apply simp 
  apply force
done

(** From the start  **)
lemma start_step_inter[iff]:
 "\<And>L R r1 r2. (start(inter L R),q) : step(inter L R) a = 
         (\<exists> r1 r2. q = length r1 # r1 @ r2 \<and> (start L,r1) : step L a \<and> (start R, r2) \<in> step R a )"
 apply (simp add:inter_def step_def)  
done

lemma steps_inter:"\<And>L R. (start (inter L R) ,q) \<in> steps (inter L R) w  \<Longrightarrow> 
    ((start L,take (hd q) (tl q)) \<in> steps L w \<and> (start R, (drop (hd q) (tl q))) \<in> steps R w)"
  apply(induct w) 
  apply simp  
  apply force 
  apply simp  
by (metis append_eq_conv_conj inter_steps_left inter_steps_right list.sel(1) list.sel(3) steps.simps(2))

lemma accepts_inter:
 "accepts (inter L R) w = (accepts L w \<and> accepts R w)"
  apply (simp add: accepts_conv_steps)  
  apply (case_tac w)
  apply simp  
  apply simp  
by (metis (no_types, opaque_lifting) append_eq_conv_conj inter_steps_from_left_right inter_steps_left inter_steps_right list.sel(1) list.sel(3) steps.simps(2))

(******************************************************)
(*                      conc                          *)
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
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "(p, q) \<in> step (epsilon vs) a = (q = [Suc 0])"
  by(simp add:epsilon_def step_def)

lemma no_empty_epsilon: "([Suc 0], []) \<notin> steps (epsilon vs) w"
  apply(induct w)
  apply simp
  apply simp
  by force

lemma steps_epsilon: "\<And>p. ((p,q) : steps (epsilon vs) w) = (if w \<noteq> [] then q = [Suc 0] else q = p)"
  apply(induct w)
  apply simp
  apply blast
  apply simp
  apply(case_tac "w = []")
  apply simp 
  apply simp
  by (simp add: relcomp.simps)


lemma accepts_epsilon[iff]: "accepts (epsilon vs) w = (w = [])"
  apply (simp add: steps_epsilon accepts_conv_steps)
  apply (simp add: epsilon_def)
  apply(case_tac "w = []")
  apply simp 
  apply simp
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
  thm relcomp.simps
  by (meson relcomp.simps step_plusI)

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
(*                       neg                          *)
(******************************************************)
lemma fin_neg[iff]:
"\<And>A B. fin (neg A B) q = (q \<noteq> [] \<and> \<not> fin A (take (hd q) (tl q)) \<and> fin B (drop (hd q) (tl q)))"
  apply(simp add:neg_def list.case_eq_if)
  done

lemma start_neg[iff]:
"\<And>A B. start (neg A B) = length (start A) # start A @ start B"
  apply(simp add:neg_def)
  done

lemma step_A_neg:
"\<And>A B. (p, q) \<in> step A a \<and> (p1, q1) \<in> step B a  \<Longrightarrow> (length p # p @ p1, length q # q @ q1) \<in> step (neg A B) a"
  apply(simp add:step_def neg_def)
  by auto

lemma empty_trans_neg:
"\<And>A B. next A a p = {} \<and> (p1, q) \<in> step B a \<Longrightarrow> (length p # p @ p1, 0# q) \<in> step (neg A B) a"
  apply(simp add:neg_def step_def)
  done

lemma neg_to_later_step:
"\<And>A B. (p, q) \<in> step (neg A B) a \<Longrightarrow> (drop (hd p) (tl p), drop (hd q) (tl q)) \<in> step B a"
  apply(simp add:neg_def step_def)
  subgoal for aa ab
  apply(case_tac "aa a (take (hd p) (tl p)) = {}")
  prefer 2
  apply simp 
  apply force
  apply simp 
  by fastforce
  done

lemma neg_to_later_steps:
"\<And>A B p. (p, q) \<in> steps (neg A B) w \<Longrightarrow> (drop (hd p) (tl p), drop (hd q) (tl q)) \<in> steps B w"
  apply(induct w)
  apply simp
  apply simp
  using neg_to_later_step 
  by fastforce

lemma start_neg2star_dot:
"\<And>A B. (start(neg A B), q) \<in> step (neg A B) a \<Longrightarrow> (start B, drop (hd q) (tl q)) \<in> step B a"
  apply(simp add:neg_def step_def)
  subgoal for aa ab ac ad
    apply(case_tac "ab a aa = {}")
     prefer 2
     apply simp 
     apply fastforce
    apply simp 
    by force
  done

lemma start_neg2star_dots:
"\<And>A B. (start(neg A B), q) \<in> steps (neg A B) w \<Longrightarrow> (start B, drop (hd q) (tl q)) \<in> steps B w"
  apply(induct w)
   apply simp
   apply force
  apply simp
  by (metis append_eq_conv_conj list.sel(1) list.sel(3) neg_to_later_steps steps.simps(2))
 

(******************************************************)
(*                       neg1                         *)
(******************************************************)
lemma fin_neg1[iff]: "fin (neg1 A) q = (q= [] \<or> \<not> fin A (tl q))"
  apply(simp add:neg1_def)
  by (smt (verit, best) case_prod_conv fin_def list.case_eq_if prod.sel(2) prod_cases4)

lemma start_neg1[iff]:"start (neg1 A) = (length (start A)) # (start A)"
  apply (simp add:neg1_def)
  by (smt (verit) case_prod_conv prod.sel(1) prod_cases4 start_def)

lemma step_A_neg1:
"\<And>A. (p, q) \<in> step A a \<Longrightarrow> ((length p # p, length q # q) \<in> step (neg1 A) a)"
  apply(simp add:step_def neg1_def)
  by blast

lemma step_neg1_A:"\<And>A. (p, q) \<in> step (neg1 A) a \<Longrightarrow> (if p = [] then q = [] else if next A a (tl p) = {} then q = [] else (tl p, tl q) \<in> step A a)"
  apply(simp add:step_def neg1_def)
  subgoal for ab
    apply(case_tac "p = []")
    apply simp  
    apply simp
    apply(case_tac "ab a (tl p) = {}")
    apply simp
    apply (simp add: list.case_eq_if)
    apply simp 
    by (smt (verit, ccfv_threshold) append.simps(1) list.case_eq_if list.distinct(1) list.sel(3) mapLR1.simps mem_Collect_eq tl_append2)
  done

lemma steps_A_neg1:
"\<And>A p. (p, q) \<in> steps A w \<Longrightarrow> ((length p # p, length q # q) \<in> steps (neg1 A) w)"
  apply(induct w)
  apply simp
  apply simp 
  by (meson relcomp.simps step_A_neg1)

lemma empty_trans_neg1:"\<And>A. (p, q) \<in> steps (neg1 A) w \<Longrightarrow> p = [] \<Longrightarrow> q = []"
  apply(induct w)
   apply simp
  apply simp
  using step_neg1_A by fastforce
                                                                       
lemma "accepts (neg1 A) w = (\<not> accepts A w)"      
  apply(induct w)                    
  apply (simp add: accepts_conv_steps)    
  apply (simp add: accepts_conv_steps)    
  sledgehammer                        
 
  
(******************************************************)
(*                       multi                        *)
(******************************************************)
lemma accptes_multi_Zero:
"accepts (multi r 0 vs) w =  (w = [])"
  by simp

lemma accptes_multi_SucN:
"accepts (multi r (Suc n) vs) w = (\<exists>w1 w2. accepts r w1 \<and> accepts ((multi r n) vs) w2 \<and> w = w1 @ w2)"
  apply(induct n)
  apply simp 
  apply (simp add: accepts_conc)
  by (metis accepts_conc multi.simps(2))

lemma accpet_step:"accepts A w1 \<Longrightarrow> (\<exists>us. (\<forall>u\<in>set us. accepts A u) \<and> w2 = concat us \<and> length us = m) \<Longrightarrow> 
                                    (\<exists>us. (\<forall>u\<in>set us. accepts A u) \<and> w1 @ w2 = concat us \<and> length us = Suc m)"
  apply(induct w2)
  apply simp apply auto  
  apply (metis append_self_conv concat.simps(2) concat_eq_Nil_conv length_Cons set_ConsD)
  by (metis concat.simps(2) length_Cons set_ConsD)
 
lemma accepts_multi:
"accepts (multi A m vs) w =  (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us \<and> length us = m)"
  apply(rule iffI)
  subgoal 
  apply(induct m arbitrary:w) 
  apply simp 
  subgoal for m apply (simp add:accepts_conc) apply clarify 
  by (simp add: accpet_step)
  done
  apply(induct m arbitrary:w) apply simp apply clarify
  by (smt (verit, ccfv_threshold) accptes_multi_SucN concat.simps(2) insertCI length_Suc_conv list.simps(15))

(******************************************************)
(*                       range                        *)
(******************************************************)

lemma zeroNrange: "accepts (range A m 0 vs) w \<Longrightarrow> (w = [])"
  apply(unfold range_def)
  apply(induct m) apply simp
  by (simp add: accepts_conv_steps)

lemma alter_Suc_n_range[simp]:
"\<And>w. accepts (range A m (Suc n) vs) w = accepts (range A m n vs) w \<or> accepts (multi A (Suc n) vs) w"
  apply(case_tac "m > Suc n") 
  apply (simp add: range_def)
  apply(case_tac "m = Suc n")
  apply(simp add:range_def) 
  using accepts_conv_steps 
  apply force
  apply(case_tac "m < Suc n") 
  prefer 2 
  apply simp 
  apply simp 
  apply(simp add:range_def) 
  apply auto
  done

lemma range_mltn:"m < n \<Longrightarrow> accepts (range A m n vs) w \<or> accepts (multi A (Suc n) vs) w \<Longrightarrow>  accepts (range A m (Suc n) vs) w"
  apply(case_tac "m > Suc n") 
  apply (simp add: range_def)
  apply(case_tac "m = Suc n")
  apply(simp add:range_def) 
  apply(case_tac "m < Suc n") 
  prefer 2 
  apply simp 
  apply simp 
  apply(simp add:range_def) 
  apply auto
  done

lemma case_unhold_range: "m > n \<Longrightarrow> \<not> accepts (range r m n vs) w"
  apply (simp add:range_def)
  apply (simp add: accepts_conv_steps)
  done

lemma range_n_eqs:"accepts (range A n n vs) w = accepts (multi A n vs) w" 
  apply(simp add:range_def)
  done

lemma range_eqs:"accepts (range A n n vs) w = accepts (multi A n vs) w"
  apply(simp add:range_def)
  done

lemma accepts_range:"
accepts (range A m n vs) w = (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us \<and> m \<le> length us & length us \<le> n)"
    apply(rule iffI)
    apply(case_tac "m > n") 
    using case_unhold_range 
    apply blast
    apply(case_tac "m = n")
    apply simp
    apply (metis accepts_multi order_refl range_eqs)
    apply(case_tac "m < n") 
    apply simp 
    prefer 2 
    apply simp 
    subgoal 
    apply(induct n arbitrary:w) 
    apply simp 
    subgoal for n w
    proof -
      assume a1:"\<And>w. \<lbrakk>accepts (range A m n vs) w; m < n\<rbrakk> \<Longrightarrow> \<exists>us. Ball (set us) (accepts A) \<and> w = concat us \<and> m \<le> length us \<and> length us \<le> n"
      assume a2:"accepts (range A m (Suc n) vs) w"
      assume a3:"m < Suc n"
      from a2 have c1:"accepts (range A m n vs) w \<or> accepts (multi A (Suc n) vs) w" 
        using alter_Suc_n_range 
        by blast
      then show "\<exists>us. Ball (set us) (accepts A) \<and> w = concat us \<and> m \<le> length us \<and> length us \<le> Suc n" 
      proof 
        assume "accepts (range A m n vs) w " 
        thus ?thesis using a1 a3 
          by (metis accepts_multi dual_order.refl le_SucI less_Suc_eq range_eqs)
      next 
        assume "accepts (multi A (Suc n) vs) w" 
        thus ?thesis by (metis a3 accepts_multi le_eq_less_or_eq)
      qed
    qed
    done
    subgoal 
    apply(case_tac "m>n")
    apply linarith
    apply(case_tac "m=n") 
    apply simp
    apply (metis accepts_multi le_antisym range_eqs)
    apply(case_tac "m<n")
    prefer 2 
    apply simp
    apply simp 
    apply(induct n arbitrary:w)
    apply simp 
    subgoal for n w  
    proof -
      assume a1:"\<And>w. \<lbrakk>\<exists>us. Ball (set us) (accepts A) \<and> w = concat us \<and> m \<le> length us \<and> length us \<le> n; m < n\<rbrakk> \<Longrightarrow> accepts (range A m n vs) w"
      assume a2:"\<exists>us. Ball (set us) (accepts A) \<and> w = concat us \<and> m \<le> length us \<and> length us \<le> Suc n" 
      assume a3:"m < Suc n"
      show "accepts (range A m (Suc n) vs) w"
      proof -
        from a2 have "(\<exists>us. Ball (set us) (accepts A) \<and> w = concat us \<and> m \<le> length us \<and> length us \<le> n) \<or> (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us \<and> length us = Suc n)"
          using le_Suc_eq 
          by blast
        then show ?thesis using a3 
            apply(case_tac "m = n")  
            apply simp 
            subgoal proof -
            assume b1:"(\<exists>us. (\<forall>x\<in>set us. accepts A x) \<and> w = concat us \<and> n \<le> length us \<and> length us \<le> n) \<or> (\<exists>us. (\<forall>u\<in>set us. accepts A u) \<and> w = concat us \<and> length us = Suc n)"
            assume b2:"m = n"
            from b1 have "accepts (multi A n vs) w \<or> accepts (multi A (Suc n) vs) w" 
              using accepts_multi le_antisym by blast
            then show ?thesis apply(simp add:a3)  
              apply(simp add:range_def) 
              apply(simp add:accepts_conc) 
              apply(simp add:accepts_multi) 
              by blast
          qed
          apply(case_tac "m < n") 
          prefer 2 
          apply simp 
          apply simp 
          by (metis a1 accepts_multi range_mltn)
      qed
    qed
    done
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

(***** Correctness of r *****)
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
  apply auto[1]  
  apply (simp add: accepts_conc Regular_Set.conc_def accepts_star in_star_iff_concat subset_iff Ball_def) 
  apply (simp add:accepts_range in_range_iff_concat  subset_iff Ball_def)   
  apply blast
  apply (simp add:accepts_neg)
  apply (smt (verit) accepts_dot accepts_neg in_star_iff_concat rexp2na.simps(12) subset_code(1))
  apply (simp add:accepts_inter) 
  apply (simp add:accepts_multi)  
  apply (meson concat_n_times multi_x_times subset_code(1))
  done
end
