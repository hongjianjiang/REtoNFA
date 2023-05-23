(*  Author: Tobias Nipkow, Alex Krauss, Christian Urban  *)

section "Regular sets"

theory Regular_Set
imports Main
begin

type_synonym 'a lang = "'a list set"

definition conc :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang" (infixr "@@" 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

text \<open>checks the code preprocessor for set comprehensions\<close>
export_code conc checking SML

overloading lang_pow == "compow :: nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
begin
  primrec lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
end


text \<open>for code generation\<close>

definition lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  lang_pow_code_def [code_abbrev]: "lang_pow = compow"

lemma [code]:
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
  "lang_pow 0 A = {[]}"
  by (simp_all add: lang_pow_code_def)


definition star :: "'a lang \<Rightarrow> 'a lang" where
"star A = (\<Union>n. A ^^ n)"


definition range1 :: "'a lang \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a lang " where
"range1 A m n= (if m \<le> n then (\<Union>i\<in>{m..n}. A ^^ i) else {})"

(*hide_const (open) lang_pow*)


lemma " [] \<in> range1 {[]} 1 1"
  apply (simp add:range1_def)
  apply(simp add:conc_def)
  done


subsection\<open>@{term "(@@)"}\<close>

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A @@ B"
by (auto simp add: conc_def)

lemma concE[elim]: 
assumes "w \<in> A @@ B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
using assms by (auto simp: conc_def)

lemma conc_mono: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A @@ B \<subseteq> C @@ D"
by (auto simp: conc_def) 

lemma conc_empty[simp]: shows "{} @@ A = {}" and "A @@ {} = {}"
by auto

lemma conc_epsilon[simp]: shows "{[]} @@ A = A" and "A @@ {[]} = A"
by (simp_all add:conc_def)

lemma conc_assoc: "(A @@ B) @@ C = A @@ (B @@ C)"
by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)

lemma conc_Un_distrib:
shows "A @@ (B \<union> C) = A @@ B \<union> A @@ C"
and   "(A \<union> B) @@ C = A @@ C \<union> B @@ C"
by auto


lemma conc_UNION_distrib:
shows "A @@ \<Union>(M ` I) = \<Union>((%i. A @@ M i) ` I)"
and   "\<Union>(M ` I) @@ A = \<Union>((%i. M i @@ A) ` I)"
by auto

lemma conc_subset_lists: "A \<subseteq> lists S \<Longrightarrow> B \<subseteq> lists S \<Longrightarrow> A @@ B \<subseteq> lists S"
by(fastforce simp: conc_def in_lists_conv_set)

lemma Nil_in_conc[simp]: "[] \<in> A @@ B \<longleftrightarrow> [] \<in> A \<and> [] \<in> B"
by (metis append_is_Nil_conv concE concI)

lemma concI_if_Nil1: "[] \<in> A \<Longrightarrow> xs : B \<Longrightarrow> xs \<in> A @@ B"
by (metis append_Nil concI)

lemma conc_Diff_if_Nil1: "[] \<in> A \<Longrightarrow> A @@ B = (A - {[]}) @@ B \<union> B"
by (fastforce elim: concI_if_Nil1)

lemma concI_if_Nil2: "[] \<in> B \<Longrightarrow> xs : A \<Longrightarrow> xs \<in> A @@ B"
by (metis append_Nil2 concI)

lemma conc_Diff_if_Nil2: "[] \<in> B \<Longrightarrow> A @@ B = A @@ (B - {[]}) \<union> A"
by (fastforce elim: concI_if_Nil2)

lemma singleton_in_conc:
  "[x] : A @@ B \<longleftrightarrow> [x] : A \<and> [] : B \<or> [] : A \<and> [x] : B"
by (fastforce simp: Cons_eq_append_conv append_eq_Cons_conv
       conc_Diff_if_Nil1 conc_Diff_if_Nil2)


subsection\<open>@{term "A ^^ n"}\<close>

lemma lang_pow_add: "A ^^ (n + m) = A ^^ n @@ A ^^ m"
by (induct n) (auto simp: conc_assoc)

lemma lang_pow_empty: "{} ^^ n = (if n = 0 then {[]} else {})"
by (induct n) auto

lemma lang_pow_empty_Suc[simp]: "({}::'a lang) ^^ Suc n = {}"
by (simp add: lang_pow_empty)

lemma conc_pow_comm:
  shows "A @@ (A ^^ n) = (A ^^ n) @@ A"
by (induct n) (simp_all add: conc_assoc[symmetric])

lemma length_lang_pow_ub:
  "\<forall>w \<in> A. length w \<le> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<le> k*n"
by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma length_lang_pow_lb:
  "\<forall>w \<in> A. length w \<ge> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<ge> k*n"
by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma lang_pow_subset_lists: "A \<subseteq> lists S \<Longrightarrow> A ^^ n \<subseteq> lists S"
  by(induct n)(auto simp: conc_subset_lists)
  
lemma empty_pow_add:
  assumes "[] \<in> A" "s \<in> A ^^ n"
  shows "s \<in> A ^^ (n + m)"
  using assms
  apply(induct m arbitrary: n)
  apply(auto simp add: concI_if_Nil1)
  done

lemma "[] \<in> {}"
  apply auto
  sorry

lemma t1:"(\<forall>xs\<in>A. xs = []) \<Longrightarrow> (A = {[]} \<or> A = {})"
  apply auto 
  done 
 
lemma " w \<in> A ^^ x \<Longrightarrow> m \<le> x \<Longrightarrow> x \<le> n \<Longrightarrow> \<exists>ws. set ws \<subseteq> A \<and> w = concat ws \<and> length ws \<le> n \<and> m \<le> length ws"
  apply(induct ) 

subsection\<open>@{const star}\<close>

lemma star_subset_lists: "A \<subseteq> lists S \<Longrightarrow> star A \<subseteq> lists S"
unfolding star_def by(blast dest: lang_pow_subset_lists)

lemma star_if_lang_pow[simp]: "w : A ^^ n \<Longrightarrow> w : star A"
by (auto simp: star_def)

lemma Nil_in_star[iff]: "[] : star A"
proof (rule star_if_lang_pow)
  show "[] : A ^^ 0" by simp
qed

lemma star_if_lang[simp]: assumes "w : A" shows "w : star A"
proof (rule star_if_lang_pow)
  show "w : A ^^ 1" using \<open>w : A\<close> by simp
qed



lemma append_in_starI[simp]:
assumes "u : star A" and "v : star A" shows "u@v : star A"
proof -
  from \<open>u : star A\<close> obtain m where "u : A ^^ m" by (auto simp: star_def)
  moreover
  from \<open>v : star A\<close> obtain n where "v : A ^^ n" by (auto simp: star_def)
  ultimately have "u@v : A ^^ (m+n)" by (simp add: lang_pow_add)
  thus ?thesis by simp
qed

lemma conc_star_star: "star A @@ star A = star A"
by (auto simp: conc_def)

lemma conc_star_comm:
  shows "A @@ star A = star A @@ A"
unfolding star_def conc_pow_comm conc_UNION_distrib
by simp

lemma star_induct[consumes 1, case_names Nil append, induct set: star]:
assumes "w : star A"
  and "P []"
  and step: "!!u v. u : A \<Longrightarrow> v : star A \<Longrightarrow> P v \<Longrightarrow> P (u@v)"
shows "P w"
proof -
  { fix n have "w : A ^^ n \<Longrightarrow> P w"
    by (induct n arbitrary: w) (auto intro: \<open>P []\<close> step star_if_lang_pow) }
  with \<open>w : star A\<close> show "P w" by (auto simp: star_def)
qed

lemma star_empty[simp]: "star {} = {[]}"
by (auto elim: star_induct)

lemma star_epsilon[simp]: "star {[]} = {[]}"
by (auto elim: star_induct)

lemma star_idemp[simp]: "star (star A) = star A"
by (auto elim: star_induct)

lemma star_unfold_left: "star A = A @@ star A \<union> {[]}" (is "?L = ?R") 
proof
  show "?L \<subseteq> ?R" by (rule, erule star_induct) auto
qed auto

lemma concat_in_star: "set ws \<subseteq> A \<Longrightarrow> concat ws : star A"
by (induct ws) simp_all

lemma zero_range1_empty:"[] \<in> range1 A 0 n"
  apply(simp add:range1_def)
  apply(induct n)
   apply simp
  apply auto
  done

lemma element_range1:"b :range1 A m n = (\<exists>i. i \<ge> m \<and> i \<le> n \<and> b : A ^^ i)"
  apply(simp add:range1_def)
  using atLeastAtMost_iff by blast

lemma concat_Suc_contains:"concat ws \<in> range1 A m n \<Longrightarrow> concat ws \<in> range1 A m (Suc n)"
  apply(induct ws)
  apply simp 
   apply (meson element_range1 le_Suc_eq)
  apply simp
  by (meson element_range1 le_Suc_eq)

lemma concat_n_times:"set ws \<subseteq> A \<Longrightarrow> concat ws \<in> A ^^ length ws"
  apply(induct ws)
   apply simp
  by simp

lemma concat_in_range1: "set ws \<subseteq> A \<and> length ws \<ge> m \<and> length ws \<le> n \<Longrightarrow> concat ws : range1 A m n"
  apply(induct n)
  subgoal 
   apply simp
    using zero_range1_empty by fastforce
  apply(case_tac "length ws \<le> n")
  subgoal for n apply simp
    by(simp add:concat_Suc_contains)
  subgoal for n 
    apply simp apply(case_tac "length ws = (Suc n)")
     prefer 2
    subgoal
      by simp
    subgoal apply simp 
      by (metis dual_order.refl element_range1 concat_n_times)
  done
  done

lemma non_range1[simp]:"range1 A 0 0 = {[]}" 
  apply(simp add:range1_def)
  done

lemma conc_range1[simp]:"range1 A 0 (Suc n) =  (range1 A 0 n) \<union> A ^^ (Suc n)"
  apply (simp add:range1_def)
  by (simp add: atLeast0_atMost_Suc inf_sup_aci(5))


 

lemma "w \<in> range1 A m n \<Longrightarrow> \<exists>ws. set ws \<subseteq> A \<and> w = concat ws \<and> length ws \<le> n \<and> m \<le> length ws "
  apply(simp add:range1_def) apply(case_tac "m\<le>n")apply simp prefer 2 apply auto subgoal for x apply (induct n) apply simp 
    apply auto  
  
lemma in_range_iff_concat:"w : range1 A m n = (\<exists>ws. set ws \<subseteq> A \<and> w = concat ws \<and> length ws \<le> n \<and> length ws \<ge> m)"
  (is "_ = (\<exists>ws. ?R w ws)")
proof
  assume "w : range1 A m n" thus "\<exists>ws. ?R w ws"
nitpick
  proof (induct n arbitrary:m)
    case 0
    then show ?case apply simp  
      by (simp add: element_range1)
  next
    case (Suc n)
    then show ?case  
      sorry
  qed
next 
  assume "\<exists>us. ?R w us" thus "w : range1 A m n"
    apply auto
    by(simp add:concat_in_range1)
qed

 

lemma in_star_iff_concat:
  "w \<in> star A = (\<exists>ws. set ws \<subseteq> A \<and> w = concat ws)"
  (is "_ = (\<exists>ws. ?R w ws)")
proof
  assume "w : star A" thus "\<exists>ws. ?R w ws"
  proof induct
    case Nil have "?R [] []" by simp
    thus ?case ..
  next
    case (append u v)
    then obtain ws where "set ws \<subseteq> A \<and> v = concat ws" by blast
    with append have "?R (u@v) (u#ws)" by auto
    thus ?case ..
  qed
next
  assume "\<exists>us. ?R w us" thus "w : star A"
  by (auto simp: concat_in_star)
qed

 




lemma star_conv_concat: "star A = {concat ws|ws. set ws \<subseteq> A}"
by (fastforce simp: in_star_iff_concat)

lemma star_insert_eps[simp]: "star (insert [] A) = star(A)"
proof-
  { fix us
    have "set us \<subseteq> insert [] A \<Longrightarrow> \<exists>vs. concat us = concat vs \<and> set vs \<subseteq> A"
      (is "?P \<Longrightarrow> \<exists>vs. ?Q vs")
    proof
      let ?vs = "filter (%u. u \<noteq> []) us"
      show "?P \<Longrightarrow> ?Q ?vs" by (induct us) auto
    qed
  } thus ?thesis by (auto simp: star_conv_concat)
qed

lemma star_unfold_left_Nil: "star A = (A - {[]}) @@ (star A) \<union> {[]}"
by (metis insert_Diff_single star_insert_eps star_unfold_left)

lemma star_Diff_Nil_fold: "(A - {[]}) @@ star A = star A - {[]}"
proof -
  have "[] \<notin> (A - {[]}) @@ star A" by simp
  thus ?thesis using star_unfold_left_Nil by blast
qed


lemma star_decom: 
  assumes a: "x \<in> star A" "x \<noteq> []"
  shows "\<exists>a b. x = a @ b \<and> a \<noteq> [] \<and> a \<in> A \<and> b \<in> star A"
using a by (induct rule: star_induct) (blast)+

lemma star_pow:
  assumes "s \<in> star A"
  shows "\<exists>n. s \<in> A ^^ n"
using assms
apply(induct)
apply(rule_tac x="0" in exI)
apply(auto)
apply(rule_tac x="Suc n" in exI)
apply(auto)
  done
end
