theory Walks
imports "HOL-Probability.Probability" "HOL-Library.Permutation"
begin

sledgehammer_params[debug=true,timeout=600]

locale walk_list = 
  fixes step :: "int list" and len::nat
  assumes "length step = len"
begin

primrec walk :: "nat \<Rightarrow> int" where
  "walk 0 = 0"
| "walk (Suc n) = walk n + step!n"


lemma  walk_as_sum:
  "walk (n+1) = (\<Sum> j \<in> {0..n}. step!j)"
by(induct n,auto)

abbreviation range :: "nat \<Rightarrow> nat" where
  "range n \<equiv> length (remdups (map (\<lambda>i. walk (nat i)) [0..(int)n]))"

lemma map_snoc:
  "map f (xs@[x]) = map f xs @ [f x]"
by(induct xs,auto)

lemma walk_member:
  assumes "m \<le> n"
  shows "walk m \<in> set (map (\<lambda>i. walk (nat i)) [0..(int)(n)])" 
  using assms proof(induct n arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc n')
  have *:"(map (\<lambda>i. walk (nat i)) [0..(int)(Suc n')]) = (map (\<lambda>i. walk (nat i)) [0..(int)(n')]) @ [walk (Suc n')]"
    using map_snoc  by (smt nat_int of_nat_0_le_iff of_nat_Suc upto_rec2)
  show ?case proof(cases "m = Suc n'")
    case True
    then show ?thesis using Suc * by auto
  next
    case False
    then show ?thesis using Suc * by auto
  qed
qed

lemma remdups_snoc:
  assumes "x \<in> set xs"
  shows "length (remdups (xs@[x])) = length (remdups xs)"
  using assms length_remdups_card_conv[of "xs@[x]"] 
  by (metis length_remdups_card_conv remdups.simps(2) rotate1.simps(2) set_rotate1)

lemma 
  assumes "range (n+1) = range n + 1" 
  shows "\<forall>m \<le> n. walk (n+1) \<noteq> walk m"
proof(rule+)
  fix m
  assume *:"m \<le> n" and "walk (n + 1) = walk m"
  hence **: "walk (n+1) \<in> set (map (\<lambda>i. walk (nat i)) [0..(int)(n)])" using walk_member by simp
  moreover have "map (\<lambda>i. walk (nat i)) [0..(int)(n+1)] = (map (\<lambda>i. walk (nat i)) [0..(int)(n)]) @ [walk (n+1)]"
       using map_snoc  nat_int of_nat_0_le_iff of_nat_Suc upto_rec2 
       by (smt of_nat_1 of_nat_add)
  ultimately have "length (remdups  (map (\<lambda>i. walk (nat i)) [0..(int)(n+1)])) = length (remdups  (map (\<lambda>i. walk (nat i)) [0..(int)(n)]))" 
    using ** * remdups_snoc[OF **] by simp
  thus False using assms by simp
qed

lemma 
  assumes "m \<le> n" and "walk (n+1) \<noteq> walk m"
  shows "(\<Sum> j \<in> {m..n}. step!j) \<noteq> 0"
using assms proof(cases "m=0")
  case True
  then show ?thesis using walk_as_sum assms by auto
next
  case False
  then obtain m' where *:"m=Suc m'"  using not0_implies_Suc by auto
  then have "(\<Sum> j \<in> {0..n}. step!j) - (\<Sum> j \<in> {0..m'}. step!j) =  (\<Sum> j \<in> {m..n}. step!j)"
    using False 
    by (smt add_leD2 assms(1) le_add1 le_add_same_cancel1 plus_1_eq_Suc sum.atLeastLessThan_concat sum.atLeast_Suc_atMost sum.last_plus)
  then show ?thesis using walk_as_sum[of m'] walk_as_sum[of n] assms * by simp
qed

end


locale walk = 
fixes step :: "nat \<Rightarrow> int"
begin

primrec walk :: "nat \<Rightarrow> int" where
  "walk 0 = 0"
| "walk (Suc n) = walk n + step n"


lemma  walk_as_sum:
  "walk (n+1) = (\<Sum> j \<in> {0..n}. step j)"
by(induct n,auto)

abbreviation range :: "nat \<Rightarrow> nat" where
  "range n \<equiv> length (remdups (map (\<lambda>i. walk (nat i)) [0..(int)n]))"

lemma map_snoc:
  "map f (xs@[x]) = map f xs @ [f x]"
by(induct xs,auto)

lemma walk_member:
  assumes "m \<le> n"
  shows "walk m \<in> set (map (\<lambda>i. walk (nat i)) [0..(int)(n)])" 
  using assms proof(induct n arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc n')
  have *:"(map (\<lambda>i. walk (nat i)) [0..(int)(Suc n')]) = (map (\<lambda>i. walk (nat i)) [0..(int)(n')]) @ [walk (Suc n')]"
    using map_snoc  by (smt nat_int of_nat_0_le_iff of_nat_Suc upto_rec2)
  show ?case proof(cases "m = Suc n'")
    case True
    then show ?thesis using Suc * by auto
  next
    case False
    then show ?thesis using Suc * by auto
  qed
qed

lemma remdups_snoc:
  assumes "x \<in> set xs"
  shows "length (remdups (xs@[x])) = length (remdups xs)"
  using assms length_remdups_card_conv[of "xs@[x]"] 
  by (metis length_remdups_card_conv remdups.simps(2) rotate1.simps(2) set_rotate1)

lemma 
  assumes "range (n+1) = range n + 1" 
  shows "\<forall>m \<le> n. walk (n+1) \<noteq> walk m"
proof(rule+)
  fix m
  assume *:"m \<le> n" and "walk (n + 1) = walk m"
  hence **: "walk (n+1) \<in> set (map (\<lambda>i. walk (nat i)) [0..(int)(n)])" using walk_member by simp
  moreover have "map (\<lambda>i. walk (nat i)) [0..(int)(n+1)] = (map (\<lambda>i. walk (nat i)) [0..(int)(n)]) @ [walk (n+1)]"
       using map_snoc  nat_int of_nat_0_le_iff of_nat_Suc upto_rec2 
       by (smt of_nat_1 of_nat_add)
  ultimately have "length (remdups  (map (\<lambda>i. walk (nat i)) [0..(int)(n+1)])) = length (remdups  (map (\<lambda>i. walk (nat i)) [0..(int)(n)]))" 
    using ** * remdups_snoc[OF **] by simp
  thus False using assms by simp
qed

lemma 
  assumes "m \<le> n" and "walk (n+1) \<noteq> walk m"
  shows "(\<Sum> j \<in> {m..n}. step j) \<noteq> 0"
using assms proof(cases "m=0")
  case True
  then show ?thesis using walk_as_sum assms by auto
next
  case False
  then obtain m' where *:"m=Suc m'"  using not0_implies_Suc by auto
  then have "(sum step {0..n}) - (sum step {0..m'}) =  (\<Sum> j \<in> {m..n}. step j)"
    using False 
    by (smt add_leD2 assms(1) le_add1 le_add_same_cancel1 plus_1_eq_Suc sum.atLeastLessThan_concat sum.atLeast_Suc_atMost sum.last_plus)
  then show ?thesis using walk_as_sum[of m'] walk_as_sum[of n] assms * by simp
qed

end

locale walk_pmf =
  fixes step_pmf :: "nat \<Rightarrow> int pmf"
begin

abbreviation walk_pmf :: "nat \<Rightarrow> int pmf" where
   "walk_pmf n = 


(*
primrec  steps1 :: "nat \<Rightarrow> int" where
 "steps1 0 = 0"
| "steps1 (Suc n) = (int)n"

value "steps1 0"

global_interpretation steps1: walk  "steps1 :: nat \<Rightarrow> int" 
  defines steps1_walk = steps1.walk and steps1_range = steps1.range
  apply unfold_locales 
  using steps1.simps by auto


value  "(steps1.range 0, map steps1.walk [0,1,2,3,4])"
*)
